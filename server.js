// Talentos — servidor endurecido, sem dependências (Node 18+).
'use strict';
const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto');
const PROD=process.env.NODE_ENV==='production',PORT=+process.env.PORT||3000,FILE=process.env.DB_FILE||path.join(__dirname,'data.db'),
CODE=process.env.RECRUITER_CODE||'',TRUST=process.env.TRUST_PROXY==='1',HOSTS=(process.env.ALLOWED_HOSTS||'').split(',').map(s=>s.trim()).filter(Boolean);
const MAIL_KEY=process.env.RESEND_API_KEY||'',FROM=process.env.MAIL_FROM||'',BASE=(process.env.BASE_URL||`http://localhost:${PORT}`).replace(/\/$/,'');
const PLATFORM_TOKEN=process.env.PLATFORM_TOKEN||'',LEADS_EMAIL=process.env.LEADS_EMAIL||'';
const PLANS={fundador:{name:'Cliente Fundador',price:199,jobs:15,users:8,pool:true,promo:'10 primeiros clientes'},essencial:{name:'Essencial',price:199,jobs:3,users:2,pool:false},profissional:{name:'Profissional',price:399,jobs:15,users:8,pool:true},empresarial:{name:'Empresarial',price:799,jobs:60,users:30,pool:true}};
const CROLES=['admin','rh','recrutador','gestor'],CAN={jobs:['admin','rh'],move:['admin','rh','recrutador'],team:['admin']};
const REQ2=process.env.REQUIRE_2FA==='1'||(PROD&&process.env.REQUIRE_2FA!=='0');
let KEY=null;
if(process.env.DATA_KEY){KEY=Buffer.from(process.env.DATA_KEY,'hex');if(KEY.length!==32){console.error('DATA_KEY deve ter 64 caracteres hex. Gere com: node -e "console.log(require(\'crypto\').randomBytes(32).toString(\'hex\'))"');process.exit(1)}}
if(PROD&&(!KEY||CODE.length<12||!/^https:\/\//.test(process.env.BASE_URL||''))){console.error('Em produção defina DATA_KEY (64 hex), RECRUITER_CODE (mín. 12 caracteres) e BASE_URL (https://seudominio).');process.exit(1)}
if(!MAIL_KEY||!FROM)console.warn('AVISO: e-mail não configurado (RESEND_API_KEY e MAIL_FROM). Em desenvolvimento os links de recuperação aparecem aqui no terminal; em produção NÃO são enviados.');
if(!KEY)console.warn('AVISO: sem DATA_KEY o banco NÃO é criptografado em disco.');
/* ---------- armazenamento (AES-256-GCM em repouso) ---------- */
const enc=s=>{const iv=crypto.randomBytes(12),c=crypto.createCipheriv('aes-256-gcm',KEY,iv),ct=Buffer.concat([c.update(s,'utf8'),c.final()]);return Buffer.concat([Buffer.from('TLN1'),iv,c.getAuthTag(),ct])};
const dec=b=>{const d=crypto.createDecipheriv('aes-256-gcm',KEY,b.subarray(4,16));d.setAuthTag(b.subarray(16,32));return Buffer.concat([d.update(b.subarray(32)),d.final()]).toString('utf8')};
let DB={users:[],jobs:[],apps:[],sessions:{},companies:[],leads:[]};
try{const b=fs.readFileSync(FILE);DB={...DB,...JSON.parse(b.subarray(0,4).toString()==='TLN1'?dec(b):b.toString('utf8'))}}
catch(e){if(e.code!=='ENOENT'){console.error('Falha ao ler o banco (chave errada ou arquivo corrompido). Abortando para não sobrescrever dados.');process.exit(1)}}
{const orph=DB.users.filter(u=>u.role==='rec'&&!u.companyId);
if(orph.length||DB.jobs.some(j=>!j.companyId)){const c={id:crypto.randomUUID(),name:'Minha empresa',plan:'essencial',created:Date.now()};DB.companies.push(c);
orph.forEach((u,i)=>{u.companyId=c.id;u.crole=i?'recrutador':'admin'});DB.jobs.forEach(j=>{if(!j.companyId)j.companyId=c.id;j.status=j.status||'open'})}}
function flush(){const s=JSON.stringify(DB);fs.writeFileSync(FILE+'.tmp',KEY?enc(s):s,{mode:0o600});fs.renameSync(FILE+'.tmp',FILE)}
let tm;const save=()=>{clearTimeout(tm);tm=setTimeout(flush,50)};
for(const s of['SIGINT','SIGTERM'])process.on(s,()=>{try{flush()}catch{}process.exit(0)});
/* ---------- utilidades ---------- */
const E=(c,m)=>({c,m}),CTRL=/[\u0000-\u0008\u000B\u000C\u000E-\u001F\u007F]/g;
const str=(v,n=200)=>String(v??'').replace(CTRL,'').trim().slice(0,n);
const list=(v,n=30,l=60)=>(Array.isArray(v)?v:[]).slice(0,n).map(x=>str(x,l)).filter(Boolean);
const EDU=['Ensino médio','Técnico','Graduação','Pós-graduação','Mestrado/Doutorado'],ENG=['Nenhum','Básico','Intermediário','Avançado','Fluente'],
QT=['text','long','choice','yesno','number','date','url'],MODE=['Presencial','Híbrido','Remoto'],ST=['Recebida','Triagem','Entrevista','Aprovado','Recusado'],
AV=['Imediata','15 dias','30 dias','Mais de 30 dias'];
const pick=(v,a)=>a.includes(v)?v:a[0],uf=v=>/^[A-Za-z]{2}$/.test(v)?v.toUpperCase():'',UUID=/^[0-9a-f-]{36}$/;
const cleanP=p=>({mode:pick(p.mode,['Qualquer',...MODE]),uf:uf(str(p.uf,2)),city:str(p.city,80),phone:str(p.phone,20).replace(/[^\d()+\-\s]/g,''),link:/^https?:\/\//i.test(str(p.link,200))?str(p.link,200):'',summary:str(p.summary,1000),edu:pick(p.edu,EDU),eng:pick(p.eng,ENG),avail:pick(p.avail,AV),
salary:str(p.salary,10).replace(/\D/g,''),open:p.open===true,skills:list(p.skills),certs:list(p.certs),
exps:(Array.isArray(p.exps)?p.exps:[]).slice(0,15).map(e=>({role:str(e?.role,80),co:str(e?.co,80),years:Math.min(Math.max(+e?.years||0,0),50)}))});
const cleanJ=j=>({title:str(j.title,120),area:str(j.area,60),desc:str(j.desc,2000),skills:list(j.skills,20),minYears:Math.min(Math.max(+j.minYears||0,0),40),minEdu:pick(j.minEdu,EDU),uf:uf(str(j.uf,2)),city:str(j.city,80),mode:pick(j.mode,MODE),
qs:(Array.isArray(j.qs)?j.qs:[]).slice(0,15).map(q=>({label:str(q?.label,200),type:pick(q?.type,QT),opts:list(q?.opts,10)})).filter(q=>q.label)});
const pub=u=>({id:u.id,name:u.name,email:u.email,role:u.role,p:u.p});
const coOf=u=>DB.companies.find(c=>c.id===u.companyId);
const usage=c=>({jobsOpen:DB.jobs.filter(j=>j.companyId===c.id&&j.status==='open').length,usersN:DB.users.filter(u=>u.companyId===c.id).length});
const self=u=>{const o={...pub(u),t2:!!u.t2,req2:REQ2&&u.role==='rec'};if(u.role==='rec'){const c=coOf(u);o.crole=u.crole;o.company={name:c.name,plan:c.plan,limits:PLANS[c.plan],...usage(c)}}return o};
const perm=(me,k)=>{need(me,'rec');need2(me);if(!CAN[k].includes(me.crole))throw E(403,'Seu papel na empresa não permite esta ação.')};
const need2=me=>{if(REQ2&&me.role==='rec'&&!me.t2)throw E(403,'Ative a verificação em duas etapas na aba Segurança para acessar dados de candidatos.')};
const need=(me,r)=>{if(!me)throw E(401,'Faça login.');if(r&&me.role!==r)throw E(403,'Sem permissão.')};
const sha=s=>crypto.createHash('sha256').update(String(s)).digest();
const safeEq=(a,b)=>crypto.timingSafeEqual(sha(a),sha(b));
const log=(ev,ip,x={})=>fs.appendFile(path.join(__dirname,'audit.log'),JSON.stringify({t:new Date().toISOString(),ev,ip,...x})+'\n',{mode:0o600},()=>{});
/* ---------- e-mail (API HTTP do Resend; sem dependências) ---------- */
async function mail(to,subject,text){
if(!MAIL_KEY||!FROM){if(!PROD)console.log('[dev] e-mail para',to,'\n'+text);return}
try{const r=await fetch('https://api.resend.com/emails',{method:'POST',headers:{Authorization:'Bearer '+MAIL_KEY,'Content-Type':'application/json'},body:JSON.stringify({from:FROM,to:[to],subject,text})});if(!r.ok)console.error('Falha ao enviar e-mail:',r.status)}catch{console.error('Falha ao enviar e-mail')}}
/* ---------- 2FA (TOTP, RFC 6238) ---------- */
const B32='ABCDEFGHIJKLMNOPQRSTUVWXYZ234567';
const b32=buf=>{let bits=0,v=0,o='';for(const x of buf){v=(v<<8)|x;bits+=8;while(bits>=5){o+=B32[(v>>>(bits-5))&31];bits-=5}}if(bits>0)o+=B32[(v<<(5-bits))&31];return o};
const unb32=s=>{let bits=0,v=0;const o=[];for(const ch of s){const i=B32.indexOf(ch);if(i<0)continue;v=(v<<5)|i;bits+=5;if(bits>=8){o.push((v>>>(bits-8))&255);bits-=8}}return Buffer.from(o)};
const hotp=(key,ctr)=>{const b=Buffer.alloc(8);b.writeBigUInt64BE(BigInt(ctr));const h=crypto.createHmac('sha1',key).update(b).digest(),o=h[19]&15;return String((h.readUInt32BE(o)&0x7fffffff)%1e6).padStart(6,'0')};
function totpOk(u,code,secret){code=String(code||'').replace(/\s/g,'');if(!/^\d{6}$/.test(code))return false;const key=unb32(secret),st=Math.floor(Date.now()/3e4);
for(let d=-1;d<=1;d++){const c=st+d;if(safeEq(hotp(key,c),code)&&c>(u.tl||0)){u.tl=c;return true}}return false}
function check2fa(u,code){if(totpOk(u,code,u.t2))return true;const i=(u.rc||[]).indexOf(th(String(code||'').trim().toLowerCase()));if(i>=0){u.rc.splice(i,1);return true}return false}
/* ---------- senhas (scrypt assíncrono) ---------- */
const scrypt=(pw,salt)=>new Promise((r,j)=>crypto.scrypt(pw.normalize('NFKC'),salt,64,{N:32768,r:8,p:1,maxmem:64<<20},(e,k)=>e?j(e):r(k)));
const hs=async pw=>{const s=crypto.randomBytes(16);return s.toString('hex')+':'+(await scrypt(pw,s)).toString('hex')};
const ok=async(pw,st)=>{const[s,h]=st.split(':');return crypto.timingSafeEqual(await scrypt(pw,Buffer.from(s,'hex')),Buffer.from(h,'hex'))};
let DUMMY;hs('dummy-password').then(x=>DUMMY=x);
const WEAK=new Set(['1234567890','password123','senha12345','qwertyuiop','1q2w3e4r5t','0123456789','abcdefghij','senhasenha1','password1234','12345678910']);
const strong=(pw,email)=>pw.length>=10&&pw.length<=128&&!WEAK.has(pw.toLowerCase())&&pw.toLowerCase()!==email&&new Set(pw).size>=5&&/\d/.test(pw)&&/\p{L}/u.test(pw);
/* ---------- limites de taxa ---------- */
const hits=new Map();
const cnt=(k,win)=>{const n=Date.now(),a=(hits.get(k)||[]).filter(t=>n-t<win);hits.set(k,a);return a};
const hit=(k,win)=>cnt(k,win).push(Date.now());
const limit=(k,max,win)=>{if(cnt(k,win).length>=max)throw E(429,'Muitas tentativas. Aguarde alguns minutos.');hit(k,win)};
setInterval(()=>{const n=Date.now();for(const[k,a]of hits)if(!a.length||n-a[a.length-1]>36e5)hits.delete(k)},6e4).unref();
/* ---------- sessões (token só em cookie HttpOnly; no banco fica apenas o hash) ---------- */
const CN=PROD?'__Host-sid':'sid',ABS=7*864e5,IDLE=8*36e5,th=t=>sha(t).toString('hex');
const ck=h=>{const o={};(h||'').split(';').forEach(p=>{const i=p.indexOf('=');if(i>0)o[p.slice(0,i).trim()]=p.slice(i+1).trim()});return o};
const cookie=(res,v,age)=>res.setHeader('Set-Cookie',`${CN}=${v}; HttpOnly; SameSite=Strict; Path=/; Max-Age=${age}${PROD?'; Secure':''}`);
function session(u,res){const now=Date.now(),t=crypto.randomBytes(32).toString('base64url');
for(const k in DB.sessions){const s=DB.sessions[k];if(s.exp<now||s.idle<now)delete DB.sessions[k]}
DB.sessions[th(t)]={uid:u.id,exp:now+ABS,idle:now+IDLE};save();cookie(res,t,ABS/1000);return{user:self(u)}}
/* ---------- rotas ---------- */
async function route(m,p,b,c){const{me,ip,res}=c,k=m+' '+p;
if(k==='POST /api/register'){limit('a:'+ip,10,9e5);const role=b.role==='rec'?'rec':'cand',email=str(b.email,120).toLowerCase(),name=str(b.name,80),pw=String(b.password||'');
if(!name||!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email))throw E(400,'Informe nome e e-mail válido.');
if(!strong(pw,email))throw E(400,'Senha: 10+ caracteres, com letras e números, e não pode ser óbvia.');
if(role==='rec'&&(!CODE||!safeEq(b.code||'',CODE))){log('recruiter_code_fail',ip);throw E(403,'Código de convite inválido.')}
const ph=await hs(pw);
if(DB.users.some(u=>u.email===email))throw E(400,'Não foi possível concluir o cadastro. Se você já tem conta, faça login.');
const u={id:crypto.randomUUID(),role,name,email,ph};if(role==='cand')u.p=cleanP({});else{const cn=str(b.company,80);if(cn.length<2)throw E(400,'Informe o nome da empresa.');
const c={id:crypto.randomUUID(),name:cn,plan:'essencial',created:Date.now()};DB.companies.push(c);u.companyId=c.id;u.crole='admin'}
DB.users.push(u);log('register',ip,{uid:u.id,role});return session(u,res)}
if(k==='POST /api/login'){limit('a:'+ip,10,9e5);const email=str(b.email,120).toLowerCase();
if(cnt('f:'+email,9e5).length>=8)throw E(429,'Muitas tentativas. Aguarde alguns minutos.');
const u=DB.users.find(x=>x.email===email),good=await ok(String(b.password||''),u?u.ph:DUMMY||await hs('x'));
if(!u||!good){hit('f:'+email,9e5);log('login_fail',ip);throw E(401,'E-mail ou senha incorretos.')}
if(u.t2){if(!b.code)return{need2fa:true};if(!check2fa(u,b.code)){hit('f:'+email,9e5);log('2fa_fail',ip,{uid:u.id});throw E(401,'Código inválido.')}save()}
hits.delete('f:'+email);log('login_ok',ip,{uid:u.id});return session(u,res)}
if(k==='POST /api/logout'){if(c.tk)delete DB.sessions[c.tk];save();cookie(res,'',0);return{ok:true}}
if(k==='GET /api/me'){need(me);return self(me)}
if(k==='PUT /api/profile'){need(me,'cand');me.p=cleanP(b);save();return self(me)}
if(k==='GET /api/jobs'){need(me);const cn=id=>DB.companies.find(c=>c.id===id)?.name||'';
return DB.jobs.filter(j=>me.role==='rec'?j.companyId===me.companyId:j.status==='open').map(({by,...j})=>({...j,company:cn(j.companyId)}))}
if(k==='POST /api/jobs'){perm(me,'jobs');limit('j:'+me.id,30,36e5);const c=coOf(me),L=PLANS[c.plan];
if(usage(c).jobsOpen>=L.jobs)throw E(402,`Limite do plano ${L.name} atingido (${L.jobs} vagas abertas). Encerre uma vaga ou faça upgrade.`);
const j={...cleanJ(b),id:crypto.randomUUID(),companyId:me.companyId,status:'open',by:me.id,created:Date.now()};
if(!j.title||!j.skills.length)throw E(400,'Informe título e ao menos uma habilidade.');DB.jobs.push(j);save();return{...j,company:c.name}}
if(k==='POST /api/apply'){need(me,'cand');limit('p:'+me.id,60,36e5);const j=DB.jobs.find(x=>x.id===b.jobId&&x.status==='open');if(!j)throw E(404,'Vaga não encontrada ou encerrada.');
if(DB.apps.some(a=>a.jobId===j.id&&a.candId===me.id))throw E(409,'Você já se candidatou a esta vaga.');
const an=Array.isArray(b.answers)?b.answers:[];if(an.length!==j.qs.length||an.some(x=>!str(x)))throw E(400,'Responda todas as perguntas.');
const a={id:crypto.randomUUID(),jobId:j.id,candId:me.id,ans:j.qs.map((q,i)=>({q:q.label,a:str(an[i],1000)})),status:'Recebida',date:new Date().toLocaleDateString('pt-BR'),hist:[{t:Date.now(),by:'Candidato',from:'',to:'Recebida'}]};
DB.apps.push(a);save();return a}
if(k==='GET /api/apps'){need(me);if(me.role==='rec'){need2(me);const ids=new Set(DB.jobs.filter(j=>j.companyId===me.companyId).map(j=>j.id));return DB.apps.filter(a=>ids.has(a.jobId))}
return DB.apps.filter(a=>a.candId===me.id).map(({hist,...a})=>a)}
if(k==='GET /api/candidates'){need(me,'rec');need2(me);const c=coOf(me),jids=new Set(DB.jobs.filter(j=>j.companyId===c.id).map(j=>j.id)),ids=new Set(DB.apps.filter(a=>jids.has(a.jobId)).map(a=>a.candId));
return DB.users.filter(u=>u.role==='cand'&&(ids.has(u.id)||(PLANS[c.plan].pool&&u.p.open))).map(pub)}
if(k==='POST /api/lgpd/request'){need(me);limit('lg:'+me.id,5,36e5);const type=str(b.type,40),detail=str(b.detail,500);
if(!['confirmacao','acesso','correcao','anonimizacao','eliminacao','revogacao'].includes(type))throw E(400,'Tipo de solicitação LGPD inválido.');
log('lgpd_titular_request',ip,{uid:me.id,email:me.email,type,detail});
if(LEADS_EMAIL)mail(LEADS_EMAIL,`Solicitação LGPD (${type}) — Talentos`,`Usuário: ${me.name} (${me.email})
Tipo: ${type}
Detalhes: ${detail}`);
return{ok:true,message:'Solicitação registrada com sucesso. O Encarregado (DPO) responderá em até 15 dias conforme a LGPD.'}}
if(k==='GET /api/export'){need(me);return{conta:pub(me),candidaturas:DB.apps.filter(a=>a.candId===me.id)}}
if(k==='DELETE /api/account'){need(me);limit('a:'+ip,10,9e5);if(!await ok(String(b.password||''),me.ph))throw E(400,'Senha incorreta.');
if(me.role==='rec'){const others=DB.users.filter(u=>u.companyId===me.companyId&&u.id!==me.id);
if(me.crole==='admin'&&others.length&&!others.some(u=>u.crole==='admin'))throw E(400,'Transfira a administração a outra pessoa antes de excluir sua conta.');
if(!others.length){const jids=new Set(DB.jobs.filter(j=>j.companyId===me.companyId).map(j=>j.id));DB.apps=DB.apps.filter(a=>!jids.has(a.jobId));DB.jobs=DB.jobs.filter(j=>j.companyId!==me.companyId);DB.companies=DB.companies.filter(x=>x.id!==me.companyId)}}
DB.users=DB.users.filter(u=>u.id!==me.id);DB.apps=DB.apps.filter(a=>a.candId!==me.id);
for(const t in DB.sessions)if(DB.sessions[t].uid===me.id)delete DB.sessions[t];save();cookie(res,'',0);log('account_delete',ip,{uid:me.id});return{ok:true}}
if(k==='POST /api/2fa/setup'){need(me);if(me.t2)throw E(400,'A verificação em duas etapas já está ativa.');me.t2p=b32(crypto.randomBytes(20));save();
return{secret:me.t2p,uri:`otpauth://totp/Talentos:${encodeURIComponent(me.email)}?secret=${me.t2p}&issuer=Talentos`}}
if(k==='POST /api/2fa/enable'){need(me);limit('t:'+me.id,10,9e5);if(!me.t2p)throw E(400,'Inicie a configuração primeiro.');
if(!totpOk(me,b.code,me.t2p))throw E(400,'Código inválido. Confira o horário do celular e tente de novo.');
me.t2=me.t2p;delete me.t2p;const codes=Array.from({length:8},()=>{const x=crypto.randomBytes(5).toString('hex');return x.slice(0,5)+'-'+x.slice(5)});me.rc=codes.map(x=>th(x));
for(const t in DB.sessions)if(DB.sessions[t].uid===me.id&&t!==c.tk)delete DB.sessions[t];save();log('2fa_on',ip,{uid:me.id});return{codes}}
if(k==='POST /api/2fa/disable'){need(me);limit('t:'+me.id,10,9e5);if(!me.t2)throw E(400,'A verificação em duas etapas não está ativa.');
if(!await ok(String(b.password||''),me.ph)||!check2fa(me,b.code))throw E(400,'Senha ou código incorretos.');
me.t2=null;me.rc=[];save();log('2fa_off',ip,{uid:me.id});return{ok:true}}
if(k==='POST /api/forgot'){limit('a:'+ip,10,9e5);const email=str(b.email,120).toLowerCase(),u=DB.users.find(x=>x.email===email);
if(u&&cnt('fp:'+email,36e5).length<3){hit('fp:'+email,36e5);const t=crypto.randomBytes(32).toString('base64url');u.rs={h:th(t),exp:Date.now()+18e5};save();log('reset_req',ip,{uid:u.id});
mail(u.email,'Talentos — redefinição de senha',`Olá, ${u.name}.\n\nPara criar uma nova senha, abra o link (válido por 30 minutos e de uso único):\n${BASE}/#reset=${t}\n\nSe você não pediu isso, ignore este e-mail: sua senha continua a mesma.`)}
return{ok:true}}
if(k==='POST /api/reset'){limit('a:'+ip,10,9e5);const pw=String(b.password||''),now=Date.now(),h=th(String(b.token||''));
const u=DB.users.find(x=>x.rs&&x.rs.exp>now&&safeEq(x.rs.h,h));
if(!u)throw E(400,'Link inválido ou expirado. Peça um novo.');
if(!strong(pw,u.email))throw E(400,'Senha: 10+ caracteres, com letras e números, e não pode ser óbvia.');
u.ph=await hs(pw);delete u.rs;delete u.inv;for(const t in DB.sessions)if(DB.sessions[t].uid===u.id)delete DB.sessions[t];hits.delete('f:'+u.email);save();log('reset_ok',ip,{uid:u.id});return{ok:true}}
if(k==='GET /api/plans')return PLANS;
if(k==='POST /api/demo'){limit('d:'+ip,5,36e5);const l={id:crypto.randomUUID(),t:Date.now(),name:str(b.name,80),company:str(b.company,80),email:str(b.email,120).toLowerCase(),phone:str(b.phone,20).replace(/[^\d()+\-\s]/g,''),msg:str(b.msg,500)};
if(!l.name||!l.company||!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(l.email))throw E(400,'Informe nome, empresa e e-mail válido.');
DB.leads.push(l);save();log('lead',ip);if(LEADS_EMAIL)mail(LEADS_EMAIL,'Novo pedido de demonstração — Talentos',`${l.name} (${l.company})\n${l.email} ${l.phone}\n${l.msg}`);return{ok:true}}
if(p.startsWith('/api/platform/')){limit('pl:'+ip,20,9e5);if(PLATFORM_TOKEN.length<24||!safeEq(c.pt,PLATFORM_TOKEN)){log('platform_denied',ip);throw E(403,'Acesso negado.')}
if(k==='GET /api/platform/companies')return DB.companies.map(x=>({...x,...usage(x)}));
if(k==='PUT /api/platform/plan'){const x=DB.companies.find(y=>y.id===b.companyId);if(!x||!PLANS[b.plan])throw E(400,'Empresa ou plano inválido.');x.plan=b.plan;save();log('plan_set',ip,{co:x.id,plan:x.plan});return x}
if(k==='GET /api/platform/leads')return DB.leads;
throw E(404,'Rota não encontrada.')}
if(k==='GET /api/team'){perm(me,'team');return DB.users.filter(u=>u.companyId===me.companyId).map(u=>({id:u.id,name:u.name,email:u.email,crole:u.crole,t2:!!u.t2,invited:!!u.inv}))}
if(k==='POST /api/team'){perm(me,'team');limit('tm:'+me.id,20,36e5);const c=coOf(me),email=str(b.email,120).toLowerCase(),name=str(b.name,80),cr=CROLES.includes(b.crole)?b.crole:'recrutador';
if(!name||!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email))throw E(400,'Informe nome e e-mail válido.');
if(usage(c).usersN>=PLANS[c.plan].users)throw E(402,`Limite de usuários do plano ${PLANS[c.plan].name} atingido (${PLANS[c.plan].users}). Faça upgrade.`);
if(DB.users.some(u=>u.email===email))throw E(400,'Este e-mail já está em uso na plataforma.');
const u={id:crypto.randomUUID(),role:'rec',companyId:c.id,crole:cr,name,email,ph:await hs(crypto.randomBytes(24).toString('hex')),inv:true},t=crypto.randomBytes(32).toString('base64url');
u.rs={h:th(t),exp:Date.now()+72*36e5};DB.users.push(u);save();log('team_invite',ip,{uid:me.id,to:u.id});
mail(email,`${c.name} convidou você para o Talentos`,`Olá, ${name}.\n\n${me.name} (${c.name}) criou seu acesso ao Talentos com o papel de ${cr}. Defina sua senha pelo link (válido por 72 horas):\n${BASE}/#reset=${t}`);return{ok:true}}
const tm2=p.match(/^\/api\/team\/([0-9a-f-]{36})$/);
if(tm2&&(m==='PATCH'||m==='DELETE')){perm(me,'team');const u=DB.users.find(x=>x.id===tm2[1]&&x.companyId===me.companyId);if(!u)throw E(404,'Usuário não encontrado.');
const nAdm=DB.users.filter(x=>x.companyId===me.companyId&&x.crole==='admin').length;
if(u.crole==='admin'&&nAdm<2&&(m==='DELETE'||b.crole!=='admin'))throw E(400,'A empresa precisa de ao menos um administrador.');
if(m==='DELETE'){DB.users=DB.users.filter(x=>x!==u);for(const t in DB.sessions)if(DB.sessions[t].uid===u.id)delete DB.sessions[t]}
else{if(!CROLES.includes(b.crole))throw E(400,'Papel inválido.');u.crole=b.crole}
save();log('team_'+m.toLowerCase(),ip,{uid:me.id,target:u.id});return{ok:true}}
const jm=p.match(/^\/api\/jobs\/([0-9a-f-]{36})$/);
if(m==='PATCH'&&jm){perm(me,'jobs');const j=DB.jobs.find(x=>x.id===jm[1]&&x.companyId===me.companyId);if(!j)throw E(404,'Vaga não encontrada.');
if(!['open','closed'].includes(b.status))throw E(400,'Status inválido.');
if(b.status==='open'&&j.status!=='open'){const c=coOf(me);if(usage(c).jobsOpen>=PLANS[c.plan].jobs)throw E(402,'Limite de vagas abertas do plano atingido.')}
j.status=b.status;save();return j}
const mm=p.match(/^\/api\/apps\/([0-9a-f-]{36})$/);
if(m==='PATCH'&&mm){perm(me,'move');const a=DB.apps.find(x=>x.id===mm[1]),jb=a&&DB.jobs.find(x=>x.id===a.jobId);if(!a||!jb||jb.companyId!==me.companyId)throw E(404,'Candidatura não encontrada.');
if(!ST.includes(b.status))throw E(400,'Status inválido.');
if(a.status!==b.status){(a.hist=a.hist||[]).push({t:Date.now(),by:me.name,from:a.status,to:b.status});a.status=b.status;save();log('app_status',ip,{uid:me.id,app:a.id,to:b.status})}return a}
throw E(404,'Rota não encontrada.')}
/* ---------- servidor HTTP ---------- */
const PUB=path.join(__dirname,'public'),IDX=path.join(PUB,'index.html');
try{fs.mkdirSync(PUB,{recursive:true})}catch(e){console.error('Não foi possível criar a pasta public:',e.message)}
const loadHTML=()=>{try{return fs.readFileSync(IDX)}catch{return null}};
let HTML=loadHTML();
if(!HTML)console.warn('AVISO: não encontrei '+IDX+'. Coloque o index.html dentro da pasta "public". O servidor continua rodando e passa a servir a página assim que o arquivo existir.');
const page=()=>{if(HTML&&PROD)return HTML;const h=loadHTML();if(h)HTML=h;return HTML};
const MISSING=Buffer.from('<!doctype html><meta charset="utf-8"><title>Talentos</title><body style="font-family:sans-serif;max-width:560px;margin:15vh auto;padding:0 1rem"><h1>Página não encontrada</h1><p>O arquivo <code>public/index.html</code> não foi encontrado no servidor. Coloque-o na pasta <code>public</code> ao lado do <code>server.js</code> e recarregue.</p></body>');
const HD={'X-Content-Type-Options':'nosniff','Referrer-Policy':'no-referrer','X-Frame-Options':'DENY','Cross-Origin-Opener-Policy':'same-origin','Cross-Origin-Resource-Policy':'same-origin',
'Permissions-Policy':'geolocation=(), camera=(), microphone=(), payment=()',
'Content-Security-Policy':"default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; connect-src 'self' https://servicodados.ibge.gov.br; img-src 'self' data:; base-uri 'none'; form-action 'none'; frame-ancestors 'none'",
...(PROD?{'Strict-Transport-Security':'max-age=31536000; includeSubDomains'}:{})};
const srv=http.createServer(async(req,res)=>{
for(const h in HD)res.setHeader(h,HD[h]);
const send=(c,t,type='application/json',cc='no-store')=>{res.setHeader('Cache-Control',cc);res.setHeader('Content-Type',type);res.writeHead(c);res.end(t)};
const j=(c,o)=>send(c,JSON.stringify(o));
const ip=(TRUST?String(req.headers['x-forwarded-for']||'').split(',').pop().trim():'')||req.socket.remoteAddress||'?';
try{
if(HOSTS.length&&!HOSTS.includes(req.headers.host))return j(400,{error:'Host inválido.'});
limit('g:'+ip,300,6e4);
const p=(req.url||'/').split('?')[0];
if(!p.startsWith('/api/')){if(req.method!=='GET'&&req.method!=='HEAD')return j(405,{error:'Método não permitido.'});const h=page();if(!h)return send(503,MISSING,'text/html; charset=utf-8');return send(200,h,'text/html; charset=utf-8','no-cache')}
if(!['GET','POST','PUT','PATCH','DELETE'].includes(req.method))return j(405,{error:'Método não permitido.'});
if(req.method!=='GET'){
 if(req.headers['x-requested-with']!=='talentos')throw E(403,'Requisição bloqueada.');
 const o=req.headers.origin;if(o){let h;try{h=new URL(o).host}catch{}if(h!==req.headers.host){log('csrf_block',ip);throw E(403,'Origem não permitida.')}}}
let s='';if(req.method!=='GET')for await(const ch of req){s+=ch;if(s.length>1e5){req.destroy();return}}
let b={};try{b=s?JSON.parse(s):{}}catch{throw E(400,'JSON inválido.')}
if(!b||typeof b!=='object'||Array.isArray(b))throw E(400,'Corpo inválido.');
const tk=th(ck(req.headers.cookie)[CN]||''),ss=DB.sessions[tk],now=Date.now();let me=null;
if(ss&&ss.exp>now&&ss.idle>now){me=DB.users.find(x=>x.id===ss.uid)||null;if(me)ss.idle=now+IDLE}
j(200,await route(req.method,p,b,{me,ip,res,tk:ss?tk:'',pt:String(req.headers['x-platform-token']||'')}))
}catch(e){if(e.c===429)log('rate_limit',ip);j(e.c||500,{error:e.c?e.m:'Erro interno.'});if(!e.c)console.error(e)}
});
srv.requestTimeout=15000;srv.headersTimeout=10000;srv.keepAliveTimeout=5000;srv.maxHeadersCount=50;
process.on('unhandledRejection',e=>console.error('unhandledRejection',e));
srv.listen(PORT,()=>{console.log('Talentos em http://localhost:'+PORT);if(!CODE)console.log('AVISO: defina RECRUITER_CODE para permitir o cadastro de recrutadores.')});
