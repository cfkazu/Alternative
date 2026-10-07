// 配合ラボのバランス確認用シミュレーション。ゲーム本体の遺伝・大会・寿命ロジックを写し、ボットに遊ばせて殿堂入りまでの日数を測る。
// 使い方: node tools/balance-sim.js [ゲーム数]  (寿命の倍率ごと) / CAPS=1 で飼育枠の上限ごと / NIGHT=1 で交配方式 (昼に交配 vs 夜にペア) ごとに比べる
function mulberry32(a){return function(){a|=0;a=(a+0x6D2B79F5)|0;let t=Math.imul(a^(a>>>15),1|a);t=(t+Math.imul(t^(t>>>7),61|t))^t;return((t^(t>>>14))>>>0)/4294967296;};}
const gauss=R=>{let u=0;while(!u)u=R();return Math.sqrt(-2*Math.log(u))*Math.cos(2*Math.PI*R());};
function poisson(l,R){const L=Math.exp(-l);let k=0,p=1;do{k++;p*=R();}while(p>L);return k-1;}
const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
const TRAITS=["str","cha","fer"], ADD={str:4,cha:4,fer:3,lon:3};
const LOCI=[];for(const t of ["str","cha","fer","lon"])for(let i=1;i<=ADD[t];i++)LOCI.push({id:t+i,trait:t,kind:"add"});
[{id:"M",f:.2},{id:"X",f:.9},{id:"Q",f:.03},{id:"D",f:.8},{id:"E",f:.5}].forEach(m=>LOCI.push({...m,kind:"mend"}));
const IDX=Object.fromEntries(LOCI.map((l,i)=>[l.id,i]));
const TL=Object.fromEntries(Object.keys(ADD).map(t=>[t,LOCI.map((l,i)=>l.trait===t?i:-1).filter(i=>i>=0)]));
const has=(g,id)=>g[IDX[id]][0]|g[IDX[id]][1], dose=(g,id)=>g[IDX[id]][0]+g[IDX[id]][1];
const cnt=(g,t)=>TL[t].reduce((s,i)=>s+g[i][0]+g[i][1],0);
function base(g){const M=has(g,"M"),sick=!has(g,"D"),mega=!has(g,"X"),q=dose(g,"Q");
 return{str:10+cnt(g,"str")/8*75+(M?15:0)+(mega?30:0)-(q===2?8:0)-(sick?25:0),cha:10+cnt(g,"cha")/8*80-(sick?15:0),fer:10+cnt(g,"fer")/6*80-(M?15:0)-(mega?20:0)+[0,18,32][q]-(sick?30:0)};}
const RAR=[{s:1,p:.5,f:.28},{s:2,p:.32,f:.4},{s:3,p:.13,f:.52},{s:4,p:.04,f:.65},{s:5,p:.01,f:.78}];
const TIERS=[40,55,68,80], PRIZE=[80,180,400,1000], PAY=[1,.3,.15];
const TOURS={race:{t:"str",off:0},contest:{t:"cha",off:0},show:{t:null,off:-6}};

function run(seed,cfg){
 const R=mulberry32(seed);
 const S={day:1,coins:400,tickets:1,cap:cfg.cap0??12,stock:[],tiers:{race:0,contest:0,show:0},cleared:{},hall:null,firstWin:{},deaths:0,champDeaths:0,deathAges:[],winAges:[],maxGen:0,sold:0,born:0};
 let nid=1;
 function life(g){ if(!cfg.life) return Infinity;
   const L=(14+cnt(g,"lon")*2+gauss(R)*1.5-(base(g).fer-50)/10*cfg.tradeoff)*cfg.life;
   return Math.max(Math.round(6*cfg.life),Math.round(L)); }
 function make(g,born,gen,star){const b=base(g),ph={};for(const t of TRAITS)ph[t]=clamp(Math.round(b[t]+gauss(R)*6),0,100);
   const ind={id:nid++,g,born,gen,ph,L:life(g),acted:0,star};S.stock.push(ind);S.maxGen=Math.max(S.maxGen,gen);return ind;}
 function gacha(){const r=(()=>{let x=R();for(const k of RAR){if((x-=k.p)<0)return k;}return RAR[0];})();
   const g=LOCI.map(l=>{const f=l.kind==="add"?r.f:l.id==="D"?.74+r.s*.03:l.f;return[R()<f?1:0,R()<f?1:0];});
   const ind=make(g,S.day-(2+Math.floor(R()*4)),0,r.s);ind.sex=R()<.5?"M":"F";return ind;}
 // 年齢による能力の倍率
 function af(ind){ if(!cfg.life) return 1; const a=S.day-ind.born, L=ind.L, e=dose(ind.g,"E");
   const [ps,pe]=e===2?[3,.5]:e===1?[4,.65]:[6,.8]; const end=Math.max(ps+2,Math.round(L*pe));
   if(a<ps) return .82+.18*(a-2)/Math.max(1,ps-2); if(a<=end) return 1; return 1-.3*(a-end)/Math.max(1,L-end);}
 const eff=(i,t)=>i.ph[t]*(t==="cha"?(1+(af(i)-1)*.5):af(i));
 const adult=i=>S.day-i.born>=2, free=i=>adult(i)&&i.acted!==S.day;
 const est=(i,t)=>eff(i,t)+(i.noise?.[t]??0);   // ボットは誤差つきでしか知らない
 const idx=i=>(i.ph.str+i.ph.cha+i.ph.fer)/3;   // 繁殖の選抜指標 (年齢補正前の素質)
 for(let k=0;k<4;k++){const ind=gacha();ind.sex=k%2?"F":"M";}
 while(S.day<=cfg.maxDay&&!S.hall){
   // 旅立ち
   const gone=S.stock.filter(i=>S.day-i.born>=i.L); S.deaths+=gone.length; for(const g of gone){ if(g.wins) S.champDeaths++; S.deathAges.push(S.day-g.born); } S.stock=S.stock.filter(i=>S.day-i.born<i.L);
   for(const i of S.stock) if(!i.noise) i.noise={str:gauss(R)*5,cha:gauss(R)*5,fer:gauss(R)*5};
   // 大会
   for(const [k,T] of Object.entries(TOURS)){ if(S.cleared[k]) continue;
     const val=i=>T.t?est(i,T.t):(est(i,"str")+est(i,"cha")+est(i,"fer"))/3;
     const c=S.stock.filter(free).sort((a,b)=>val(b)-val(a))[0]; if(!c) continue;
     c.acted=S.day; const real=T.t?eff(c,T.t):(eff(c,"str")+eff(c,"cha")+eff(c,"fer"))/3;
     const me=clamp(Math.round(real+gauss(R)*(T.t?6:5)),0,100), tier=S.tiers[k];
     let place=1; for(let j=0;j<7;j++) if(clamp(Math.round(TIERS[tier]+T.off+gauss(R)*7),0,100)>me) place++;
     S.coins+=place<=3?Math.round(PRIZE[tier]*PAY[place-1]):10;
     if(place===1){ c.wins=(c.wins||0)+1; S.winAges.push(S.day-c.born); if(tier<3) S.tiers[k]++; else { S.cleared[k]=S.day; S.firstWin[k]=c.gen; } }
   }
   if(["race","contest","show"].every(k=>S.cleared[k])) { S.hall=S.day; break; }
   // 交配: 夜にペアで。行動は使わない。1晩の組数は研究所の繁殖小屋で増える (1 → 2 → 3)
   const slots=cfg.nightly?1+(S.barn2?1:0)+(S.barn3?1:0):2;
   const bp=cfg.barnPrice||[500,1200];
   if(cfg.nightly&&!cfg.noBarn){ if(!S.barn2&&S.coins>bp[0]+400){S.coins-=bp[0];S.barn2=1;} else if(S.barn2&&!S.barn3&&S.coins>bp[1]+600){S.coins-=bp[1];S.barn3=1;} }
   const usedP=new Set();
   for(let p=0;p<slots;p++){ const room=S.cap-S.stock.length; if(room<2) break;
     const ok=i=>adult(i)&&!usedP.has(i)&&(cfg.nightly||free(i));
     const ms=S.stock.filter(i=>ok(i)&&i.sex==="M").sort((a,b)=>idx(b)-idx(a)), fs=S.stock.filter(i=>ok(i)&&i.sex==="F").sort((a,b)=>idx(b)-idx(a));
     if(!ms.length||!fs.length) break; const s=ms[0], d=fs[0]; usedP.add(s); usedP.add(d); if(!cfg.nightly) s.acted=d.acted=S.day;
     const n=Math.min(Math.max(1,poisson(.2+eff(d,"fer")/100*3.4+eff(s,"fer")/100*.8,R)),room);
     for(let j=0;j<n;j++){ const g=LOCI.map((_,i)=>[0,1].map(q=>{const pr=q?d.g[i]:s.g[i];let a=pr[R()<.5?0:1];if(R()<.005)a^=1;return a;}));
       const c=make(g,S.day,Math.max(s.gen,d.gen)+1,0); c.sex=R()<.5?"M":"F"; S.born++; } }
   // ガチャ
   while(S.tickets>0&&S.cap-S.stock.length>2){S.tickets--;gacha();}
   if(S.coins>700&&S.cap-S.stock.length>3&&S.maxGen<3){S.coins-=100;gacha();}
   // 枠を広げる
   if(S.coins>1200&&S.cap<(cfg.capMax??16)){S.coins-=300+Math.max(0,S.cap-12)*50;S.cap+=4;}
   // 間引き: 空きを4匹ぶん確保。素質が低い大人から売る
   while(S.cap-S.stock.length<4){ const c=S.stock.filter(adult).sort((a,b)=>idx(a)-idx(b))[0]; if(!c) break; S.stock=S.stock.filter(i=>i!==c); S.coins+=40; S.sold++; }
   S.herd=(S.herd||0)+S.stock.length; S.coins-=S.stock.reduce((s,i)=>s+(adult(i)?3:1),0);
   S.day++; if(S.tickets<3) S.tickets++;
 }
 const best=S.stock.slice().sort((a,b)=>idx(b)-idx(a))[0];
 return {herd:Math.round(S.herd/Math.max(1,S.day-1)),champDeaths:S.champDeaths,deathAges:S.deathAges,winAges:S.winAges,hall:S.hall,cleared:S.cleared,gen:S.maxGen,firstWin:S.firstWin,deaths:S.deaths,born:S.born,coins:S.coins,bestIdx:best?Math.round(idx(best)):0};
}
const scen=process.env.NIGHT?[["昼に交配(旧)",{life:1,tradeoff:1}],["夜 小屋500/1200",{life:1,tradeoff:1,nightly:1}],["夜 1組のみ",{life:1,tradeoff:1,nightly:1,noBarn:1}],["夜 小屋1200/3000",{life:1,tradeoff:1,nightly:1,barnPrice:[1200,3000]}]]:process.env.CAPS?[["上限8",{life:1,tradeoff:1,cap0:8,capMax:8}],["上限12",{life:1,tradeoff:1,cap0:12,capMax:12}],["上限16",{life:1,tradeoff:1,cap0:12,capMax:16}],["上限20",{life:1,tradeoff:1,cap0:12,capMax:20}],["上限28",{life:1,tradeoff:1,cap0:12,capMax:28}]]:[["寿命なし",{life:0}],["短め x0.6",{life:.6,tradeoff:1}],["中 x1.0",{life:1,tradeoff:1}],["中 x1.3",{life:1.3,tradeoff:1}],["長め x2.0",{life:2,tradeoff:1}]];
const N=+process.argv[2]||60;
const med=a=>{const s=a.slice().sort((x,y)=>x-y);return s[Math.floor(s.length/2)];};
const pct=(a,q)=>{const s=a.slice().sort((x,y)=>x-y);return s[Math.floor((s.length-1)*q)];};
for(const [name,c] of scen){ const cfg={maxDay:200,...c}; const rs=[];for(let s=1;s<=N;s++)rs.push(run(s*7919,cfg));
  const ok=rs.filter(r=>r.hall), days=ok.map(r=>r.hall);
  const firsts=k=>rs.filter(r=>r.cleared[k]).map(r=>r.cleared[k]);
  const da=rs.flatMap(r=>r.deathAges), wa=rs.flatMap(r=>r.winAges);
  console.log(`   ${name}: 優勝した子の旅立ち 中央${med(rs.map(r=>r.champDeaths))}匹/ゲーム  旅立ち年齢 中央${da.length?med(da):'-'}日  優勝時の年齢 中央${med(wa)}日 (90%:${pct(wa,.9)})`);
  console.log(`${name.padEnd(10)} 平均頭数${med(rs.map(r=>r.herd))} 殿堂入り ${ok.length}/${N}  日数 中央${days.length?med(days):"-"} (25%:${days.length?pct(days,.25):"-"} 75%:${days.length?pct(days,.75):"-"})  世代 中央${med(rs.map(r=>r.gen))}  王者到達日 中央 レース${med(firsts("race"))??"-"} コンテスト${med(firsts("contest"))??"-"} 品評会${firsts("show").length?med(firsts("show")):"-"}  旅立ち${med(rs.map(r=>r.deaths))}匹  誕生${med(rs.map(r=>r.born))}匹`);
}
