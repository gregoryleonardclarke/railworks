(()=>{'use strict';
const $=s=>document.querySelector(s), $all=s=>[...document.querySelectorAll(s)];
const canvas=$('#glcanvas'),overlay=$('#hudcanvas'),ctx=overlay.getContext('2d');
const gl=canvas.getContext('webgl',{antialias:true,alpha:false,depth:true,stencil:false,preserveDrawingBuffer:false});
if(!gl){$('#failure').style.display='block';return;}
const WORLD_X=180,WORLD_Z=140,CELL=2.56,PORT=CELL*.39,STORAGE='railworks-3d-v5',OLD_STORAGE='railworks-3d-v3',FIRST_STORAGE='railworks-3d-v2';
const K=(x,z)=>x+','+z, parseKey=k=>k.split(',').map(Number), world=k=>{let a=parseKey(k);return {x:a[0]*CELL,z:a[1]*CELL};};
const mix=(a,b,t)=>a+(b-a)*t, clamp=(v,a,b)=>Math.max(a,Math.min(b,v)),dist=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z);
const edgeKey=(a,b)=>a<b?a+'|'+b:b+'|'+a;
const C={ground:'#5c795c',grass:'#547856',sleep:'#684b39',bed:'#7c7464',rail:'#e1e0ce',railSide:'#787e79',shadow:'#3b5745',yellow:'#e9b75f'};
const rgb=hex=>{let s=hex[0]==='#'?hex.slice(1):hex;return [parseInt(s.slice(0,2),16)/255,parseInt(s.slice(2,4),16)/255,parseInt(s.slice(4,6),16)/255]};
let graph=new Map(),stations=[],industries=[],trains=[],signals=[],points=new Map(),nextTrain=1,nextStation=1,nextSignal=1,nextIndustry=1,selectedTrainId=null,mode='rail',anchor=null,hover=null,showGrid=true,showBlocks=false,signalReverse=false,paused=false,dirty=true,noticeExpiry=0,anchorFrom=null,previewNodes=null,previewKey='',lastBuild=[],blockByEdge=new Map(),blocks=[],bank=5000,delivered=0,industryClock=0,railHeading=0;
const camera={x:90*CELL,z:70*CELL,zoom:.82,yaw:-.77,elev:.94};
// Target orientation interpolates toward the drag/keyboard controls. Camera movement
// remains screen-space consistent at every yaw and tilt.
const viewTarget={yaw:camera.yaw,elev:camera.elev};
const heldKeys=new Set();
let viewport={w:innerWidth,h:innerHeight},mouse={x:0,y:0,down:false,dragging:false,button:0,lastX:0,lastY:0,downX:0,downY:0},timePrev=0,uiTick=0,minimapTick=0;
function keyValid(k){let [x,z]=parseKey(k);return Number.isInteger(x)&&Number.isInteger(z)&&x>=0&&z>=0&&x<WORLD_X&&z<WORLD_Z}
function neighbors(a){return [...(graph.get(a)||[])].filter(n=>graph.get(n)?.has(a))}
function link(a,b){if(a===b||!keyValid(a)||!keyValid(b))return false;let [ax,az]=parseKey(a),[bx,bz]=parseKey(b);if(Math.max(Math.abs(ax-bx),Math.abs(az-bz))!==1)return false;if(!graph.has(a))graph.set(a,new Set());if(!graph.has(b))graph.set(b,new Set());let exists=graph.get(a).has(b);graph.get(a).add(b);graph.get(b).add(a);dirty=true;return !exists}
function removeEdge(a,b){graph.get(a)?.delete(b);graph.get(b)?.delete(a);if(graph.get(a)?.size===0)graph.delete(a);if(graph.get(b)?.size===0)graph.delete(b);signals=signals.filter(s=>edgeKey(s.a,s.b)!==edgeKey(a,b));if(graph.get(a)?.size===0)graph.delete(a);if(graph.get(b)?.size===0)graph.delete(b);recomputeBlocks();dirty=true}
// Actual physical rail ports and turn curves. Rails no longer run to a hard corner
// at the centre of the grid: every edge ends at a turnout/crossing port, and
// compatible routes connect those ports via tangent-continuous cubic curves.
const unit=(a,b)=>{let d=dist(a,b)||1;return{x:(b.x-a.x)/d,z:(b.z-a.z)/d}};
function port(node,adj){let n=world(node);if(neighbors(node).length<=1)return n;let v=unit(n,world(adj));return{x:n.x+v.x*PORT,z:n.z+v.z*PORT}}
function bendAllowed(a,node,b){if(!a||!b)return true;if(a===b)return false;let p=world(a),c=world(node),q=world(b),u=unit(p,c),v=unit(c,q);return u.x*v.x+u.z*v.z>=.69}
function edgeEnds(a,b){return [port(a,b),port(b,a)]}
function curveAt(a,node,b,t){let center=world(node),start=port(node,a),end=port(node,b);
 let inDir=unit(start,center),outDir=unit(center,end),h=PORT*.78;
 let c1={x:start.x+inDir.x*h,z:start.z+inDir.z*h},c2={x:end.x-outDir.x*h,z:end.z-outDir.z*h};let u=1-t;
 return{x:u*u*u*start.x+3*u*u*t*c1.x+3*u*t*t*c2.x+t*t*t*end.x,z:u*u*u*start.z+3*u*u*t*c1.z+3*u*t*t*c2.z+t*t*t*end.z}}
function curveLength(a,n,b){let len=0,prev=curveAt(a,n,b,0);for(let i=1;i<=28;i++){let q=curveAt(a,n,b,i/28);len+=dist(prev,q);prev=q}return len}
const DIRS=[[1,0],[1,1],[0,1],[-1,1],[-1,0],[-1,-1],[0,-1],[1,-1]];
function planRail(a,b,prev=null){
 if(!keyValid(a)||!keyValid(b)||a===b)return null;
 const [ax,az]=parseKey(a),[bx,bz]=parseKey(b),margin=12;
 const minX=Math.max(0,Math.min(ax,bx)-margin),maxX=Math.min(WORLD_X-1,Math.max(ax,bx)+margin);
 const minZ=Math.max(0,Math.min(az,bz)-margin),maxZ=Math.min(WORLD_Z-1,Math.max(az,bz)+margin);
 const heuristic=n=>dist(world(n),world(b));
 const state=(n,dir,cool)=>n+'@'+dir+'@'+cool,heap=[];
 function push(v){let i=heap.length;heap.push(v);while(i>0){let p=(i-1)>>1;if(heap[p].f<=v.f)break;heap[i]=heap[p];i=p}heap[i]=v}
 function pop(){let top=heap[0],tail=heap.pop();if(heap.length){let i=0;while(i*2+1<heap.length){let l=i*2+1,r=l+1,j=r<heap.length&&heap[r].f<heap[l].f?r:l;if(heap[j].f>=tail.f)break;heap[i]=heap[j];i=j}heap[i]=tail}return top}
 let startDir=-1;if(prev){let p=parseKey(prev);startDir=DIRS.findIndex(([dx,dz])=>dx===ax-p[0]&&dz===az-p[1])}
 const origin=state(a,startDir,0),seen=new Map([[origin,0]]),links=new Map();
 push({n:a,dir:startDir,cool:0,g:0,f:heuristic(a)*1.18,key:origin});
 let result=null;
 for(let steps=0;heap.length&&steps<120000;steps++){
  const cur=pop();if(cur.g>(seen.get(cur.key)??Infinity)+.001)continue;
  if(cur.n===b){result=cur.key;break}
  let [x,z]=parseKey(cur.n);
  for(let dir=0;dir<DIRS.length;dir++){
   let [dx,dz]=DIRS[dir],nx=x+dx,nz=z+dz;
   if(nx<minX||nx>maxX||nz<minZ||nz>maxZ)continue;
   let delta=cur.dir<0?0:Math.min((dir-cur.dir+8)%8,(cur.dir-dir+8)%8);
   if(delta>1||(delta===1&&cur.cool>0))continue;
   let cool=delta?2:Math.max(0,cur.cool-1),next=K(nx,nz);
   let existing=graph.get(cur.n)?.has(next),g=cur.g+Math.hypot(dx,dz)*CELL+(delta?CELL*1.05:0)-(existing?.17:0),key=state(next,dir,cool);
   if(g>=(seen.get(key)??Infinity)-.001)continue;
   seen.set(key,g);links.set(key,cur.key);push({n:next,dir,cool,g,key,f:g+heuristic(next)*1.18});
  }
 }
 if(!result)return null;
 const path=[];for(let k=result;k;k=links.get(k))path.unshift(k.split('@')[0]);
 return path;
}
function routeCanBuild(path){return !!(path&&path.length>=2&&!path.some(n=>industries.some(s=>dist(world(n),world(s.node))<3.7)))}
function layPlanned(a,b,incoming=null){let route=planRail(a,b,incoming);if(!routeCanBuild(route))return{added:0,route:null};let added=0;
 let created=[];for(let i=1;i<route.length;i++)if(link(route[i-1],route[i])){added++;created.push([route[i-1],route[i]])}
 if(added){lastBuild=created;recomputeBlocks()}
 return{added,route};}
function addLine(a,b){return layPlanned(a,b).added}
function ensureRoute(nodes){for(let i=1;i<nodes.length;i++)link(K(...nodes[i-1]),K(...nodes[i]))}
function stationById(id){return stations.find(s=>s.id===id)}
const DEPOSITS=[
 {kind:'timber',x:61,z:54,r:10},{kind:'timber',x:44,z:83,r:12},{kind:'timber',x:130,z:102,r:13},
 {kind:'timber',x:155,z:35,r:11},{kind:'timber',x:92,z:118,r:9},
 {kind:'iron',x:112,z:53,r:9},{kind:'iron',x:71,z:104,r:8},{kind:'iron',x:148,z:75,r:9},
 {kind:'iron',x:32,z:27,r:11},{kind:'iron',x:116,z:116,r:9}
];
function depositNear(node,kind){let p=world(node);return DEPOSITS.some(d=>d.kind===kind&&Math.hypot(p.x-d.x*CELL,p.z-d.z*CELL)<d.r*CELL)}
function nearestSite(node){let p=world(node),best=null,d=Infinity;for(let site of industries){let n=dist(p,world(site.node));if(n<d&&n<=18){d=n;best=site}}return best}
function addIndustry(kind,node){
 if(!keyValid(node)||industries.some(s=>dist(world(s.node),world(node))<9))return null;
 if((kind==='timber'||kind==='iron')&&!depositNear(node,kind))return null;
 if(industries.length>=120)return null;
 const names={timber:'Logging camp',iron:'Ore mine',depot:'Machine works',freight:'Distribution hub'};
 let site={id:'i'+nextIndustry++,kind,node,name:names[kind]+' '+String(nextIndustry-1).padStart(2,'0'),stock:{timber:0,steel:0,machinery:0},received:{timber:0,steel:0,machinery:0},production:0};
 industries.push(site);dirty=true;updateIndustryUI();return site;
}
function emptyWorld(){
 graph=new Map();stations=[];industries=[];trains=[];signals=[];points=new Map();
 nextTrain=nextStation=nextSignal=nextIndustry=1;bank=5000;delivered=0;industryClock=0;selectedTrainId=null;
 anchor=null;anchorFrom=null;previewNodes=null;lastBuild=[];dirty=true;
 camera.x=90*CELL;camera.z=70*CELL;camera.zoom=.82;
 recomputeBlocks();setMode('timber',true);updateUI();updateIndustryUI();
 announce('New frontier: build logging camps in green forest zones and ore mines in grey-blue ore deposits. Nothing is prebuilt.');
}
function demo(){emptyWorld()}
function addStation(name,node,kind='freight',doDirty=true){let site=nearestSite(node);kind=site?.kind||kind;let s={id:'s'+nextStation++,name:site?site.name+' Station':name,node,kind,siteId:site?.id||null,stock:{timber:0,steel:0,machinery:0},received:{timber:0,steel:0,machinery:0},production:0};stations.push(s);if(doDirty)dirty=true;return s}
function ensureIndustry(s){if(!s.stock)s.stock={timber:0,steel:0,machinery:0};if(!s.received)s.received={timber:0,steel:0,machinery:0};if(s.production===undefined)s.production=0}
const GOODS={timber:{label:'Timber',icon:'🌲',color:'#bf8d5b'},steel:{label:'Steel',icon:'⚙',color:'#aeb8c1'},machinery:{label:'Machinery',icon:'📦',color:'#efc06e'}};
function takeGoods(s,good,count){let n=Math.min(count,Math.floor(s.stock[good]||0));s.stock[good]-=n;return n}
function accepts(s,good){return (s.kind==='depot'&&['timber','steel'].includes(good))||(s.kind==='freight'&&good==='machinery')}
function cargoStop(t,st){ensureIndustry(st);let good=t.freightType||'timber',cap=Math.max(0,t.cars)*14;
if((t.load||0)>0&&accepts(st,t.loadGood||good)){let oldGood=t.loadGood||good;let unload=t.load;t.load=0;st.received[oldGood]=(st.received[oldGood]||0)+unload;t.cargo='EMPTY';if(st.kind==='freight'){delivered+=unload;bank+=unload*26;announce(`${t.name} delivered ${unload} machinery · +£${unload*26}`)}else announce(`${t.name} delivered ${unload} ${GOODS[oldGood].label} to ${st.name}`)}
if(st.stock[good]>0&&t.load===0&&cap>0){let quantity=takeGoods(st,good,cap);if(quantity){t.load=quantity;t.loadGood=good;t.cargo=good.toUpperCase();announce(`${t.name} loaded ${quantity} ${GOODS[good].label} at ${st.name}`)}}
}
function tickIndustry(dt){
 industryClock+=dt;
 for(let s of stations){let site=nearestSite(s.node);if(site){s.siteId=site.id;s.kind=site.kind;s.name=site.name+' Station'}else{s.siteId=null;s.kind='unassigned'}}
 for(let site of industries){ensureIndustry(site);
  if(site.kind==='timber')site.stock.timber=Math.min(260,site.stock.timber+dt*.7);
  if(site.kind==='iron')site.stock.steel=Math.min(260,site.stock.steel+dt*.55);
  if(site.kind==='depot'){
   site.production+=dt;
   while(site.production>=2.8&&site.received.timber>=2&&site.received.steel>=1&&site.stock.machinery<260){
    site.production-=2.8;site.received.timber-=2;site.received.steel-=1;site.stock.machinery+=1;
   }
   site.production=Math.min(site.production,2.8);
  }
  const links=stations.filter(s=>s.siteId===site.id);
  for(const stop of links){ensureIndustry(stop);
   for(const item of ['timber','steel','machinery']){
    if(site.stock[item]>0&&stop.stock[item]<140){let n=Math.min(site.stock[item],140-stop.stock[item],dt*6);site.stock[item]-=n;stop.stock[item]+=n}
    if(stop.received[item]>0&&['depot','freight'].includes(site.kind)){
     const n=stop.received[item];site.received[item]+=n;stop.received[item]=0;
    }
   }
  }
 }
 if(industryClock>.7){industryClock=0;updateIndustryUI()}
}
function updateIndustryUI(){
 const el=$('#industryContent');if(!el)return;
 const count=kind=>industries.filter(s=>s.kind===kind).length;
 const stock=(kind,item)=>Math.floor(industries.filter(s=>s.kind===kind).reduce((n,s)=>n+(s.stock[item]||0),0));
 const input=item=>Math.floor(industries.filter(s=>s.kind==='depot').reduce((n,s)=>n+(s.received[item]||0),0));
 el.innerHTML='<div class="industry-chain">'+
 '<span>🌲 Logging camps <b>'+count('timber')+' · '+stock('timber','timber')+' logs</b></span>'+
 '<span>⛏ Ore mines <b>'+count('iron')+' · '+stock('iron','steel')+' ore</b></span>'+
 '<span>🏭 Machine works <b>'+count('depot')+' · '+stock('depot','machinery')+' machines</b></span>'+
 '<span>📦 Distribution hubs <b>'+count('freight')+'</b></span></div>'+
 '<p class="industry-note">Factory inputs: '+input('timber')+' timber + '+input('steel')+' steel. Build a station on nearby track to connect each facility.</p>';
 $('#credits').textContent=Math.floor(bank);$('#deliveries').textContent=delivered;
}
function createTrain(from,to,starter=false){if(!graph.get(from)?.has(to))return null;let t={id:nextTrain++,name:starter?'Pioneer 01':`Locomotive ${String(nextTrain-1).padStart(2,'0')}`,from,to,progress:0,past:[],cars:starter?2:1,speed:0,speedCap:starter?4.8:4.1,halted:false,auto:true,dwell:0,status:'Running',schedule:stations.map(s=>s.id),stopIndex:0,target:stations[0]?.id||null,cargo:'EMPTY',load:0,loadGood:'timber',freightType:'timber',manualPoints:false,color:starter?'#cc5949':(['#4f99a4','#d99f48','#a56b82'][nextTrain%3]),distanceTotal:0};trains.push(t);selectedTrainId=t.id;dirty=true;return t}
function seedPast(from,to){let past=[],prev=to,at=from;for(let i=0;i<7;i++){let opts=neighbors(at).filter(k=>k!==prev&&!past.includes(k));if(!opts.length)break;let p=world(prev),h=world(at),wx=h.x-p.x,wz=h.z-p.z;opts.sort((a,b)=>{let aa=world(a),bb=world(b);return ((bb.x-h.x)*wx+(bb.z-h.z)*wz)-((aa.x-h.x)*wx+(aa.z-h.z)*wz)});let next=opts[0];past.push(next);prev=at;at=next}return past}
// Signal cut points partition the physical network into occupancy blocks.
// A directed signal at node a faces into edge a->b; it separates that edge
// from the remaining incident tracks at a, but not from what lies beyond b.
function recomputeBlocks(){let edges=[];for(let [a,nn] of graph)for(let b of nn)if(a<b)edges.push(edgeKey(a,b));let parent=new Map(edges.map(e=>[e,e]));const find=e=>{let q=e;while(parent.get(q)!==q)q=parent.get(q);while(parent.get(e)!==q){let n=parent.get(e);parent.set(e,q);e=n}return q};const union=(a,b)=>{let ra=find(a),rb=find(b);if(ra!==rb)parent.set(ra,rb)};
let dirs=new Set(signals.map(s=>s.a+'>'+s.b));for(let [node,ns] of graph){let incident=[...ns].map(n=>edgeKey(node,n)).filter(e=>parent.has(e)&&!dirs.has(node+'>'+((e.split('|')[0]===node)?e.split('|')[1]:e.split('|')[0])));for(let i=1;i<incident.length;i++)union(incident[0],incident[i])}
// Independent tracks may intersect at a diamond without sharing a routable vertex.
// They stay topologically independent but occupy a common protected block.
for(let i=0;i<edges.length;i++)for(let j=i+1;j<edges.length;j++){
 const [a,b]=edges[i].split('|'),[c,d]=edges[j].split('|');if(a===c||a===d||b===c||b===d)continue;
 let A=world(a),B=world(b),C=world(c),D=world(d);
 let orient=(p,q,r)=>(q.x-p.x)*(r.z-p.z)-(q.z-p.z)*(r.x-p.x);
 if(orient(A,B,C)*orient(A,B,D)<-.0001&&orient(C,D,A)*orient(C,D,B)<-.0001)union(edges[i],edges[j]);
}
blockByEdge=new Map();let ids=new Map();blocks=[];for(let e of edges){let root=find(e);if(!ids.has(root)){let id=blocks.length;ids.set(root,id);blocks.push({id,edges:[]})}let id=ids.get(root);blockByEdge.set(e,id);blocks[id].edges.push(e)}updateStats()}
function signalAt(a,b){return signals.find(s=>s.a===a&&s.b===b)}
function placeSignal(a,b,type){if(!graph.get(a)?.has(b))return;let existing=signalAt(a,b);if(existing){if(existing.type===type){signals=signals.filter(s=>s!==existing);announce('Signal removed.')}else{existing.type=type;announce('Changed to '+(type==='chain'?'chain':'block')+' signal.')}}else{signals.push({id:nextSignal++,a,b,type});announce((type==='chain'?'Chain':'Block')+' signal placed, facing travel '+a+' → '+b+'.')}recomputeBlocks();dirty=true}
function occupiedBy(){let occ=new Map();for(let t of trains)for(let edge of trainOccupied(t)){let block=blockByEdge.get(edge);if(block===undefined)continue;if(!occ.has(block))occ.set(block,new Set());occ.get(block).add(t.id)}return occ}
function availableBlock(block,trainId,occ,reservations){if(block===undefined)return true;let users=occ.get(block);if(users&&[...users].some(id=>id!==trainId))return false;let reserved=reservations?.get(block);return reserved===undefined||reserved===trainId}
function entryBlocks(t,a,b,occ,reservations){let sig=signalAt(a,b),block=blockByEdge.get(edgeKey(a,b));if(!sig)return {ok:true,blocks:[]};if(!availableBlock(block,t?.id,occ,reservations))return{ok:false,blocks:[],reason:'Block occupied'};
let needs=new Set([block]);if(sig.type==='chain'){
let destination=stationById(t?.target)?.node;let path=destination?shortest(b,destination):null;let future=path?.length?path:[b];let foundExit=false;
for(let i=1;i<Math.min(90,future.length);i++){let u=future[i-1],v=future[i],nextSig=signalAt(u,v),blockId=blockByEdge.get(edgeKey(u,v));if(blockId!==undefined)needs.add(blockId);if(!availableBlock(blockId,t?.id,occ,reservations))return{ok:false,blocks:[],reason:'Chain waits for clear exit'};if(nextSig?.type==='rail'){foundExit=true;break}}
// A destination station itself is a valid terminus; no exit signal needed.
if(!foundExit&&(!destination||future.at(-1)!==destination))return{ok:false,blocks:[],reason:'Chain needs a downstream exit'};
}
return{ok:true,blocks:[...needs]}}
function signalStatus(s){let train=trains.find(t=>t.from===s.a&&t.to===s.b),occ=occupiedBy();let routes=train?[train.target]:stations.map(st=>st.id);return routes.some(id=>entryBlocks(train||{id:-1,target:id},s.a,s.b,occ,new Map()).ok)?'green':'red'}
function pointBranches(node){return neighbors(node)}
function turnPoint(node){let exits=pointBranches(node);if(exits.length<3)return false;let n=(points.get(node)||0);points.set(node,(n+1)%exits.length);dirty=true;announce(`Junction ${node}: preferred exit ${((n+1)%exits.length)+1} of ${exits.length}. Scheduled trains set points automatically.`);return true}
function pointExit(node,incoming=null){let exits=pointBranches(node).sort().filter(n=>n!==incoming);return exits[(points.get(node)||0)%exits.length]}
function shortestHeading(previous,start,goal){if(!graph.has(start)||!graph.has(goal))return null;if(start===goal)return[start];
 let states=new Map(),todo=[],pathPrev=new Map();const key=(p,n)=>String(p||'none')+'>'+n,first=key(previous,start);
 states.set(first,0);todo.push({n:start,prev:previous,id:first,g:0});
 while(todo.length){let best=0;for(let i=1;i<todo.length;i++)if(todo[i].g<todo[best].g)best=i;
 let here=todo.splice(best,1)[0];if(here.g>(states.get(here.id)??Infinity))continue;
 if(here.n===goal){let route=[here.n],k=here.id;while(pathPrev.has(k)){let back=pathPrev.get(k);route.unshift(back.node);k=back.id}return route}
 for(let n of neighbors(here.n)){if(!bendAllowed(here.prev,here.n,n))continue;let nextId=key(here.n,n);
 let cost=dist(world(here.n),world(n))+(here.prev? .42*(1-((world(here.n).x-world(here.prev).x)*(world(n).x-world(here.n).x)+(world(here.n).z-world(here.prev).z)*(world(n).z-world(here.n).z))/(dist(world(here.prev),world(here.n))*dist(world(here.n),world(n)))):0);
 let g=here.g+cost;if(g>=(states.get(nextId)??Infinity))continue;states.set(nextId,g);pathPrev.set(nextId,{id:here.id,node:here.n});todo.push({n,prev:here.n,id:nextId,g});
 }}return null;}
function shortest(start,goal){return shortestHeading(null,start,goal)}
function bestNext(train,at,incoming=train.from){if(train.manualPoints&&neighbors(at).length>=3){let exits=neighbors(at).filter(n=>bendAllowed(incoming,at,n));let preferred=pointExit(at,incoming);if(exits.includes(preferred))return preferred;if(exits.length)return exits[0]}let target=stationById(train.target);
 if(target){let p=shortestHeading(incoming,at,target.node);if(p?.length>1)return p[1];if(!p)return null}
 let exits=neighbors(at).filter(n=>bendAllowed(incoming,at,n));if(!exits.length)return null;
 if((train.manualPoints||!target)&&exits.length>1){let preferred=pointExit(at,incoming);return exits.includes(preferred)?preferred:exits[0]}
 let before=world(incoming),here=world(at),wanted={x:here.x-before.x,z:here.z-before.z};
 exits.sort((a,b)=>{let aa=world(a),bb=world(b);return ((bb.x-here.x)*wanted.x+(bb.z-here.z)*wanted.z)-((aa.x-here.x)*wanted.x+(aa.z-here.z)*wanted.z)});
 return exits[0]}
function head(t){if(t.phase==='turn'){return curveAt(t.turnPrev,t.turnNode,t.turnNext,t.turnProgress||0)}let [a,b]=edgeEnds(t.from,t.to);return{x:mix(a.x,b.x,clamp(t.progress||0,0,1)),z:mix(a.z,b.z,clamp(t.progress||0,0,1))}}
function resetTrail(t){let p=head(t),at=t.distanceTotal||0;t.trail=[{x:p.x,z:p.z,s:at}];let earlier=[world(t.from),...(t.past||[]).filter(keyValid).map(world)];let cursor=p,s=at;
 for(let next of earlier){let length=dist(cursor,next),n=Math.ceil(length/.22);for(let i=1;i<=n;i++){let part=i/n;t.trail.push({x:mix(cursor.x,next.x,part),z:mix(cursor.z,next.z,part),s:s-length*part})}s-=length;cursor=next;if(at-s>24)break}}
function recordTrail(t,previous,now,moved){if(!t.trail?.length)resetTrail(t);if(moved<=0)return;
 let s0=t.distanceTotal||0,steps=Math.max(1,Math.ceil(moved/.13));for(let i=1;i<=steps;i++){let k=i/steps;t.trail.unshift({x:mix(previous.x,now.x,k),z:mix(previous.z,now.z,k),s:s0+moved*k})}
 t.distanceTotal=s0+moved;while(t.trail.length>2&&t.trail.at(-2).s<t.distanceTotal-25)t.trail.pop();}
function behind(t,d){if(!t.trail?.length)resetTrail(t);let target=(t.distanceTotal||0)-d,arr=t.trail;
 if(target>=arr[0].s)return{x:arr[0].x,z:arr[0].z};for(let i=1;i<arr.length;i++)if(arr[i].s<=target){let a=arr[i-1],b=arr[i],f=clamp((a.s-target)/((a.s-b.s)||1),0,1);return{x:mix(a.x,b.x,f),z:mix(a.z,b.z,f)}}
 let a=arr.at(-2)||arr[0],b=arr.at(-1),l=dist(a,b)||1,g=b.s-target;return{x:b.x+(b.x-a.x)*g/l,z:b.z+(b.z-a.z)*g/l}}
function trainCars(t){let p=[head(t)];for(let i=1;i<=t.cars;i++)p.push(behind(t,i*2.55));return p}
function trainOccupied(t){let set=new Set([edgeKey(t.from,t.to)]),len=dist(world(t.from),world(t.to));if(t.phase==='turn'&&t.turnNode&&t.turnNext)set.add(edgeKey(t.turnNode,t.turnNext));let remaining=(t.cars*2.55+1)-len*t.progress,prev=t.from;for(let n of (t.past||[])){if(remaining<=0)break;set.add(edgeKey(prev,n));remaining-=dist(world(prev),world(n));prev=n}return set}
function approachingConflict(t){let near=head(t),other=trains.filter(u=>u!==t);for(let u of other){let cars=trainCars(u);for(let [i,p] of cars.entries()){if(dist(near,p)<(i===0?2.25:1.82))return true}let here=u.from,next=u.to;if(edgeKey(t.from,t.to)===edgeKey(here,next)){let uHead=head(u);if(dist(near,uHead)<5)return true}}return false}
function reached(t,node){let st=stationById(t.target);if(st&&st.node===node){cargoStop(t,st);t.dwell=2.7;t.speed=0;t.status='At station';if(!t.auto)t.halted=true;t.cargo=st.kind==='timber'?'TIMBER':st.kind==='iron'?'STEEL':st.kind==='freight'?'GOODS':'EMPTY';if(t.auto&&t.schedule.length>1){let idx=t.schedule.indexOf(t.target);t.stopIndex=(idx+1)%t.schedule.length;t.nextTarget=t.schedule[t.stopIndex]}announce(`${t.name} arrived at ${st.name}`)}}
function tickTrains(dt){tickIndustry(dt);let occupied=occupiedBy(),reserved=new Map();
 for(let t of trains){
  if(!t.phase)t.phase='edge';if(!t.trail?.length)resetTrail(t);
  if(t.dwell>0){t.dwell=Math.max(0,t.dwell-dt);t.speed=0;t.status='Loading / unloading';if(t.dwell<=0&&t.nextTarget){t.target=t.nextTarget;t.nextTarget=null}continue}
  if(t.phase==='edge'&&!graph.get(t.from)?.has(t.to)){t.speed=0;t.status='Rail removed — route broken';continue}
  if(t.phase==='waiting'){
   let n=bestNext(t,t.to,t.from);if(!n||!graph.get(t.to)?.has(n)){t.speed=0;t.status='No compatible route — extend the line';continue}
   t.turnPrev=t.from;t.turnNode=t.to;t.turnNext=n;t.turnProgress=0;t.phase='turn';
  }
  let movingTurn=t.phase==='turn',entry=movingTurn?entryBlocks(t,t.turnNode,t.turnNext,occupied,reserved):entryBlocks(t,t.from,t.to,occupied,reserved);
  let next=!movingTurn?bestNext(t,t.to,t.from):null;
  let follow=next?entryBlocks(t,t.to,next,occupied,reserved):{ok:true};
  let length=movingTurn?curveLength(t.turnPrev,t.turnNode,t.turnNext):dist(...edgeEnds(t.from,t.to));
  let progress=movingTurn?(t.turnProgress||0):t.progress;
  let gap=(1-progress)*length,braking=8.5;
  let mustStop=!entry.ok&&(movingTurn||progress<.001),conflict=approachingConflict(t);
  let approachSpeed=(!movingTurn&&!follow.ok&&next)?Math.sqrt(Math.max(0,2*braking*Math.max(0,gap-.3))):t.speedCap;
  let targetSpeed=(t.halted||conflict||mustStop)?0:Math.min(t.speedCap,approachSpeed);
  t.status=t.halted?'Stopped':mustStop?(entry.reason||'Red signal'):conflict?'Traffic hold':targetSpeed<t.speedCap*.7?'Approaching red':movingTurn?'Taking junction':'Running';
  let accel=targetSpeed<t.speed?braking:2.6;t.speed+=clamp(targetSpeed-t.speed,-accel*dt,accel*dt);
  let travel=t.speed*dt;if(travel<.00001)continue;
  for(let guard=0;travel>.00001&&guard<80;guard++){
   movingTurn=t.phase==='turn';let currentFrom=movingTurn?t.turnNode:t.from,currentTo=movingTurn?t.turnNext:t.to;
   let permit=entryBlocks(t,currentFrom,currentTo,occupied,reserved),atStart=movingTurn?(t.turnProgress||0)<.00001:t.progress<.00001;
   if(atStart&&!permit.ok){t.speed=0;t.status=permit.reason||'Signal stop';break}
   for(let b of permit.blocks)reserved.set(b,t.id);
   let len=movingTurn?curveLength(t.turnPrev,t.turnNode,t.turnNext):dist(...edgeEnds(t.from,t.to));
   let progress=movingTurn?(t.turnProgress||0):t.progress;
   let movement=Math.min(travel,.16,Math.max(0,(1-progress)*len));if(movement<.00000001){break}
   let was=head(t),nextProgress=clamp(progress+movement/Math.max(.01,len),0,1);
   if(movingTurn)t.turnProgress=nextProgress;else t.progress=nextProgress;
   let now=head(t);recordTrail(t,was,now,movement);travel-=movement;
   if(nextProgress>=1-0.000001){
    if(movingTurn){t.past.unshift(t.turnPrev);t.past=t.past.slice(0,55);t.from=t.turnNode;t.to=t.turnNext;t.progress=0;t.phase='edge';t.turnPrev=null;t.turnNode=null;t.turnNext=null;t.turnProgress=0;}
    else{t.phase='waiting';reached(t,t.to);if(t.dwell>0){travel=0;break}let next=bestNext(t,t.to,t.from);
     if(!next){t.speed=0;t.status='Track ends — build a return loop';travel=0;break}
     t.turnPrev=t.from;t.turnNode=t.to;t.turnNext=next;t.turnProgress=0;t.phase='turn';}
   }
  }
  occupied=occupiedBy();
 }}

function resize(){let dpr=Math.min(2,devicePixelRatio||1);viewport.w=innerWidth;viewport.h=innerHeight;canvas.width=Math.floor(innerWidth*dpr);canvas.height=Math.floor(innerHeight*dpr);overlay.width=Math.floor(innerWidth*dpr);overlay.height=Math.floor(innerHeight*dpr);canvas.style.width=overlay.style.width=innerWidth+'px';canvas.style.height=overlay.style.height=innerHeight+'px';ctx.setTransform(dpr,0,0,dpr,0,0);gl.viewport(0,0,canvas.width,canvas.height)}
function zoomHeight(){return 29/camera.zoom}function scale(){return viewport.h/(2*zoomHeight())}
function project(x,y,z){let dx=x-camera.x,dz=z-camera.z,s=scale(),co=Math.cos(camera.yaw),si=Math.sin(camera.yaw),se=Math.sin(camera.elev),ce=Math.cos(camera.elev);return{x:viewport.w/2+(dx*co-dz*si)*s,y:viewport.h/2+((dx*si+dz*co)*se-y*ce)*s}}
function unproject(px,py){let s=scale(),a=(px-viewport.w/2)/s,b=(py-viewport.h/2)/(s*Math.sin(camera.elev)),co=Math.cos(camera.yaw),si=Math.sin(camera.yaw);return{x:camera.x+a*co+b*si,z:camera.z-a*si+b*co}}
function snap(p){return K(clamp(Math.round(p.x/CELL),0,WORLD_X-1),clamp(Math.round(p.z/CELL),0,WORLD_Z-1))}
function closestEdge(p){let winner=null,best=Infinity;for(let [a,set] of graph)for(let b of set){if(a>b)continue;let A=world(a),B=world(b),vx=B.x-A.x,vz=B.z-A.z,t=clamp(((p.x-A.x)*vx+(p.z-A.z)*vz)/(vx*vx+vz*vz),0,1),q={x:A.x+vx*t,z:A.z+vz*t},d=dist(p,q);if(d<best){best=d;winner={a,b,t,q,d}}}return winner}
function nearestTrain(p){let result=null,d=Infinity;for(let t of trains){let n=dist(p,head(t));if(n<d){d=n;result=t}}return d<3.1?result:null}
// Geometry construction: original low-poly 3D mesh primitives, all vertices are in world space.
class Mesh{
constructor(){this.pos=[];this.norm=[];this.colors=[];this.count=0}
tri(a,b,c,n,color){let co=Array.isArray(color)?color:rgb(color);this.pos.push(...a,...b,...c);for(let i=0;i<3;i++){this.norm.push(...n);this.colors.push(...co)}this.count+=3}
quad(a,b,c,d,n,col){this.tri(a,b,c,n,col);this.tri(a,c,d,n,col)}
box(x,y,z,w,h,l,angle,col){if(w<=0||h<=0||l<=0)return;let ca=Math.cos(angle),sa=Math.sin(angle);let p=(lx,ly,lz)=>[x+lx*ca+lz*sa,y+ly,z-lx*sa+lz*ca],vx=ca,vz=-sa,zx=sa,zz=ca;
let A=p(-w/2,-h/2,-l/2),B=p(w/2,-h/2,-l/2),Cc=p(w/2,-h/2,l/2),D=p(-w/2,-h/2,l/2),E=p(-w/2,h/2,-l/2),F=p(w/2,h/2,-l/2),G=p(w/2,h/2,l/2),H=p(-w/2,h/2,l/2);
this.quad(E,H,G,F,[0,1,0],col);this.quad(D,A,B,Cc,[0,-1,0],col);this.quad(D,Cc,G,H,[zx,0,zz],col);this.quad(B,A,E,F,[-zx,0,-zz],col);this.quad(A,D,H,E,[-vx,0,-vz],col);this.quad(Cc,B,F,G,[vx,0,vz],col)}
cylinder(x,y,z,r,h,col,segments=10){let c=rgb(col);for(let i=0;i<segments;i++){let a=i/segments*Math.PI*2,b=(i+1)/segments*Math.PI*2,ca=Math.cos(a),sa=Math.sin(a),cb=Math.cos(b),sb=Math.sin(b);let p=[x+r*ca,y-h/2,z+r*sa],q=[x+r*cb,y-h/2,z+r*sb],u=[x+r*ca,y+h/2,z+r*sa],v=[x+r*cb,y+h/2,z+r*sb],n=[(ca+cb)/2,0,(sa+sb)/2];this.quad(u,p,q,v,n,c);this.tri([x,y+h/2,z],u,v,[0,1,0],c)}}
cone(x,y,z,r,h,col,segments=9){let c=rgb(col);for(let i=0;i<segments;i++){let a=i/segments*Math.PI*2,b=(i+1)/segments*Math.PI*2;let p=[x+r*Math.cos(a),y-h/2,z+r*Math.sin(a)],q=[x+r*Math.cos(b),y-h/2,z+r*Math.sin(b)],peak=[x,y+h/2,z];let m=(a+b)/2;this.tri(p,q,peak,[Math.cos(m),r/h,Math.sin(m)],c)}}
// Quad flush with ground, with normal pointing upward.
flat(x,z,w,l,col,y=.012){this.quad([x-w/2,y,z-l/2],[x-w/2,y,z+l/2],[x+w/2,y,z+l/2],[x+w/2,y,z-l/2],[0,1,0],col)}
}
function oriented(m,x,y,z,w,h,l,angle,col){m.box(x,y,z,w,h,l,angle,col)}
// An extruded, continuous ribbon across the ENTIRE rail section instead of
// lots of overlapping rectangular boxes. Joins share their vertex positions,
// which prevents square joints, exposed ends and visible cracks on bends.
function trackRibbon(m,pts,offset,width,bottom,top,col,sideCol=col){
 if(pts.length<2)return;
 let edges=[];
 for(let i=0;i<pts.length;i++){
  let prev=pts[Math.max(0,i-1)],next=pts[Math.min(pts.length-1,i+1)],delta=unit(prev,next);
  let sx=delta.z,sz=-delta.x;
  // Shared frame at each sampling point produces smoothly rounded corners.
  let mid={x:pts[i].x+sx*offset,z:pts[i].z+sz*offset};
  edges.push({l:[mid.x-sx*width/2,top,mid.z-sz*width/2],r:[mid.x+sx*width/2,top,mid.z+sz*width/2],lb:[mid.x-sx*width/2,bottom,mid.z-sz*width/2],rb:[mid.x+sx*width/2,bottom,mid.z+sz*width/2],n:[sx,0,sz]});
 }
 for(let i=1;i<edges.length;i++){
  let a=edges[i-1],b=edges[i];
  m.quad(a.l,b.l,b.r,a.r,[0,1,0],col);
  m.quad(a.lb,a.l,b.l,b.lb,[-a.n[0],0,-a.n[2]],sideCol);
  m.quad(a.r,a.rb,b.rb,b.r,a.n,sideCol);
 }
}
function sweptRail(m,pts,bed=true){
 if(pts.length<2)return;
 if(bed)trackRibbon(m,pts,0,1.60,.02,.14,'#807d70','#615f54');
 // Sleepers are placed at even *travelled distances*, not one per short
 // subdivision; this keeps turnout sleepers looking consistent.
 let distance=0,nextTie=.20,spacing=.56;
 for(let i=1;i<pts.length;i++){
  const a=pts[i-1],b=pts[i],length=dist(a,b);
  if(length<1e-5)continue;
  while(nextTie<=distance+length+1e-6){
   let t=clamp((nextTie-distance)/length,0,1),x=mix(a.x,b.x,t),z=mix(a.z,b.z,t),ang=Math.atan2(b.x-a.x,b.z-a.z);
   m.box(x,.203,z,1.77,.125,.21,ang,'#70543d');
   nextTie+=spacing;
  }
  distance+=length;
 }
 // Steel rails: a dark foot, narrow web and a silver running surface.
 for(const side of [-1,1]){
  trackRibbon(m,pts,side*.445,.165,.265,.314,'#485050','#383f3f');
  trackRibbon(m,pts,side*.445,.085,.308,.414,'#596462','#444d4c');
  trackRibbon(m,pts,side*.445,.145,.402,.462,'#e8e3cc','#a8aea6');
 }
}
function segmentMesh(m,a,b){let [p,q]=edgeEnds(a,b),d=dist(p,q),count=Math.max(1,Math.ceil(d/.34));let pts=[];
 for(let i=0;i<=count;i++)pts.push({x:mix(p.x,q.x,i/count),z:mix(p.z,q.z,i/count)});sweptRail(m,pts)}
function junctionMesh(m,n){let nn=neighbors(n),p=world(n),distinct=new Set();
 if(nn.length<2)return;
 for(let i=0;i<nn.length;i++)for(let j=i+1;j<nn.length;j++){
  if(!bendAllowed(nn[i],n,nn[j]))continue;
  let pts=[];let length=curveLength(nn[i],n,nn[j]);let count=Math.max(4,Math.ceil(length/.18));
  for(let k=0;k<=count;k++)pts.push(curveAt(nn[i],n,nn[j],k/count));sweptRail(m,pts);
 }
 if(nn.length>=3){m.box(p.x+1.10,.20,p.z+.98,.68,.26,.62,0,'#806c47');m.box(p.x+1.10,.40,p.z+.98,.30,.14,.23,0,'#e8b95b');let chosen=pointExit(n);if(chosen){let out=port(n,chosen),dir=unit(p,out),theta=Math.atan2(dir.x,dir.z);m.box(p.x+dir.x*.42,.385,p.z+dir.z*.42,.14,.075,.64,theta,'#f1c577')}}
}
function hash(x){let s=Math.sin(x*18.263+4.928)*54831.82;return s-Math.floor(s)}
function hasRailNear(x,z){let p={x,z};let e=closestEdge(p);return e&&e.d<2.7}
function buildFactory(m,s){
 let p=world(s.node),ns=neighbors(s.node),v=ns.length?world(ns[0]):{x:p.x+2,z:p.z},ang=Math.atan2(v.x-p.x,v.z-p.z),px=p.x+Math.cos(ang)*1.43,pz=p.z-Math.sin(ang)*1.43;
 m.box(px,.20,pz,1.35,.32,4.55,ang,'#999687');m.box(px,.39,pz,1.32,.06,4.55,ang,'#e6c883');
 m.box(px,1.04,pz,.12,1.10,.13,ang,'#c9d9d2');m.box(px,1.62,pz,1.28,.24,.18,ang,s.siteId?'#648f7f':'#825f59');
}
function buildIndustry(m,site){
 let p=world(site.node),x=p.x,z=p.z,k=site.kind;
 m.box(x,.09,z,7.3,.14,7.3,0,'#858a7d');
 const color={timber:'#94745b',iron:'#788a8b',depot:'#bba578',freight:'#699494'}[k];
 m.box(x,.97,z,6.1,1.7,5.8,0,color);m.box(x,1.93,z,6.65,.24,6.4,0,'#4e5960');
 for(let i=-1;i<=1;i++)m.box(x+i*1.63,1.04,z+2.94,.95,.8,.07,0,'#c2dbd6');
 if(k==='timber')for(let i=0;i<7;i++)m.box(x-3+i,.41,z+4.35,.33,.38,2.25,0,'#bc8e56');
 if(k==='iron'){m.cylinder(x-1.65,3.05,z-1.4,.60,4.8,'#686a6a',12);m.cylinder(x+1.7,2.2,z-1.65,.36,3.1,'#565e65',10)}
 if(k==='depot'){m.box(x+2.5,1.3,z-3.6,1.4,2.6,1.4,0,'#8b9e98');m.box(x-2.1,.45,z-3.65,2.2,.9,1.5,0,'#d4bd86')}
 if(k==='freight')for(let i=0;i<4;i++)m.box(x-3+i*1.8,.7,z+4.5,1.4,1.25,1.2,0,i%2?'#b7ad8e':'#ae9e78');
}
let staticMesh=null,dynamicMesh=null,shader=null;
function buildStatic(){
 let m=new Mesh(),w=(WORLD_X-1)*CELL,h=(WORLD_Z-1)*CELL;
 m.box(w/2,-.45,h/2,w+CELL,.82,h+CELL,0,'#3c5846');m.box(w/2,-.025,h/2,w+CELL,.055,h+CELL,0,'#5e7e5b');
 for(let x=0;x<WORLD_X-4;x+=7)for(let z=0;z<WORLD_Z-4;z+=7){let n=hash(x*24+z*79),shade=n<.2?'#5b7b57':n<.5?'#587754':n<.75?'#5d805b':'#638360';m.flat((x+3.5)*CELL,(z+3.5)*CELL,CELL*6.9,CELL*6.9,shade,.011)}
 for(let d of DEPOSITS){let x=d.x*CELL,z=d.z*CELL;
  m.flat(x,z,d.r*CELL*1.3,d.r*CELL*1.3,d.kind==='iron'?'#60766d':'#467751',.019);
  for(let i=0;i<26;i++){
   let a=i*2.39996+hash(i+d.x)*.7,r=(.25+.65*hash(i*11+d.z))*d.r*CELL,px=x+Math.cos(a)*r,pz=z+Math.sin(a)*r;
   if(industries.some(s=>dist({x:px,z:pz},world(s.node))<6))continue;
   if(d.kind==='iron')m.cone(px,.42,pz,.65+hash(i)*.43,.9+hash(i*3)*.6,i%3?'#768d8d':'#93a69d',7);
   else{let scale=.72+hash(i*37+d.x)*.55;m.cylinder(px,.72*scale,pz,.17*scale,1.35*scale,'#554e3d',6);m.cone(px,2*scale,pz,.95*scale,2.5*scale,i%3?'#366746':'#4c8151',7)}
  }
 }
 for(let i=0;i<340;i++){
  let x=4+hash(i*31+11)*(w-8),z=4+hash(i*17+3)*(h-8);
  if(DEPOSITS.some(d=>dist({x,z},{x:d.x*CELL,z:d.z*CELL})<d.r*CELL*.9))continue;
  if(industries.some(s=>dist({x,z},world(s.node))<7)||hasRailNear(x,z))continue;
  let scale=.5+hash(i*53+7)*.7;m.cylinder(x,.60*scale,z,.16*scale,1.2*scale,'#625343',6);m.cone(x,1.85*scale,z,.88*scale,2.5*scale,'#47764a',7);
 }
 for(let [a,set] of graph)for(let b of set)if(a<b)segmentMesh(m,a,b);
 for(let [node,set] of graph)if(set.size>=2)junctionMesh(m,node);
 for(let s of stations)buildFactory(m,s);
 for(let site of industries)buildIndustry(m,site);
 return m;
}
function drawTrainMesh(m,t){let points=trainCars(t);let angle;let nose=head(t),tail=behind(t,.5);angle=Math.atan2(nose.x-tail.x,nose.z-tail.z);
const at=(pos, ang, ox,oy,oz)=>({x:pos.x+ox*Math.cos(ang)+oz*Math.sin(ang),y:oy,z:pos.z-ox*Math.sin(ang)+oz*Math.cos(ang)});
function boxAt(pos,ang,x,y,z,w,h,l,col){let p=at(pos,ang,x,y,z);m.box(p.x,p.y,p.z,w,h,l,ang,col)}
function car(pos,ang,idx){m.box(pos.x,.035,pos.z,1.8,.06,2.5,ang,'#415948');boxAt(pos,ang,0,.32,0,1.35,.22,2.18,'#30383e');for(let x of [-.68,.68])for(let z of [-.70,.70])boxAt(pos,ang,x,.29,z,.27,.33,.48,'#242c30');
if(idx===0){let col=t.color;boxAt(pos,ang,0,.56,0,1.38,.28,2.35,'#414a50');boxAt(pos,ang,0,.90,.55,1.23,.95,1.25,col);boxAt(pos,ang,0,1.13,-.52,1.18,1.25,1.00,col);boxAt(pos,ang,0,1.83,-.54,1.31,.20,1.18,'#3d474c');boxAt(pos,ang,-.62,1.22,-.53,.065,.53,.67,'#afd3d7');boxAt(pos,ang,.62,1.22,-.53,.065,.53,.67,'#afd3d7');boxAt(pos,ang,0,1.19,-1.04,.71,.57,.064,'#afd3d7');boxAt(pos,ang,-.43,.88,1.19,.18,.16,.05,'#f9deb0');boxAt(pos,ang,.43,.88,1.19,.18,.16,.05,'#f9deb0');boxAt(pos,ang,0,1.21,1.19,.72,.12,.05,'#f6c675');boxAt(pos,ang,0,.47,1.23,1.18,.28,.19,'#edb864');
let pipe=at(pos,ang,0,1.56,.72);m.cylinder(pipe.x,pipe.y,pipe.z,.19,.40,'#2e3538',10);
}else{boxAt(pos,ang,0,.53,0,1.27,.21,2.07,'#9b7750');boxAt(pos,ang,-.58,.91,0,.14,.74,2.06,t.cargo==='STEEL'?'#7a8080':'#90735a');boxAt(pos,ang,.58,.91,0,.14,.74,2.06,t.cargo==='STEEL'?'#7a8080':'#90735a');boxAt(pos,ang,0,.94,-.99,1.32,.75,.13,'#8f704f');boxAt(pos,ang,0,.94,.99,1.32,.75,.13,'#8f704f');
if(t.cargo==='TIMBER'){for(let j=-1;j<=1;j++)boxAt(pos,ang,j*.32,1.05,0,.25,.29,1.73,'#c59861')}
else if(t.cargo==='STEEL'){for(let j=-1;j<=1;j++)boxAt(pos,ang,0,1.12,j*.42,1.02,.26,.24,'#aebcb7')}
else{boxAt(pos,ang,-.24,1.12,-.1,.49,.44,.7,'#c6a276');boxAt(pos,ang,.29,1.12,.27,.45,.44,.57,'#a4b69c')}
}}
for(let i=0;i<points.length;i++){let p=points[i],ang;if(i===0)ang=angle;else{let front=points[i-1],back=behind(t,i*2.55+.3);ang=Math.atan2(front.x-back.x,front.z-back.z)}car(p,ang,i)}
}
const vs=`attribute vec3 aPos; attribute vec3 aNormal; attribute vec3 aColor; uniform mat4 uProj;uniform mat4 uView;varying vec3 vColor;void main(){gl_Position=uProj*uView*vec4(aPos,1.); vec3 n=normalize(aNormal);float lit=0.69+0.30*max(dot(n,normalize(vec3(-0.35,0.85,0.40))),0.0);vColor=aColor*lit;}`;
const fs=`precision mediump float;varying vec3 vColor;void main(){gl_FragColor=vec4(vColor,1.0);}`;
function compile(type,src){let s=gl.createShader(type);gl.shaderSource(s,src);gl.compileShader(s);if(!gl.getShaderParameter(s,gl.COMPILE_STATUS))throw Error(gl.getShaderInfoLog(s));return s}
function initGL(){let program=gl.createProgram();gl.attachShader(program,compile(gl.VERTEX_SHADER,vs));gl.attachShader(program,compile(gl.FRAGMENT_SHADER,fs));gl.linkProgram(program);if(!gl.getProgramParameter(program,gl.LINK_STATUS))throw Error(gl.getProgramInfoLog(program));gl.useProgram(program);shader={program,proj:gl.getUniformLocation(program,'uProj'),view:gl.getUniformLocation(program,'uView'),pos:gl.getAttribLocation(program,'aPos'),norm:gl.getAttribLocation(program,'aNormal'),col:gl.getAttribLocation(program,'aColor')};gl.clearColor(.31,.44,.37,1);gl.enable(gl.DEPTH_TEST);gl.depthFunc(gl.LEQUAL);gl.disable(gl.CULL_FACE)}
function upload(mesh,old,usage){let b=old||{p:gl.createBuffer(),n:gl.createBuffer(),c:gl.createBuffer()};for(let [name,data] of [['p',mesh.pos],['n',mesh.norm],['c',mesh.colors]]){gl.bindBuffer(gl.ARRAY_BUFFER,b[name]);gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(data),usage)}b.count=mesh.count;return b}
function draw(b){if(!b||!b.count)return;for(let [buf,loc] of [[b.p,shader.pos],[b.n,shader.norm],[b.c,shader.col]]){gl.bindBuffer(gl.ARRAY_BUFFER,buf);gl.enableVertexAttribArray(loc);gl.vertexAttribPointer(loc,3,gl.FLOAT,false,0,0)}gl.drawArrays(gl.TRIANGLES,0,b.count)}
function viewMat(){let ex=camera.x+Math.sin(camera.yaw)*Math.cos(camera.elev)*105,ez=camera.z+Math.cos(camera.yaw)*Math.cos(camera.elev)*105,ey=Math.sin(camera.elev)*105;let eye=[ex,ey,ez],focus=[camera.x,0,camera.z];let norm=v=>{let d=Math.hypot(...v);return v.map(x=>x/d)},cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],dot=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2];let z=norm(eye.map((v,i)=>v-focus[i])),x=norm(cross([0,1,0],z)),y=cross(z,x);return new Float32Array([x[0],y[0],z[0],0,x[1],y[1],z[1],0,x[2],y[2],z[2],0,-dot(x,eye),-dot(y,eye),-dot(z,eye),1])}
function projMat(){let hh=zoomHeight(),hw=hh*viewport.w/viewport.h,n=.1,f=500;return new Float32Array([1/hw,0,0,0,0,1/hh,0,0,0,0,-2/(f-n),0,0,0,-(f+n)/(f-n),1])}
function drawSignalsMesh(m){let occ=occupiedBy();for(let s of signals){if(!graph.get(s.a)?.has(s.b))continue;let A=world(s.a),B=world(s.b),vx=B.x-A.x,vz=B.z-A.z,l=Math.hypot(vx,vz),along=.27,side=s.type==='chain'?-.67:.67;
let x=A.x+vx*along+vz/l*side,z=A.z+vz*along-vx/l*side,good=signalStatus(s)==='green';
m.box(x,.65,z,.14,1.24,.14,0,'#303b41');m.box(x,1.35,z,.42,.58,.28,0,s.type==='chain'?'#315d71':'#41484d');m.box(x,1.47,z+.17,.26,.25,.10,0,good?'#61dba2':'#f06c63');m.box(x,.12,z,.53,.13,.53,0,'#777f78');
if(s.type==='chain')m.box(x,1.17,z+.17,.20,.10,.10,0,'#79bddb')
}}
function render3D(){if(dirty){staticMesh=upload(buildStatic(),staticMesh,gl.STATIC_DRAW);dirty=false;updateStats()};let m=new Mesh();drawSignalsMesh(m);for(let t of trains)drawTrainMesh(m,t);dynamicMesh=upload(m,dynamicMesh,gl.DYNAMIC_DRAW);gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);gl.useProgram(shader.program);gl.uniformMatrix4fv(shader.proj,false,projMat());gl.uniformMatrix4fv(shader.view,false,viewMat());draw(staticMesh);draw(dynamicMesh)}
function labels(){
 const root=$('#labels'),list=[...stations.map(s=>({...s,label:s.name})),...industries.map(s=>({...s,label:s.name}))];
 const key=list.map(s=>s.id+':'+s.label).join('|');
 if(root.dataset.key!==key){root.dataset.key=key;root.textContent='';for(let s of list){let l=document.createElement('div');l.className='station-tag';l.textContent=s.label;l.dataset.id=s.id;root.appendChild(l)}}
 for(let el of root.children){let s=list.find(s=>s.id===el.dataset.id);if(!s)continue;let p=world(s.node),q=project(p.x,s.id[0]==='i'?3.45:1.8,p.z);el.style.left=q.x+'px';el.style.top=q.y+'px';el.style.display=q.x<-20||q.x>viewport.w+20||q.y<-20||q.y>viewport.h+20?'none':'block'}
}
function drawGhostPath(nodes){
 if(!nodes||nodes.length<2)return;
 ctx.save();ctx.beginPath();let start=world(nodes[0]),q=project(start.x,.62,start.z);ctx.moveTo(q.x,q.y);
 for(let i=0;i<nodes.length-1;i++){
  let a=nodes[i],b=nodes[i+1],p1=port(a,b),p2=port(b,a),s=project(p1.x,.62,p1.z),t=project(p2.x,.62,p2.z);
  ctx.lineTo(s.x,s.y);ctx.lineTo(t.x,t.y);
  if(i<nodes.length-2){for(let k=1;k<=9;k++){let w=curveAt(a,b,nodes[i+2],k/9),v=project(w.x,.62,w.z);ctx.lineTo(v.x,v.y)}}
 }
 ctx.strokeStyle='#b5edce';ctx.lineWidth=5;ctx.globalAlpha=.94;ctx.setLineDash([9,5]);ctx.stroke();ctx.restore();
 let last=world(nodes.at(-1)),v=project(last.x,.68,last.z);ctx.fillStyle='#b5edce';ctx.beginPath();ctx.arc(v.x,v.y,6,0,Math.PI*2);ctx.fill();
}
function overlayDraw(){ctx.clearRect(0,0,viewport.w,viewport.h);
 if(showGrid){ctx.save();ctx.strokeStyle='#c8d3bc';ctx.globalAlpha=.14;ctx.lineWidth=1;
  const range=24,ix=Math.round(camera.x/CELL),iz=Math.round(camera.z/CELL);
  for(let x=Math.max(0,ix-range);x<=Math.min(WORLD_X-1,ix+range);x++){
   let a=project(x*CELL,.055,Math.max(0,iz-range)*CELL),b=project(x*CELL,.055,Math.min(WORLD_Z-1,iz+range)*CELL);ctx.beginPath();ctx.moveTo(a.x,a.y);ctx.lineTo(b.x,b.y);ctx.stroke()}
  for(let z=Math.max(0,iz-range);z<=Math.min(WORLD_Z-1,iz+range);z++){
   let a=project(Math.max(0,ix-range)*CELL,.055,z*CELL),b=project(Math.min(WORLD_X-1,ix+range)*CELL,.055,z*CELL);ctx.beginPath();ctx.moveTo(a.x,a.y);ctx.lineTo(b.x,b.y);ctx.stroke()}
  ctx.restore();
 }
 if(mode==='rail'&&anchor&&hover&&hover!==anchor){let key=anchor+'>'+hover+'@'+anchorFrom;
  if(key!==previewKey){previewKey=key;previewNodes=planRail(anchor,hover,anchorFrom);if(!routeCanBuild(previewNodes))previewNodes=null}
  drawGhostPath(previewNodes);
 }
 if(mode==='rail'&&!anchor&&hover){let [x,z]=parseKey(hover),[dx,dz]=DIRS[railHeading],next=K(x+dx,z+dz);
  if(graph.has(hover)){let p=world(hover),a=project(p.x,.75,p.z);ctx.fillStyle='#aef7b6';ctx.font='bold 11px system-ui';ctx.fillText('▶ Click to extend rail here',a.x-40,a.y-22);
    for(let n of neighbors(hover)){let q=world(n),dx=p.x-q.x,dz=p.z-q.z,l=Math.hypot(dx,dz),b=project(p.x+dx/l*1.4,.63,p.z+dz/l*1.4);ctx.fillStyle='#aaf5c5';ctx.beginPath();ctx.moveTo(b.x,b.y-6);ctx.lineTo(b.x+6,b.y+5);ctx.lineTo(b.x-6,b.y+5);ctx.fill()}}
  else if(keyValid(next))drawGhostPath([hover,next]);
 }
 if(hover&&mode!=='select'){let p=world(hover),q=project(p.x,.22,p.z);ctx.beginPath();ctx.arc(q.x,q.y,7,0,Math.PI*2);ctx.strokeStyle='#ffe09b';ctx.lineWidth=2;ctx.stroke()}
 if(mode==='rail'&&anchor){let A=world(anchor),p=project(A.x,.70,A.z);ctx.fillStyle='#ffce74';ctx.beginPath();ctx.arc(p.x,p.y,7,0,Math.PI*2);ctx.fill()}
 if(['timber','iron','depot','freight'].includes(mode)&&hover){let p=world(hover),v=project(p.x,1,p.z),valid=industryCanPlace(mode,hover);
  ctx.save();ctx.strokeStyle=valid?'#94e4b4':'#fd9d8b';ctx.fillStyle=valid?'#b5efca36':'#fb8d8244';ctx.lineWidth=3;
  let polygon=[[-3.8,-3.8],[3.8,-3.8],[3.8,3.8],[-3.8,3.8]];ctx.beginPath();for(let i=0;i<polygon.length;i++){let [x,z]=polygon[i],pt=project(p.x+x,.15,p.z+z);i?ctx.lineTo(pt.x,pt.y):ctx.moveTo(pt.x,pt.y)}ctx.closePath();ctx.fill();ctx.stroke();ctx.fillStyle=valid?'#c1f5cd':'#ffc4b5';ctx.font='bold 12px system-ui';ctx.textAlign='center';ctx.fillText(valid?'Click to construct':'Requires matching resource / clear space',v.x,v.y-18);ctx.restore();
 }
 if(showBlocks){for(let block of blocks){ctx.save();ctx.strokeStyle=['#89d3ee','#eec981','#bd9def','#eab1b0','#a6db8b'][block.id%5];ctx.globalAlpha=.55;ctx.lineWidth=4;ctx.beginPath();for(let e of block.edges){let [a,b]=e.split('|'),A=world(a),B=world(b),u=project(A.x,.5,A.z),v=project(B.x,.5,B.z);ctx.moveTo(u.x,u.y);ctx.lineTo(v.x,v.y)}ctx.stroke();ctx.restore()}}
 if(['block','chain'].includes(mode)&&hover){let e=closestEdge(unproject(mouse.x,mouse.y));if(e&&e.d<1.25){let a=world(e.a),b=world(e.b),q=project(mix(a.x,b.x,.27),1.2,mix(a.z,b.z,.27));ctx.fillStyle='#fff0c3';ctx.font='bold 12px system-ui';ctx.fillText('Click to install '+mode+' signal',q.x-58,q.y-14)}}
 for(let t of trains){let p=head(t),q=project(p.x,2.65,p.z);if(t.id===selectedTrainId){ctx.fillStyle='#fff0ca';ctx.textAlign='center';ctx.font='bold 12px system-ui';ctx.fillText('◆ '+t.name,q.x,q.y-3)}}
}
function industryCanPlace(kind,node){
 if(!keyValid(node)||industries.some(s=>dist(world(s.node),world(node))<9))return false;
 if((kind==='timber'||kind==='iron')&&!depositNear(node,kind))return false;
 return ![...graph.keys()].some(k=>dist(world(k),world(node))<4.5);
}
function drawMini(){let mini=$('#minimap'),c=mini.getContext('2d'),sx=mini.width/((WORLD_X)*CELL),sz=mini.height/((WORLD_Z)*CELL);c.fillStyle='#3e6049';c.fillRect(0,0,mini.width,mini.height);for(let i=0;i<100;i++){c.fillStyle=i%2?'#41644b':'#4a6b4e';let x=hash(i*11)*mini.width,z=hash(i*42)*mini.height;c.fillRect(x,z,3,3)}for(let d of DEPOSITS){c.fillStyle=d.kind==='iron'?'#87a4ac':'#4f9065';c.beginPath();c.arc(d.x*CELL*sx,d.z*CELL*sz,Math.max(2,d.r*CELL*sx*.45),0,Math.PI*2);c.fill()}for(let s of industries){let p=world(s.node);c.fillStyle=s.kind==='depot'?'#f2c674':s.kind==='freight'?'#a3e6d7':'#f6edd8';c.fillRect(p.x*sx-3,p.z*sz-3,6,6)}c.strokeStyle='#d1baa0';c.lineWidth=3;c.beginPath();for(let [a,set] of graph)for(let b of set)if(a<b){let A=world(a),B=world(b);c.moveTo(A.x*sx,A.z*sz);c.lineTo(B.x*sx,B.z*sz)}c.stroke();for(let s of signals){let A=world(s.a),B=world(s.b),x=mix(A.x,B.x,.27)*sx,z=mix(A.z,B.z,.27)*sz;c.beginPath();c.arc(x,z,2.2,0,6.283);c.fillStyle=signalStatus(s)==='green'?'#68e6ad':'#f37163';c.fill()}c.fillStyle='#e2a45f';for(let s of stations){let p=world(s.node);c.fillRect(p.x*sx-3,p.z*sz-3,6,6)}for(let t of trains){let p=head(t);c.beginPath();c.arc(p.x*sx,p.z*sz,3.8,0,6.283);c.fillStyle=t.id===selectedTrainId?'#fff5ba':'#e15a55';c.fill()}
let scaleX=mini.width/(WORLD_X*CELL),scaleZ=mini.height/(WORLD_Z*CELL),corner=[unproject(0,0),unproject(viewport.w,0),unproject(viewport.w,viewport.h),unproject(0,viewport.h)];c.beginPath();corner.forEach((p,i)=>i?c.lineTo(p.x*scaleX,p.z*scaleZ):c.moveTo(p.x*scaleX,p.z*scaleZ));c.closePath();c.strokeStyle='#b7e9cb';c.lineWidth=1.2;c.stroke()}
function updateStats(){let c=0;for(let [a,set] of graph)for(let b of set)if(a<b)c++;$('#trackcount').textContent=c;$('#traincount').textContent=trains.length;let n=$('#signalcount');if(n)n.textContent=signals.length;let b=$('#blockcount');if(b)b.textContent=blocks.length}
function announce(s){$('#hinttext').textContent=s;$('#notice').textContent=s;$('#notice').style.opacity='1';noticeExpiry=performance.now()+3300}
function setMode(m,silent=false){mode=m;anchor=null;anchorFrom=null;previewNodes=null;previewKey='';$all('.tool').forEach(b=>b.classList.toggle('active',b.dataset.mode===m));let helps={timber:'Click within a GREEN FOREST to build a logging camp. Place a station on rail nearby.',iron:'Click within a GREY-BLUE ORE deposit to place an ore mine.',depot:'Build machine works on clear land. It consumes shipped timber and steel.',freight:'Build a distribution hub on clear land to receive machinery.',rail:'Click open ground to place the first rail; then move and click to extend. Click an existing track connector to branch. R again rotates the first piece; right-click or Escape ends the planner.',junction:'Click a turnout (3+ rail connections) to cycle its manual preferred direction. Trains with destinations automatically line up points.',block:'Click rail to place a BLOCK signal: protects the next occupied track block. Press F to reverse signal direction.',chain:'Click rail to place a CHAIN signal: reserves a path through a junction until the next exit. Press F to flip direction.',select:'Click a locomotive in the world to manage its route, carriages, speed and orders.',station:'Build a station on connected rail near a logging camp, mine, factory or distributor.',train:'Click any connected track node to place a new locomotive and wagon.',delete:'Click close to a rail segment or station to remove it. The trains will react if their line breaks.'};$('#toolhelp').textContent=helps[m];if(!silent)announce(helps[m])}
function routePresetFor(t){let kinds=t.schedule?.map(id=>stationById(id)?.kind)||[];if(kinds.join(',')==='timber,depot'&&t.freightType==='timber')return'timber';if(kinds.join(',')==='iron,depot'&&t.freightType==='steel')return'steel';if(kinds.join(',')==='depot,freight'&&t.freightType==='machinery')return'machinery';if(kinds.length===stations.length&&kinds.every((v,i)=>stations[i]?.kind===v))return'all';return'keep'}
function updateUI(){let t=trains.find(t=>t.id===selectedTrainId),root=$('#traincontent');if(!t){root.innerHTML=`<div class="sectionlabel">LOCOMOTIVE CONTROL</div><div class="no-train">No train selected. Choose <b>Select train</b> and click a locomotive, or place a new train onto the rail network.</div>`;return}
root.innerHTML=`<div class="panel-heading"><span class="eyebrow">LOCOMOTIVE CONTROL</span><span class="countbadge">TRAIN #${String(t.id).padStart(2,'0')}</span></div><div class="trainname">${t.name}</div><div class="trainillustration">🚂 <span style="font-size:27px;opacity:.8">🚃🚃</span></div><div class="metricrow"><div class="metric"><span>Speed</span><strong id="speedvalue">0 km/h</strong></div><div class="metric"><span>Status</span><strong id="statusvalue" style="font-size:12px">Running</strong></div></div><label class="fieldlabel" for="stationselect">NEXT DESTINATION</label><select id="stationselect">${stations.map(s=>`<option value="${s.id}" ${s.id===t.target?'selected':''}>${s.name.replaceAll('<','&lt;')}</option>`).join('')}</select><div class="btnrow"><button id="btnSend" class="actionbtn">→ Dispatch train</button><button id="btnHold" class="actionbtn secondary">${t.halted?'▶ Resume':'Ⅱ Stop'}</button></div><div class="controlrow"><span>Automatic station schedule</span><input class="switch" id="autoSchedule" type="checkbox" ${t.auto?'checked':''}></div><div class="controlrow"><span>Obey manual switch points</span><input class="switch" id="manualPoints" type="checkbox" ${t.manualPoints?'checked':''}></div><label class="fieldlabel">CRUISING SPEED <span id="speedcap">${Math.round(t.speedCap*12)} km/h</span></label><input id="trainSpeed" type="range" min="1" max="8" step="0.2" value="${t.speedCap}"><div class="controlrow"><span>Wagons attached</span><span><button class="smallbtn" id="removeWagon" style="padding:4px 10px">−</button> <b id="wagoncount">${t.cars}</b> <button class="smallbtn" id="addWagon" style="padding:4px 10px">+</button></span></div><label class="fieldlabel" for="routePreset">AUTOMATIC ROUTE</label><select id="routePreset"><option value="keep" ${routePresetFor(t)==='keep'?'selected':''}>Custom route / current order</option><option value="timber" ${routePresetFor(t)==='timber'?'selected':''}>🌲 Timber Mill ↔ Central Depot</option><option value="steel" ${routePresetFor(t)==='steel'?'selected':''}>⚙ Ironworks ↔ Central Depot</option><option value="machinery" ${routePresetFor(t)==='machinery'?'selected':''}>📦 Central Depot ↔ Distribution</option><option value="all" ${routePresetFor(t)==='all'?'selected':''}>↻ Visit every station</option></select><label class="fieldlabel" for="freightType">FREIGHT ORDER · EACH WAGON HOLDS 14 UNITS</label><select id="freightType">${Object.entries(GOODS).map(([id,good])=>`<option value="${id}" ${t.freightType===id?'selected':''}>${good.icon} ${good.label}</option>`).join('')}</select><div class="trainhint"><span style="color:#edba70">◉</span> Load: <b id="cargoValue">${t.load||0} ${GOODS[t.loadGood||'timber'].label}</b><br>Stops automatically load cargo at producers and unload at industries that need it. Select matching source and destination stations.</div>`;
$('#routePreset').onchange=e=>{let v=e.target.value,kind=v==='steel'?'steel':v==='machinery'?'machinery':'timber';let stops=v==='all'?stations.map(s=>s.id):v==='keep'?t.schedule:([v==='steel'?'iron':v==='machinery'?'depot':'timber',v==='machinery'?'freight':'depot'].map(k=>stations.find(s=>s.kind===k)?.id).filter(Boolean));if(stops.length<2){announce('This route needs two stations.');return}t.schedule=stops;t.freightType=kind;t.target=stops[0];t.stopIndex=0;t.nextTarget=null;t.auto=true;t.halted=false;t.dwell=0;if(t.progress===0){let next=bestNext(t,t.from);if(next)t.to=next;}announce(`${t.name}: ${GOODS[kind].label} route activated.`);updateUI()};$('#freightType').onchange=e=>{t.freightType=e.target.value;t.cargo=t.load>0?t.loadGood.toUpperCase():'EMPTY';announce('Assigned '+GOODS[t.freightType].label+' freight to '+t.name);updateUI()};$('#btnSend').onclick=()=>{let newtarget=$('#stationselect').value;let st=stationById(newtarget);if(!st)return;t.target=newtarget;t.nextTarget=null;t.dwell=0;t.halted=false;t.auto=false;t.status='Dispatched';if(t.progress===0){let departure=bestNext(t,t.from);if(departure)t.to=departure;}announce(`${t.name} dispatched to ${st.name}`);updateUI()};$('#btnHold').onclick=()=>{t.halted=!t.halted;announce(t.halted?`${t.name}: emergency hold`:`${t.name}: resuming service`);updateUI()};$('#manualPoints').onchange=e=>{t.manualPoints=e.target.checked;announce(t.manualPoints?'Manual points override enabled for this train':'Automatic junction routing restored')};$('#autoSchedule').onchange=e=>{t.auto=e.target.checked;if(t.auto){if(!t.schedule?.length)t.schedule=stations.map(s=>s.id);t.nextTarget=null}announce(t.auto?'Automatic timetable enabled':'Manual dispatch enabled')};$('#trainSpeed').oninput=e=>{t.speedCap=+e.target.value;$('#speedcap').textContent=Math.round(t.speedCap*12)+' km/h'};$('#addWagon').onclick=()=>{t.cars=Math.min(5,t.cars+1);$('#wagoncount').textContent=t.cars;updateUI()};$('#removeWagon').onclick=()=>{t.cars=Math.max(0,t.cars-1);$('#wagoncount').textContent=t.cars;updateUI()}}
function updateTrainUI(){let t=trains.find(t=>t.id===selectedTrainId);if(!t)return;let speed=$('#speedvalue');if(speed){speed.textContent=Math.round(t.speed*12)+' km/h';$('#statusvalue').textContent=t.status;$('#cargoValue').textContent=(t.load||0)+' '+GOODS[t.loadGood||'timber'].label}}
function clickWorld(px,py){let p=unproject(px,py),node=snap(p),nodePos=world(node);
if(mode==='rail'){
 if(!anchor){
  if(graph.has(node)){
   anchor=node;let ns=neighbors(node),aim=unproject(mouse.x,mouse.y);
   ns.sort((aa,bb)=>{let p=world(node),a=world(aa),b=world(bb);return (a.x-p.x)*(aim.x-p.x)+(a.z-p.z)*(aim.z-p.z)-((b.x-p.x)*(aim.x-p.x)+(b.z-p.z)*(aim.z-p.z))});
   anchorFrom=ns[0]||null;announce('Rail connector selected. Aim and click to extend or branch.');
  }else{
   let [x,z]=parseKey(node),[dx,dz]=DIRS[railHeading],next=K(x+dx,z+dz);
   if(!keyValid(next)){announce('Rail starts must be inside the map.');return}
   if(!routeCanBuild([node,next])){announce('A building blocks this rail section.');return}
   link(node,next);lastBuild=[[node,next]];recomputeBlocks();anchor=next;anchorFrom=node;
   announce('Starting rail laid! Move the cursor to preview bends, then click to build.');
  }
  previewNodes=null;previewKey='';
 }else if(node===anchor){anchor=null;anchorFrom=null;previewNodes=null;announce('Rail planner ended.')}
 else{
  let result=layPlanned(anchor,node,anchorFrom);
  if(result.route){anchorFrom=result.route.at(-2);anchor=result.route.at(-1);previewNodes=null;previewKey='';announce(result.added?'Built '+result.added+' rail sections. Continue extending.':'Connected track selected.');}
  else announce('No suitable route: try a wider curve or another approach.');
 }
}
else if(['timber','iron','depot','freight'].includes(mode)){
 if(!industryCanPlace(mode,node)){announce('Building needs the correct resource deposit and enough clear ground.');return}
 let site=addIndustry(mode,node);
 if(site){bank=Math.max(0,bank-160);updateIndustryUI();announce(site.name+' built. Connect it to your railway using a nearby station.');}
}
else if(mode==='junction'){if(!turnPoint(node))announce('A junction needs at least three tracks meeting at one point. Build a branch first.')}
else if(mode==='block'||mode==='chain'){let e=closestEdge(p);if(!e||e.d>1.20){announce('Click directly on a rail to attach a signal.');return}let closer=dist(p,world(e.a))<=dist(p,world(e.b))?e.a:e.b;let a=signalReverse?(closer===e.a?e.b:e.a):closer,b=a===e.a?e.b:e.a;placeSignal(a,b,mode==='block'?'rail':'chain')}
else if(mode==='station'){if(dist(p,nodePos)>1.65||!graph.has(node)){announce('Stations must sit on an existing track node.');return}let old=stations.find(s=>s.node===node);if(old){announce('A station is already at that track node.');return}let s=addStation('Rail Station '+nextStation,node,'unassigned');for(let t of trains){t.schedule.push(s.id)}dirty=true;updateUI();announce(`${s.name} built — trains can now be sent here.`)}
else if(mode==='train'){if(!graph.has(node)){announce('Place locomotives on connected track.');return}let neighborsHere=neighbors(node);if(!neighborsHere.length)return;let closest=nearestTrain(nodePos);if(closest&&dist(head(closest),nodePos)<2.5){announce('Choose an empty track section for the new locomotive.');return}let t=createTrain(node,neighborsHere[0]);t.past=seedPast(node,neighborsHere[0]);updateUI();announce(`${t.name} placed. Set its destination or use automatic schedule.`)}
else if(mode==='select'){let t=nearestTrain(p);if(t){selectedTrainId=t.id;updateUI();announce(`${t.name} selected — use the control panel to manage it.`)}else{let st=stations.find(s=>dist(p,world(s.node))<1.5);if(st)announce(`${st.name} — send trains here from the train controls.`)}}
else if(mode==='delete'){let site=industries.find(s=>dist(p,world(s.node))<4.7);if(site){industries=industries.filter(s=>s!==site);dirty=true;updateIndustryUI();announce(site.name+' demolished.');return}let sig=signals.find(s=>{let a=world(s.a),b=world(s.b),pos={x:mix(a.x,b.x,.27),z:mix(a.z,b.z,.27)};return dist(p,pos)<.65});if(sig){signals=signals.filter(s=>s!==sig);recomputeBlocks();dirty=true;announce('Signal demolished.');return}let s=stations.find(s=>dist(p,world(s.node))<1.35);if(s){stations=stations.filter(t=>t!==s);trains.forEach(t=>{t.schedule=t.schedule.filter(id=>id!==s.id);if(t.target===s.id){t.target=t.schedule[0]||null}if(t.nextTarget===s.id)t.nextTarget=null});dirty=true;updateUI();announce('Station removed.');return}let e=closestEdge(p);if(e&&e.d<1.08){removeEdge(e.a,e.b);announce('Track removed. Trains will stop if their route is interrupted.')}else announce('Click closer to the track to demolish it.')}
}
function panFromPointer(dx,dy){
 let a=unproject(viewport.w/2,viewport.h/2),b=unproject(viewport.w/2+dx,viewport.h/2+dy);
 camera.x+=a.x-b.x;camera.z+=a.z-b.z;
}
function tickCamera(dt){
 const dtc=Math.min(dt,.06);
 if(heldKeys.has('q'))viewTarget.yaw-=dtc*1.75;
 if(heldKeys.has('e'))viewTarget.yaw+=dtc*1.75;
 // Screen-oriented pan, so WASD never feels backward after rotating the view.
 const right=(heldKeys.has('d')||heldKeys.has('arrowright')?1:0)-(heldKeys.has('a')||heldKeys.has('arrowleft')?1:0);
 const down=(heldKeys.has('arrowdown')?1:0)-(heldKeys.has('w')||heldKeys.has('arrowup')?1:0);
 if(right||down){const panSpeed=23/camera.zoom,co=Math.cos(camera.yaw),si=Math.sin(camera.yaw),step=dtc*panSpeed;
  camera.x+=(right*co+down*si)*step;camera.z+=(-right*si+down*co)*step;}
 const factor=1-Math.exp(-dtc*13);
 // shortest angular interpolation, also handles crossing the +/-pi boundary.
 const delta=Math.atan2(Math.sin(viewTarget.yaw-camera.yaw),Math.cos(viewTarget.yaw-camera.yaw));
 camera.yaw+=delta*factor;camera.elev+=(viewTarget.elev-camera.elev)*factor;
}
canvas.addEventListener('contextmenu',e=>e.preventDefault());
canvas.addEventListener('pointerdown',e=>{
 mouse.down=true;mouse.dragging=false;mouse.button=e.button;mouse.pan=e.button===1||(e.button===2&&e.shiftKey);
 mouse.lastX=e.clientX;mouse.lastY=e.clientY;mouse.downX=e.clientX;mouse.downY=e.clientY;
 canvas.setPointerCapture(e.pointerId);
});
canvas.addEventListener('pointermove',e=>{
 mouse.x=e.clientX;mouse.y=e.clientY;
 if(mouse.down){let dx=e.clientX-mouse.lastX,dy=e.clientY-mouse.lastY;
  if(Math.hypot(e.clientX-mouse.downX,e.clientY-mouse.downY)>3)mouse.dragging=true;
  if(mouse.button===2&&!mouse.pan){viewTarget.yaw-=dx*.009;viewTarget.elev=clamp(viewTarget.elev-dy*.006,.40,1.47)}
  else if(mouse.pan)panFromPointer(dx,dy);
 }
 hover=snap(unproject(e.clientX,e.clientY));
 mouse.lastX=e.clientX;mouse.lastY=e.clientY;
});
canvas.addEventListener('pointerup',e=>{if(mouse.down&&mouse.button===0&&!mouse.dragging)clickWorld(e.clientX,e.clientY);else if(mouse.down&&mouse.button===2&&!mouse.dragging&&mode==='rail'){anchor=null;anchorFrom=null;previewNodes=null;previewKey='';announce('Rail planner cancelled.')}mouse.down=false;mouse.dragging=false});
canvas.addEventListener('pointercancel',()=>{mouse.down=false;mouse.dragging=false});
window.addEventListener('blur',()=>heldKeys.clear());
$('#minimap').addEventListener('pointerdown',e=>{let r=e.currentTarget.getBoundingClientRect();camera.x=clamp((e.clientX-r.left)/r.width*WORLD_X*CELL,0,(WORLD_X-1)*CELL);camera.z=clamp((e.clientY-r.top)/r.height*WORLD_Z*CELL,0,(WORLD_Z-1)*CELL)});
canvas.addEventListener('wheel',e=>{e.preventDefault();let old=unproject(e.clientX,e.clientY);camera.zoom=clamp(camera.zoom*Math.exp(-e.deltaY*.0011),.48,3.4);let now=unproject(e.clientX,e.clientY);camera.x+=old.x-now.x;camera.z+=old.z-now.z},{passive:false});
window.addEventListener('keyup',e=>heldKeys.delete(e.key.toLowerCase()));
window.addEventListener('keydown',e=>{
 if(['INPUT','TEXTAREA','SELECT'].includes(e.target?.tagName))return;
 let k=e.key.toLowerCase();
 if(['q','e','w','a','d','arrowup','arrowdown','arrowleft','arrowright'].includes(k)){heldKeys.add(k);if(k.startsWith('arrow')||['q','e'].includes(k))e.preventDefault();}
 // Keep S as the station shortcut on the initial press, but holding S pans.
 if(e.repeat)return;
 if(k==='1')setMode('timber');else if(k==='2')setMode('iron');else if(k==='3')setMode('depot');else if(k==='4')setMode('freight');else if(k==='r'){if(mode==='rail'&&!anchor){railHeading=(railHeading+1)%8;announce('Starting rail rotated 45 degrees.')}else setMode('rail');}else if(k==='v')setMode('select');else if(k==='s')setMode('station');else if(k==='t')setMode('train');else if(k==='x')setMode('delete');else if(k==='j')setMode('junction');else if(k==='b')setMode('block');else if(k==='c')setMode('chain');else if(k==='f'){signalReverse=!signalReverse;announce('Signal orientation '+(signalReverse?'reversed':'normal'));}else if(k==='h'){showBlocks=!showBlocks;announce('Block boundary overlay '+(showBlocks?'enabled':'disabled'))}else if((e.altKey&&k==='z')||(e.ctrlKey&&k==='z')){e.preventDefault();if(lastBuild.length){for(let [a,b] of lastBuild)removeEdge(a,b);lastBuild=[];announce('Last track construction undone.')}else announce('Nothing to undo.')}else if(k==='g'){showGrid=!showGrid;dirty=true}else if(k==='escape'){anchor=null;anchorFrom=null;previewNodes=null;$('#help').classList.remove('show');announce('Action cancelled.')}else if(e.code==='Space'){paused=!paused;announce(paused?'Simulation paused':'Simulation resumed');e.preventDefault()}
});
$all('.tool').forEach(b=>b.onclick=()=>setMode(b.dataset.mode));$('#btnRotateLeft').onclick=()=>viewTarget.yaw-=Math.PI/8;
$('#btnRotateRight').onclick=()=>viewTarget.yaw+=Math.PI/8;
$('#btnResetView').onclick=()=>{camera.x=90*CELL;camera.z=70*CELL;camera.zoom=.94;viewTarget.yaw=-.77;viewTarget.elev=.94;announce('Camera recentered and orientation reset.')};$('#btnHelp').onclick=()=>$('#help').classList.add('show');$('#btnCloseHelp').onclick=()=>$('#help').classList.remove('show');
function snapshot(){let state={version:5,edges:[],stations,industries,trains,signals,points:[...points.entries()],nextTrain,nextStation,nextSignal,nextIndustry,bank,delivered};for(let [a,links] of graph)for(let b of links)if(a<b)state.edges.push([a,b]);return state}
function save(){try{localStorage.setItem(STORAGE,JSON.stringify(snapshot()));announce('Railway saved in this browser.')}catch(e){announce('Browser storage unavailable — use Export instead.')}}
function loadState(s){if(!s||!Array.isArray(s.edges)||!Array.isArray(s.trains)||!Array.isArray(s.stations))return false;
// Reject malformed imported rail endpoints and out-of-map data.
if(s.edges.length>25000||s.trains.length>300||s.stations.length>1200||s.industries?.length>120||s.edges.some(e=>!Array.isArray(e)||e.length!==2||!e.every(n=>typeof n==='string'&&keyValid(n))||Math.max(...parseKey(e[0]).map((v,i)=>Math.abs(v-parseKey(e[1])[i])))!==1))return false;
graph=new Map();for(let [a,b] of s.edges)link(a,b);stations=s.stations||[];industries=Array.isArray(s.industries)?s.industries:[];nextIndustry=s.nextIndustry||industries.length+1;trains=s.trains||[];nextTrain=s.nextTrain||trains.length+1;nextStation=s.nextStation||stations.length+1;signals=(s.signals||[]).filter(sig=>graph.get(sig.a)?.has(sig.b));points=new Map(s.points||[]);nextSignal=s.nextSignal||signals.length+1;bank=s.bank??5000;delivered=s.delivered||0;for(let st of stations)ensureIndustry(st);recomputeBlocks();selectedTrainId=trains[0]?.id||null;for(let t of trains){t.phase=t.phase||'edge';t.turnProgress=t.turnProgress||0;t.past=t.past||[];t.schedule=t.schedule||stations.map(s=>s.id);t.speed=0;t.status='Ready';t.dwell=0;t.nextTarget=null;t.progress=clamp(t.progress||0,0,.999);t.cars=clamp(t.cars||0,0,5);t.freightType=t.freightType||'timber';t.manualPoints=!!t.manualPoints;t.load=t.load||0;t.loadGood=t.loadGood||'timber';if(!t.trail?.length)resetTrail(t)}dirty=true;setMode('select',true);updateUI();updateIndustryUI();return true}
function load(){try{const raw=localStorage.getItem(STORAGE);return raw?loadState(JSON.parse(raw)):false}catch(e){return false}}
function exportSave(){let blob=new Blob([JSON.stringify(snapshot(),null,2)],{type:'application/json'});let u=URL.createObjectURL(blob);let a=document.createElement('a');a.href=u;a.download='railworks-railway-save.json';document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),250);announce('Railway exported as JSON. Keep a copy before updating itch.io.')}
$('#btnExport').onclick=exportSave;$('#btnImport').onclick=()=>$('#importSave').click();$('#importSave').onchange=async e=>{let file=e.target.files?.[0];if(!file)return;try{let candidate=JSON.parse(await file.text());if(!candidate||!Array.isArray(candidate.edges)||!Array.isArray(candidate.stations)||!Array.isArray(candidate.trains))throw Error('Invalid railway file');if(!confirm('Replace your current railway with this imported save?'))return;if(!loadState(candidate))throw Error('Invalid railway data');save();announce('Railway imported successfully.')}catch(err){announce('Cannot import this file: '+err.message)}finally{e.target.value=''}};
$('#btnSave').onclick=save;$('#btnReset').onclick=()=>{if(confirm('Delete this frontier and begin with a blank map? Export your save first if needed.')){try{localStorage.removeItem(STORAGE)}catch(e){}emptyWorld()}};
function loop(now){let dt=Math.min(.08,Math.max(0,(now-timePrev)/1000||.016));timePrev=now;tickCamera(dt);if(!paused)tickTrains(dt);render3D();overlayDraw();labels();if(now-minimapTick>180){drawMini();minimapTick=now}if(now-uiTick>110){updateTrainUI();uiTick=now}if(noticeExpiry&&now>noticeExpiry){$('#notice').style.opacity='0';noticeExpiry=0}requestAnimationFrame(loop)}
window.__RAILWORKS_TEST={get graph(){return graph},get trains(){return trains},get stations(){return stations},get industries(){return industries},get DEPOSITS(){return DEPOSITS},get mapSize(){return [WORLD_X,WORLD_Z]},get anchor(){return anchor},get signals(){return signals},get blocks(){return blocks},get bank(){return bank},get delivered(){return delivered},get blockByEdge(){return blockByEdge},project,world,K,shortest,entryBlocks,signalAt,placeSignal,link,addLine,planRail,layPlanned,bendAllowed,edgeEnds,curveAt,curveLength,head,behind,trackRibbon,get camera(){return camera},get viewTarget(){return viewTarget},get heldKeys(){return heldKeys},tickCamera,recordTrail,resetTrail,recomputeBlocks,occupiedBy,createTrain,tickTrains,buildStatic,render3D,demo,addIndustry,depositNear,industryCanPlace,emptyWorld,addStation,setMode,clickWorld,turnPoint};
try{initGL();resize();addEventListener('resize',resize);if(load())announce('Saved railway loaded — welcome back.');else demo();requestAnimationFrame(loop)}catch(e){console.error(e);$('#failure').style.display='block';$('#failure').innerHTML='<h2>Could not start the 3D simulation</h2><p>'+String(e.message).replaceAll('<','&lt;')+'</p>'}
})();
