#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,time,math,gzip,os
from dataclasses import dataclass
from fractions import Fraction as F
from n6_fixed_core import FI,S,PI,sin_interval,cos_interval,sqrt_fi,floordiv,ceildiv
from n6_exact_intervals import candidate_bounds

QBAR=FI.frac(F(142559,50000)); RB=sqrt_fi(QBAR); RHO=sqrt_fi(QBAR-FI.frac(F(1,4)))-FI.frac(F(1,2)); CAPK=RHO-FI.frac(F(1,2))
R_PIN=FI.frac(F(9,10)); HALF=FI.frac(F(1,2)); ZERO=FI.point_int(0)
NAMES=('E','N','W','D','S');OFF={n:2+3*i for i,n in enumerate(NAMES)};DIM=17
RAT={'E':F(0),'N':F(1,2),'W':F(1),'D':F(1),'S':F(3,2)}; PINR={'E':F(0),'N':F(1,2),'W':F(11,12),'D':F(5,4),'S':F(19,12)}; CANDR={'E':F(0),'N':F(1,2),'W':F(1),'D':F(5,4),'S':F(3,2)}
def pang(r):return FI.frac(r)*PI
PIN={n:pang(PINR[n]) for n in NAMES};PHI0={n:pang(RAT[n]) for n in NAMES};PHIC={n:pang(CANDR[n]) for n in NAMES}
hq,sq,tq,dq,qq=candidate_bounds()
def fq(q):return FI.bounds_frac(q.lo,q.hi)
SC,TC,DC=fq(sq),fq(tq),fq(dq)
CC={'E':(SC+1,SC),'N':(SC,SC+1),'W':(SC-1,TC),'D':(-DC,-DC),'S':(TC,SC-1)}
assert fq(qq).hi < QBAR.lo

def sn(x):return sin_interval(x.lo,x.hi)
def cs(x):return cos_interval(x.lo,x.hi)
def wid(ph):return (cs(ph).abs()+sn(ph).abs()).div_int(2)
def minabs(x):return 0 if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))
def div_bound_floor(num:int,den:int):
 assert den>0; return floordiv(num*S,den)
def div_bound_ceil(num:int,den:int):
 assert den>0; return ceildiv(num*S,den)

@dataclass
class Box:
 iv:list[FI];depth:int=0
 def copy(self):return Box(list(self.iv),self.depth)
 def get(self,n):k=OFF[n];return self.iv[k],self.iv[k+1],self.iv[k+2]
 def seto(self,n,ph=None,a=None,b=None):
  k=OFF[n]
  if ph is not None:self.iv[k]=ph
  if a is not None:self.iv[k+1]=a
  if b is not None:self.iv[k+2]=b
 def center(self,n):
  ph,a,b=self.get(n);c=cs(ph);z=sn(ph);return a*c-b*z,a*z+b*c
 def nearest(self,n):
  ph,a,_=self.get(n);r=a-HALF;return r*cs(ph),r*sn(ph)
 def marker(self,n):ph,_,b=self.get(n);return ph+FI.frac(F(5,4))*b

def contract(box):
 cx,cy=box.iv[:2]
 xa=minabs(cx)+HALF.lo;ya=minabs(cy)+HALF.lo
 if floordiv(xa*xa,S)+floordiv(ya*ya,S)>QBAR.hi:return False
 for _ in range(3):
  ch=False
  for n in NAMES:
   ph,a,b=box.get(n);de=PIN[n]-ph;q1=R_PIN*cs(de);q2=R_PIN*sn(de)
   na=a.intersect(FI(q1.lo-HALF.hi,q1.hi+HALF.hi));nb=b.intersect(FI(q2.lo-HALF.hi,q2.hi+HALF.hi))
   if na is None or nb is None:return False
   bm=minabs(nb); y=bm+HALF.lo; rem=QBAR-FI(floordiv(y*y,S),ceildiv(y*y,S))
   if rem.hi<0:return False
   ahi=sqrt_fi(FI(max(0,rem.lo),max(0,rem.hi))).hi-HALF.lo
   na=na.intersect(FI(FI.frac(F(177,200)).lo,ahi))
   if na is None:return False
   x=na.lo+HALF.lo; rem2=QBAR-FI(floordiv(x*x,S),ceildiv(x*x,S))
   if rem2.hi<0:return False
   bh=sqrt_fi(FI(max(0,rem2.lo),max(0,rem2.hi))).hi-HALF.lo
   nb=nb.intersect(FI(-bh,bh))
   if nb is None:return False
   if na!=a or nb!=b:box.seto(n,a=na,b=nb);ch=True
  if not ch:break
 return box.get('W')[0].lo<=box.get('D')[0].hi

def point_contract(box,n,qx,qy):
 ph,a,b=box.get(n);c=cs(ph);z=sn(ph);ue=qx*c+qy*z;uf=qx*(-z)+qy*c
 na=a.intersect(FI(ue.lo-HALF.hi,ue.hi+HALF.hi));nb=b.intersect(FI(uf.lo-HALF.hi,uf.hi+HALF.hi))
 if na is None or nb is None:return False
 box.seto(n,a=na,b=nb);return True

def devmin(ph,target):
 if not(ph.hi<target.lo or target.hi<ph.lo):return 0
 return target.lo-ph.hi if ph.hi<target.lo else ph.lo-target.hi

def capmax(th:int):
 x=FI(th,th);si=sn(x);co=cs(x);prod=RB*si
 b1=CAPK*co-HALF*si;b2=RB-co-si
 if prod.hi<=HALF.lo:return b1.hi
 if prod.lo>=HALF.hi:return b2.hi
 return max(b1.hi,b2.hi)

def side(box,n):
 cx,cy=box.iv[:2]
 if n=='E':return cx+HALF
 if n=='N':return cy+HALF
 if n=='W':return HALF-cx
 if n=='S':return HALF-cy
 raise KeyError

def cardlin(box,n):
 cx,cy=box.iv[:2];ph,a,b=box.get(n);c=cs(ph);z=sn(ph);w=wid(ph)
 if n=='E':return c,(-b*z)-cx-(HALF+w)
 if n=='N':return z,b*c-cy-(HALF+w)
 if n in ('W','D'):return -c,b*z+cx-(HALF+w)
 if n=='S':return -z,cy-b*c-(HALF+w)
 raise KeyError

def ownlin(box,n):
 cx,cy=box.iv[:2];ph,a,b=box.get(n);return FI.point_int(1),-(cx*cs(ph)+cy*sn(ph))-(HALF+wid(ph))

def central_contract(box,p):
 cx,cy=box.iv[:2]
 if not point_contract(box,'E',cx+1,ZERO):return False
 if not point_contract(box,'N',ZERO,cy+1):return False
 if ((p>>2)&1)==0 and not point_contract(box,'W',cx-1,ZERO):return False
 if ((p>>3)&1)==0 and not point_contract(box,'D',cx-1,ZERO):return False
 if ((p>>4)&1)==0 and not point_contract(box,'S',ZERO,cy-1):return False
 if ((p>>2)&1)==0 and ((p>>3)&1)==0:return False
 for n in ('E','N','W','S'):
  i=NAMES.index(n)
  if ((p>>i)&1)==0:
   dm=devmin(box.get(n)[0],PHIC[n])
   if dm>=FI.frac(F(2,5)).lo:return False
   if side(box,n).lo>capmax(dm):return False
 for a,b in (('E','W'),('N','S')):
  ia=NAMES.index(a);ib=NAMES.index(b)
  if ((p>>ia)&1)==0 and ((p>>ib)&1)==0:
   if devmin(box.get(a)[0],PHIC[a])+devmin(box.get(b)[0],PHIC[b]) > 4*(RHO.hi-S):return False
 for i,n in enumerate(NAMES):
  ph,a,b=box.get(n)
  if (p>>i)&1:
   if n in ('E','N') and devmin(ph,PHIC[n])>=FI.frac(F(9,20)).lo:return False
   co,re=ownlin(box,n);lo=a.lo
   if re.hi<0:lo=max(lo,div_bound_floor(-re.hi,co.hi))
   cc,rr=cardlin(box,n)
   if cc.lo<=0 or rr.lo>=0:return False
   hi=min(a.hi,div_bound_ceil(-rr.lo,cc.lo))
   if lo>hi:return False
   box.seto(n,a=FI(lo,hi))
  else:
   co,re=cardlin(box,n);lo=a.lo
   if co.hi<=0:return False
   if re.hi<0:lo=max(lo,div_bound_floor(-re.hi,co.hi))
   if lo>a.hi:return False
   box.seto(n,a=FI(lo,a.hi))
 for i,n in enumerate(NAMES):
  cc,rr=cardlin(box,n); a=box.get(n)[1]; cm=a*cc+rr
  if (p>>i)&1:
   co,re=ownlin(box,n);om=a*co+re
   if om.hi<0 or cm.lo>=0:return False
  elif cm.hi<0:return False
 return True

def markerok(box):
 m={n:box.marker(n) for n in NAMES};gs=[m['N']-m['E'],m['W']-m['N'],m['D']-m['W'],m['S']-m['D'],m['E']+2*PI-m['S']];lo=PI.div_int(3);hi=(2*PI).div_int(3)
 return all(g.hi>=lo.lo and g.lo<=hi.hi for g in gs)
def footok(box):
 cx,cy=box.iv[:2];f={n:box.nearest(n) for n in NAMES}
 if f['E'][0].hi<cx.lo+HALF.lo or f['N'][1].hi<cy.lo+HALF.lo:return False
 for n in ('W','D','S'):
  x,y=f[n]
  if x.lo>=cx.hi+HALF.hi or y.lo>=cy.hi+HALF.hi:return False
  if not(x.lo<=cx.hi-HALF.lo or y.lo<=cy.hi-HALF.lo):return False
 return True
def pinok(box,n):
 ph,a,b=box.get(n);de=PIN[n]-ph;x=R_PIN*cs(de)-a;y=R_PIN*sn(de)-b
 return x.lo<HALF.hi and x.hi>-HALF.hi and y.lo<HALF.hi and y.hi>-HALF.hi
def foreign(box,sq,pin):
 ph,a,b=box.get(sq);de=PIN[pin]-ph;x=R_PIN*cs(de)-a;y=R_PIN*sn(de)-b
 return x.lo>-HALF.lo and x.hi<HALF.lo and y.lo>-HALF.lo and y.hi<HALF.lo

def axisupper(box,a,b,ax):
 pa=box.center(a);pb=box.center(b);dx=pb[0]-pa[0];dy=pb[1]-pa[1];dot=dx*cs(ax)+dy*sn(ax);wi=wid(ax-box.get(a)[0]);wj=wid(ax-box.get(b)[0]);return dot.abs().hi-(wi.lo+wj.lo)
def overlap(box,a,b):
 pa=box.get(a)[0];pb=box.get(b)[0];return all(axisupper(box,a,b,z)<0 for z in (pa,pa+pang(F(1,2)),pb,pb+pang(F(1,2))))
def commonsep(box,i,j):
 if i=='C':pi=(box.iv[0],box.iv[1]);wi=HALF
 else:pi=box.center(i);wi=wid(box.get(i)[0])
 if j=='C':pj=(box.iv[0],box.iv[1]);wj=HALF
 else:pj=box.center(j);wj=wid(box.get(j)[0])
 th=wi.hi+wj.hi;return (pj[0]-pi[0]).abs().lo>=th or (pj[1]-pi[1]).abs().lo>=th
def oblique(box):
 ns=('C',)+NAMES;z=0
 for i in range(6):
  for j in range(i+1,6):z+=not commonsep(box,ns[i],ns[j])
 return z

def nearcand(x,c,eta):return x.lo>=c.hi-eta and x.hi<=c.lo+eta
def local(box):
 eta=FI.frac(F(1,100));
 if not nearcand(box.iv[0],SC,eta.hi) or not nearcand(box.iv[1],SC,eta.hi):return False
 for n in NAMES:
  if not nearcand(box.get(n)[0],PHIC[n],eta.hi):return False
  x,y=box.center(n);tx,ty=CC[n]
  if not nearcand(x,tx,eta.hi) or not nearcand(y,ty,eta.hi):return False
 return True
def fourside(box,p):
 if any((p>>NAMES.index(n))&1 for n in ('E','N','W','S')):return False
 eta=FI.frac(F(1,24)).hi
 return all(nearcand(box.get(n)[0],PHIC[n],eta) for n in NAMES)
def cover(box,p):
 if local(box):return 'local'
 if oblique(box)<=1:return 'one'
 if fourside(box,p):return 'four'
 return None

def reject(box,p):
 for _ in range(2):
  if not contract(box):return 'con'
  if not central_contract(box,p):return 'cent'
  if not markerok(box):return 'mark'
  if not footok(box):return 'foot'
 if any(not pinok(box,n) for n in NAMES):return 'pin'
 if any(foreign(box,a,b) for a in NAMES for b in NAMES if a!=b):return 'foreign'
 if any(overlap(box,NAMES[i],NAMES[j]) for i in range(5) for j in range(i+1,5)):return 'overlap'
 return None

def initbox():
 qtr=pang(F(1,4));v=[FI.bounds_frac(F(-23,200),F(23,200)),FI.bounds_frac(F(-23,200),F(23,200))]
 for n in NAMES:v += [FI(PHI0[n].lo-qtr.hi,PHI0[n].hi+qtr.hi),FI.bounds_frac(F(177,200),F(223,200)),FI.bounds_frac(F(-117,250),F(117,250))]
 return Box(v)
SCA=[.23,.23]+sum(([math.pi/2,.23,.94] for _ in NAMES),[])
def possible_axes(box,a,b):
 pa=box.get(a)[0];pb=box.get(b)[0];axs=(pa,pa+pang(F(1,2)),pb,pb+pang(F(1,2)));return [x for x in axs if axisupper(box,a,b,x)>=0]
def split(box):
 sc=[(x.width()/S)/z for x,z in zip(box.iv,SCA)]
 for n in NAMES:sc[OFF[n]]*=1.25
 for a,b in (('W','N'),('S','E'),('D','W'),('D','S')):
  if len(possible_axes(box,a,b))==1:
   for n in (a,b):k=OFF[n];sc[k]*=3;sc[k+1]*=2;sc[k+2]*=2
 k=max(range(DIM),key=sc.__getitem__);x=box.iv[k];m=(x.lo+x.hi)//2
 if m==x.lo:m+=1
 a=box.copy();b=box.copy();a.iv[k]=FI(x.lo,m);b.iv[k]=FI(m,x.hi);a.depth=b.depth=box.depth+1;return a,b

def encbox(b):
 return {'depth':b.depth,'iv':[[x.lo,x.hi] for x in b.iv]}
def decbox(o):return Box([FI(x[0],x[1]) for x in o['iv']],int(o['depth']))
def saveck(path,p,q,st):
 tmp=path+'.tmp'
 with gzip.open(tmp,'wt',encoding='utf-8') as f:json.dump({'v':1,'bits':50,'p':p,'q':[encbox(x) for x in q],'st':st},f,separators=(',',':'))
 os.replace(tmp,path)
def loadck(path):
 with gzip.open(path,'rt',encoding='utf-8') as f:o=json.load(f)
 if o.get('bits')!=50:raise ValueError('checkpoint bit width mismatch')
 return int(o['p']),[decbox(x) for x in o['q']],dict(o['st'])

def run(p,nodes,depth,checkpoint=None,resume=None,checkpoint_every=25000,report_every=0):
 if resume:
  p0,q,st=loadck(resume)
  if p0!=p:raise ValueError('checkpoint branch mismatch')
 else:q=[initbox()];st={'vis':0,'split':0,'surv':0,'rej':{},'cov':{},'maxd':0}
 target=st['vis']+nodes;last=st['vis'];tm=time.time()
 while q and st['vis']<target:
  b=q.pop();st['vis']+=1;st['maxd']=max(st['maxd'],b.depth);r=reject(b,p)
  if r:st['rej'][r]=st['rej'].get(r,0)+1;continue
  c=cover(b,p)
  if c:st['cov'][c]=st['cov'].get(c,0)+1;continue
  if b.depth>=depth:st['surv']+=1;continue
  x,y=split(b);q.extend((x,y));st['split']+=1
  if checkpoint and st['vis']-last>=checkpoint_every:
   saveck(checkpoint,p,q,st);last=st['vis']
  if report_every and st['vis']%report_every==0:
   print('progress',p,st['vis'],'queue',len(q),'depth',st['maxd'],'surv',st['surv'],flush=True)
 if checkpoint:saveck(checkpoint,p,q,st)
 out=dict(st);out['queue']=len(q);out['sec']=time.time()-tm;out['complete']=not q and not st['surv'];return out

def selftest():
 b=initbox();b.iv[0]=SC;b.iv[1]=SC
 rt2=sqrt_fi(FI.point_int(2))
 vals={
  'E':(PHIC['E'],SC+1,SC),
  'N':(PHIC['N'],SC+1,-SC),
  'W':(PHIC['W'],1-SC,-TC),
  'D':(PHIC['D'],DC*rt2,ZERO),
  'S':(PHIC['S'],1-SC,TC),
 }
 for n,(ph,a,bb) in vals.items():b.seto(n,ph=ph,a=a,b=bb)
 assert reject(b,8) is None
 assert cover(b,8)=='local'
 assert not central_contract(initbox(),0)

def main():
 selftest()
 ap=argparse.ArgumentParser();ap.add_argument('--branch',default='8');ap.add_argument('--nodes',type=int,default=1000);ap.add_argument('--depth',type=int,default=48);ap.add_argument('--checkpoint');ap.add_argument('--resume');ap.add_argument('--checkpoint-every',type=int,default=25000);ap.add_argument('--report-every',type=int,default=0);a=ap.parse_args();ps=range(32) if a.branch=='all' else [int(a.branch)]
 if len(list(ps))>1 and (a.checkpoint or a.resume):raise SystemExit('checkpoint/resume require one branch')
 ps=range(32) if a.branch=='all' else [int(a.branch)]
 print('fixed bits',50,'QBAR',QBAR.f(),'pi',PI.f())
 for p in ps:print(p,json.dumps(run(p,a.nodes,a.depth,a.checkpoint,a.resume,a.checkpoint_every,a.report_every),sort_keys=True),flush=True)
if __name__=='__main__':main()
