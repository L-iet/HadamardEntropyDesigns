from explore import paley
from itertools import product
from degree_explore import anf
h=paley(11);groups={}
for i,row in enumerate(h):
 x=sum(int(row[j]<0)<<z for z,j in enumerate([1,2,3]));groups.setdefault(x,[]).append(i)
for choices in product([0,1],repeat=8):
 labels=[None]*12
 for (x,ix),bit in zip(sorted(groups.items()),choices):
  labels[ix[0]]=x+8*bit
  if len(ix)==2:labels[ix[1]]=x+8*(1-bit)
 outside=sorted(set(range(16))-set(labels));degrees=[];polys=[]
 for j in range(1,12):
  best=9;ans=None
  for bits in product([0,1],repeat=4):
   f=[0]*16
   for row,lab in zip(h,labels):f[lab]=int(row[j]<0)
   for lab,bit in zip(outside,bits):f[lab]=bit
   a=anf(f,4);degree=max((i.bit_count() for i,z in enumerate(a) if z),default=0)
   if degree<best:best=degree;ans=[i for i,z in enumerate(a) if z]
  degrees.append(best);polys.append(ans)
 if max(degrees)<=2:
  print('FOUND',labels,outside,degrees,polys);break
else:print('NONE')
