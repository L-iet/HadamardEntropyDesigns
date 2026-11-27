from explore import paley
from itertools import product

def anf(f,r):
 a=f[:]
 for j in range(r):
  for i in range(1<<r):
   if i&(1<<j):a[i]^=a[i^(1<<j)]
 return a
h=paley(11);seen={};labels=[]
for row in h:
 x=sum(int(row[j]<0)<<i for i,j in enumerate([1,2,3]));lab=x+8*seen.get(x,0);seen[x]=seen.get(x,0)+1;labels.append(lab)
outside=sorted(set(range(16))-set(labels));print('labels',labels,'outside',outside)
for j in range(1,12):
 best=9;ans=None
 for bits in product([0,1],repeat=4):
  f=[0]*16
  for row,lab in zip(h,labels):f[lab]=int(row[j]<0)
  for lab,bit in zip(outside,bits):f[lab]=bit
  a=anf(f,4);degree=max((i.bit_count() for i,x in enumerate(a) if x),default=0)
  if degree<best:best=degree;ans=[i for i,x in enumerate(a) if x]
 print(j,best,ans)
