from explore import paley

def solve(rows,b,n):
 a=[sum(x<<i for i,x in enumerate(row))|(v<<n) for row,v in zip(rows,b)];r=0;piv=[]
 for j in range(n):
  k=next((k for k in range(r,len(a)) if (a[k]>>j)&1),None)
  if k is None:continue
  a[r],a[k]=a[k],a[r]
  for k in range(len(a)):
   if k!=r and (a[k]>>j)&1:a[k]^=a[r]
  piv.append(j);r+=1
 if any((x&((1<<n)-1))==0 and (x>>n)&1 for x in a):return None
 ans=0
 for i,j in enumerate(piv):ans|=((a[i]>>n)&1)<<j
 return ans
h=paley(19);labels=[sum(int(row[j]<0)<<i for i,j in enumerate([1,2,3,4,5])) for row in h]
for j in range(1,20):
 for deg in range(1,6):
  mons=[m for m in range(32) if m.bit_count()<=deg];a=[[int(x&m==m) for m in mons] for x in labels];sol=solve(a,[int(row[j]<0) for row in h],len(mons))
  if sol is not None:print(j,deg,[m for i,m in enumerate(mons) if (sol>>i)&1]);break
