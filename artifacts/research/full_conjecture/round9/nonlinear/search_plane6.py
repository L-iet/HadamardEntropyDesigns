from itertools import combinations
s=sorted(set(range(16))-{0,1,2,3});mons=[m for m in range(16) if m.bit_count()<=2]
gens=[sum(int(x&m==m)<<i for i,x in enumerate(s)) for m in mons];code={0}
for x in gens:code|={y^x for y in list(code)}
vertices=sorted(x for x in code if x.bit_count()==6 and x&1==0);print('size',len(code),'verts',len(vertices))
adj=[sum(1<<j for j,y in enumerate(vertices) if (x^y).bit_count()==6) for x in vertices]
count=0
def find(cl,cand):
 global count
 count+=1
 if len(cl)==6:return cl
 if len(cl)+cand.bit_count()<6:return
 while cand:
  low=cand&-cand;j=low.bit_length()-1;cand^=low
  ans=find(cl+[j],cand&adj[j])
  if ans:return ans
 return
ans=find([], (1<<len(vertices))-1);print('search',count,'answer',ans,'words',None if ans is None else[vertices[j] for j in ans])



