from itertools import combinations

def paley(p):
 chi=lambda a:0 if a%p==0 else 1 if pow(a%p,(p-1)//2,p)==1 else -1
 h=[[1]*(p+1)]+[[1]+[chi(j-i)-int(i==j) for j in range(p)] for i in range(p)]
 assert all(sum(x*y for x,y in zip(a,b))==(p+1)*int(i==j) for i,a in enumerate(h) for j,b in enumerate(h))
 return h
