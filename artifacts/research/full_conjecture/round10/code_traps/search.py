# SPDX-License-Identifier: Apache-2.0
"""Bounded deterministic search using adjacent original project code."""
from pathlib import Path
import importlib.util,random,json
root=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('code_checks',root.parent/'codes/check.py')
cc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cc)
q=19;residues={x*x%q for x in range(1,q)}
chi=lambda x:0 if x%q==0 else (1 if x%q in residues else -1)
h=[[1]*20]+[[1]+[chi(j-i)-(i==j) for j in range(q)] for i in range(q)]
profiles={};records=[];trap=None
for trial in range(200):
    rng=random.Random(2026112000+trial)
    basis=cc.self_dual_extension(h[:5],5,rng)
    family=cc.sign_words_from_systematic(basis,5)
    rank=len(cc.rref(family,5))
    key=f'{len(family)}/{rank}';profiles[key]=profiles.get(key,0)+1
    if len(family)<20 and rank==10:
        assert cc.verify_family(family,5)[0]==0
        trap=dict(trial=trial,seed=2026112000+trial,basis=basis,signs=family,
                  signCount=len(family),rank=rank)
        break
result=dict(profiles=profiles,trials=trial+1,trap=trap)
(root/'search.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(profiles=profiles,trials=trial+1,trapFound=trap is not None)))
