# SPDX-License-Identifier: Apache-2.0
"""Exact code-neighbor incidence and two-code-pool checks."""
from pathlib import Path
import importlib.util
import json

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('local_code_tools',ROOT/'check.py')
cc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cc)

def main():
    trap=json.loads((ROOT.parent/'code_traps/search.json').read_text())['trap']
    exchange=json.loads((ROOT.parent/'code_traps/exchange.json').read_text())
    old=tuple(tuple(x) for x in trap['basis'])
    rows=[tuple(x) for x in trap['signs']]
    kept=[x for i,x in enumerate(rows) if i not in exchange['deletedOldRowIndices']]
    g=cc.rref(kept,5);assert len(g)==9
    old_sign=set(cc.sign_words_from_systematic(old,5))
    shared=set(cc.sign_words_from_systematic(g,5))
    pool=set(cc.sign_words_from_systematic(cc.rref(cc.kernel(g,5),5),5))
    new=cc.pivot_code(old,exchange['newRows'][0],5)
    new_sign=set(cc.sign_words_from_systematic(new,5))
    assert old_sign|new_sign==pool and old_sign&new_sign==shared
    assert (len(old_sign),len(shared),len(pool),len(new_sign))==(12,10,22,20)
    assert len(new_sign)==len(pool)-len(old_sign)+len(shared)

    data=json.loads((ROOT/'checks.json').read_text())
    c=tuple(tuple(x) for x in data['allSelfDualExtensionsOfSeed'][0]['selfDualBasis'])
    s=cc.sign_words_from_systematic(c,3)
    # Four prescribed independent sign rows, chosen deterministically.
    g=cc.rref(s[:4],3);assert len(g)==4
    old_words=cc.span(c,3);dual=cc.span(cc.kernel(g,3),3)
    neighbors={}
    for v in sorted(dual-old_words):
        if cc.dot(v,v)%3:continue
        alpha=[cc.dot(row,v)%3 for row in c]
        factor=pow(next(x for x in alpha if x),-1,3)
        key=tuple(x*factor%3 for x in alpha)
        if key not in neighbors:neighbors[key]=cc.pivot_code(c,v,3)
    assert len(neighbors)==4
    r=len(s);b=len(cc.signs(cc.span(g,3),3));mg=len(cc.signs(dual,3))
    sizes=[len(cc.sign_words_from_systematic(basis,3)) for basis in neighbors.values()]
    assert sum(x-r for x in sizes)==mg-r-(r-b)*3
    result={'passed':True,
            'order20TwoCodePool':{'oldClasses':12,'sharedClasses':10,'modularPool':22,'newClasses':20},
            'order12Incidence':{'oldClasses':r,'retainedSpanSignClasses':b,
              'modularPool':mg,'neighborSignCounts':sizes,
              'sumGainsMinusLosses':sum(x-r for x in sizes)}}
    (ROOT/'neighbor_checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('Exact code-neighbor incidence and two-code-pool checks passed.')

if __name__=='__main__':main()
