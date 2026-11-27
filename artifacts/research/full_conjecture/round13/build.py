# SPDX-License-Identifier: Apache-2.0
"""Reproduce the thirteenth research pass and its exact certificates."""
from pathlib import Path
from datetime import datetime, timezone
import importlib.util, hashlib, json, subprocess, sys

ROOT=Path(__file__).resolve().parent

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def prefix(title):
    text=module('prior_style',ROOT.parent/'round9/build.py').PREFIX
    return text.replace('Support rigidity, optimal atom exchange,\\\\and modular Hadamard-extension counts',title)

def assemble():
    parts={name:(ROOT/path).read_text(encoding='utf-8') for name,path in
           [('phase','quaternary/quaternary.tex'),('weighing','weighing/weighing.tex'),
            ('spectral','spectral/rank_two.tex'),('quantum','quantum/quantum.tex')]}
    intro=r'''
\begin{abstract}
Four formulations of the real Hadamard existence problem are examined.
For complex Hadamard matrices, the operator norm of the entrywise fourth
power exactly detects conversion to the quaternary phase alphabet and
gives a quantitative obstruction for Fourier-block families.
For weighing matrices with two zeros per row, all zero-preserving
Hadamard completions reduce to eight root choices; an explicit
order-twelve example has no real completion supported on its zeros.
Rank-two Gram errors have an integer-quantized energy spectrum, and
the energy $8(n-1)$ alone certifies a unique one-entry Hadamard repair.
Finally, flat quantum measurements give exact commuting criteria,
but even flat dilations with vanishing relative dimension overhead
do not ensure nearby projective descent with fixed sign labels.
These results provide local certificates and obstructions, not an
all-order construction. Bibliographic priority is not established.
\end{abstract}
The full conjecture asks for a real sign matrix $H$ with
$HH^T=nI_n$ for every positive $n$ divisible by four.
Each section below keeps its additional hypotheses explicit.
The finite checks certify examples; the general statements have paper proofs.
'''
    end=r'''
\section{The remaining existence steps}
The quaternary route requires an actual four-phase construction at every
even order, beyond the Fourier-block families excluded here. This is a
sufficient stronger target, not an assumed equivalence with all real
Hadamard existence. The weighing route requires compatible global
block data: even two zeros per row do not force completion of a
prescribed matrix. The Gram-error result is a local repair theorem;
we have no procedure reaching its threshold in every admissible order.
The quantum formulation does not remove the requirement of entrywise
real flatness, and unrestricted measurement simulation is a different task.

Useful next tests are to construct quaternary families outside the
Fourier-block orbit, classify the two-zero triangle constraints by
signed-permutation holonomy, and find a globally convergent sign-matrix
operation that reaches the certified repair energy without a target
Hadamard matrix as an input. No such all-order mechanism is proved here.
No Lean code, git commits, publication or submission is part of this pass.
\end{document}
'''
    (ROOT/'research.tex').write_text(prefix('Four-phase constructions, weighing completion,\\\\and exact Gram-defect repair')+intro+
        ''.join(parts[x] for x in ('phase','weighing','spectral','quantum'))+end,encoding='utf-8',newline='\n')
    for name,title,key in [
        ('phase_route','Four-phase Hadamard constructions\\\\and a quantitative Fourier obstruction','phase'),
        ('spectral_repair','Quantized Gram defects\\\\and exact one-entry Hadamard repair','spectral')]:
        (ROOT/(name+'.tex')).write_text(prefix(title)+parts[key]+'\n\\end{document}\n',encoding='utf-8',newline='\n')

def main():
    assemble()
    checkers=[x+'/check.py' for x in ('quaternary','weighing','spectral','quantum')]
    for checker in checkers:
        r=subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True,capture_output=True,encoding='utf-8')
        folder=ROOT/'.build'/'checkers'/Path(checker).parent.name;folder.mkdir(parents=True,exist_ok=True)
        (folder/'output.txt').write_text(r.stdout+r.stderr,encoding='utf-8')
        print(checker,'passed',flush=True)
    compiler=module('prior_compiler',ROOT.parent/'round3/build.py');compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('phase_route.tex','spectral_repair.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p!=ROOT/'verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':checkers,'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'scope':{'hadamardConjectureProved':False,'unknownOrderConstructed':False,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built thirteenth-pass papers:',pages)

if __name__=='__main__':main()
