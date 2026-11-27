# SPDX-License-Identifier: Apache-2.0
"""Reproduce the twelfth research pass with exact arithmetic checks."""
from pathlib import Path
from datetime import datetime,timezone
import importlib.util,hashlib,json,subprocess,sys

ROOT=Path(__file__).resolve().parent

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def prefix(title):
    text=module('prior_style',ROOT.parent/'round9/build.py').PREFIX
    return text.replace('Support rigidity, optimal atom exchange,\\\\and modular Hadamard-extension counts',title)

INPUT=r'''
\section*{Inputs from the preceding work}
The unconditional multiplier input is
$\tau(u)=O(\log u/\log\log u)$ for positive odd $u$.
Its proof and formalization are preserved in the main project.
Define $T(x)=\max(2,\max_{u\le x,\ u\text{ odd}}\tau(u))$.
Eventual monotonicity and a finite initial buffer give
$T(x)=O(\log x/\log\log x)$, and Sylvester doubling gives
a Hadamard matrix of order $2^{T(x)}v$ for every integer $1\le v\le x$.

\begin{theorem}[Spanning-slope input, proved in the eleventh pass]
\label{thm:design-spanning-slopes}
Let $h=2^s$, let $k$ be a known Hadamard order, and assume
$s\le h-k<h/2$. There is an exactly unbiased pairwise-independent
uniform law on $h^2$ atoms and $kh-1$ bits. It is a strict local
collision maximum in the full moment polytope, and has collision
$1/h^2$ and total variation distance exactly $1-1/k$ from the convex
hull of all order-$kh$ Hadamard laws. Its additive R\'enyi entropy
excess is $\log(h/k)$ for every entropy order.
\end{theorem}
The proof is in \path{../round11/global_repair.tex}, Sections 2--4:
finite-field affine slopes provide exact moments, and an omitted
additive-spanning slope set forces the support orthogonality graph
to consist of $h$ disjoint $h$-cliques. No small-repair assertion
or unproved Hadamard existence assumption is inserted here.
'''

def assemble():
    arithmetic=(ROOT/'arithmetic/arithmetic.tex').read_text(encoding='utf-8')
    rates=(ROOT/'stability/prime_rates.tex').read_text(encoding='utf-8')
    gaps=(ROOT/'stability/gap_transfer.tex').read_text(encoding='utf-8')
    project=(ROOT/'stability/project_input.tex').read_text(encoding='utf-8')
    moments=(ROOT/'moments/third.tex').read_text(encoding='utf-8')
    dilations=(ROOT/'dilations/dilations.tex').read_text(encoding='utf-8')
    intro=r'''
\begin{abstract}
The multiplier theorem combines with a precise conditional
prime-distribution estimate to give partial Hadamard matrices with
at least $n/2-\sqrt n\exp(O(\log n/\log\log n))$ rows.
Only Dirichlet GRH for power-of-two conductors is needed for that
result, and it remains explicitly conditional.
Separately, the same unconditional multiplier theorem gives exact
near-optimal isotropic laws with only $n+n^{1/2+o(1)}$ atoms but
distance $1-(1+o(1))n^{-1/2}$ from every Hadamard mixture.
Third completion moments improve two finite certificates.
An exact rational-dilation parameterization and a structured
order-twenty example show why arithmetic concatenations cannot
automatically be completed while preserving their rows.
These results neither construct unknown Hadamard orders nor prove
the full conjecture; bibliographic novelty is unestablished.
\end{abstract}
The unconditional existence inputs are read from the existing project.
No attempt to validate the recent GRH announcement is part of this
pass. Conditional and unconditional statements below are kept separate.
'''
    ending=r'''
\section{What remains unresolved}
The arithmetic construction reaches roughly half the required rows,
and the rational dilation solves scaled orthogonality without solving
its sign constraints. The structured finite example requires changing
a prescribed row before reaching a full matrix.
The third-moment method improves one weak count certificate only to
eleven, still below its completion threshold. No uniform high-moment
or count-surplus theorem is proved.

The stronger instability family shows that a fixed relative
collision or entropy tolerance cannot guarantee a small repair across
dimensions. It does not exclude the dimension-dependent punctured
extraction route. A full-conjecture proof still needs an actual
all-order construction or a global exchange theorem that reaches its
target without assuming the desired matrix exists.
The checks validate finite arithmetic certificates, not GRH or the
asymptotic constants. No Lean code, commits or submissions were made.
\end{document}
'''
    full=prefix('Quantitative partial Hadamard matrices,\\\\near-square instability, and rational dilations')
    (ROOT/'research.tex').write_text(full+intro+arithmetic+INPUT+rates+gaps+project+moments+dilations+ending,encoding='utf-8',newline='\n')
    conditional=prefix('A conditional square-root-scale deficit\\\\for partial Hadamard matrices')
    (ROOT/'conditional_partial.tex').write_text(conditional+arithmetic+'\n\\end{document}\n',encoding='utf-8',newline='\n')
    stability=prefix('Quantitative near-square instability\\\\from established Hadamard constructions')
    (ROOT/'stability_rates.tex').write_text(stability+INPUT+rates+gaps+project+'\n\\end{document}\n',encoding='utf-8',newline='\n')

def main():
    assemble()
    checkers=['arithmetic/check.py','stability/check.py','moments/check.py','dilations/check.py']
    for checker in checkers:
        result=subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True,
                              capture_output=True,encoding='utf-8')
        folder=ROOT/'.build'/'checkers'/Path(checker).parent.name
        folder.mkdir(parents=True,exist_ok=True)
        (folder/'output.txt').write_text(result.stdout+result.stderr,encoding='utf-8')
        print(checker,'passed',flush=True)
    compiler=module('prior_compiler',ROOT.parent/'round3/build.py');compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in
           ('conditional_partial.tex','stability_rates.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p!=ROOT/'verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':checkers,'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'scope':{'hadamardConjectureProved':False,'unknownOrderConstructed':False,
                     'GRHVerified':False,'arithmeticPartialBoundConditional':True,
                     'projectMultiplierAndStabilityRatesUnconditional':True,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built twelfth-pass papers:',pages)

if __name__=='__main__':main()
