# SPDX-License-Identifier: Apache-2.0
"""Reproduce the eleventh research pass with exact branch checks."""
from pathlib import Path
from datetime import datetime,timezone
import importlib.util,hashlib,json,subprocess,sys

ROOT=Path(__file__).resolve().parent

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    return m

def assemble():
    prefix=module('old_style',ROOT.parent/'round9/build.py').PREFIX
    old='Support rigidity, optimal atom exchange,\\\\and modular Hadamard-extension counts'
    prefix=prefix.replace(old,'Limits of collision stability, completion geometry,\\\\and exact code landscapes')
    designs=(ROOT/'designs/repair.tex').read_text(encoding='utf-8')
    designs+=''.join((ROOT/'designs'/name).read_text(encoding='utf-8') for name in
                     ('concentration.tex','relative_stability.tex','relative_sequence.tex'))
    quotients=(ROOT/'quotients/quotients.tex').read_text(encoding='utf-8')
    moments=(ROOT/'moments/moments.tex').read_text(encoding='utf-8')
    census=(ROOT/'landscape/landscape.tex').read_text(encoding='utf-8')
    census=census.split('\\maketitle',1)[1].split('\\end{document}',1)[0]
    census='\n\\section{The full neighbor census of a specified terminal code}\n'+census
    census,bib=census.split('\\begin{thebibliography}',1)
    census+=(ROOT/'landscape/retention.tex').read_text(encoding='utf-8')
    bibliography='\\begin{thebibliography}'+bib
    intro=r'''
\begin{abstract}
We continue three complementary approaches to Hadamard existence.
At infinitely many known Hadamard orders, exactly pairwise-independent
laws can have relatively optimal collision and vanishing additive
entropy excess, yet distance tending to one from every convex mixture
of Hadamard laws. The laws are strict local collision maxima.
The finite-field construction has exact distance $1-1/k$.
An explicit global repair attains the sharp replacement fraction
$1-1/k$ while preserving endpoint collision probability in a separate
divisible power-of-two parameter regime.
Second, a four-dimensional isotropic quotient turns all compatible
completions into weighted rows and columns of a finite grid.
Third, exact global completion moments give a quantitative count
certificate, while a census of all 2441406 neighbors of one specified
order-twenty code finds exactly 42 improving moves.
These are structural theorems, constructive known-order benchmarks,
and finite certificates. They neither prove a count surplus at
unknown orders nor resolve the Hadamard conjecture. Novelty remains
unverified; classical incidence, code and character ingredients are
credited.
\end{abstract}
The standing near-extremal distribution target and its proven
extraction implication are unchanged; see
\path{../round6/collision_stability.tex}. We do not assume this input
exists at every admissible order. The repair family below concerns
full $n-1$-bit isotropy at known power-of-two orders, whereas the
extraction input is punctured to $N-4$ bits.
'''
    ending=r'''
\section{What is still missing}
The sharp global repair family rules out an automatic small-change
conversion of arbitrary isotropic laws to Hadamard mixtures; it
does not restrict all possible global constructions.
The quotient grid solves compatibility once a suitable retained
space and modular pool have been supplied. The moment certificate
still needs favorable counts, and the neighbor census covers one
code at one known order.

A proof of the full conjecture still requires an all-order
construction, or a uniform count or exchange theorem that reaches
the extraction threshold without assuming a desired matrix already
exists. The new tools do not supply that theorem. All finite
checks use exact arithmetic, not Lean; no external proof code,
Git commits, submissions or publications were made.
'''
    (ROOT/'research.tex').write_text(prefix+intro+designs+quotients+moments+census+ending+bibliography+'\n\\end{document}\n',encoding='utf-8',newline='\n')
    short=prefix.replace('Limits of collision stability, completion geometry,\\\\and exact code landscapes',
                         'Limits of collision stability and global repair\\\\for pairwise-independent laws')
    (ROOT/'global_repair.tex').write_text(short+designs+'\n\\end{document}\n',encoding='utf-8',newline='\n')

def main():
    assemble()
    checkers=['designs/check.py','designs/check_concentration.py',
              'designs/check_relative.py','designs/check_sequence.py',
              'quotients/check.py','moments/check.py',
              'landscape/census.py','landscape/check_retention.py']
    for checker in checkers:
        result=subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True,
                              capture_output=True,encoding='utf-8')
        folder=ROOT/'.build'/'checkers'/Path(checker).parent.name
        folder.mkdir(parents=True,exist_ok=True)
        (folder/'output.txt').write_text(result.stdout+result.stderr,encoding='utf-8')
        print(checker,'passed',flush=True)
    compiler=module('previous_compiler',ROOT.parent/'round3/build.py');compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('global_repair.tex','research.tex')}
    paths=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p!=ROOT/'verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':checkers,'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
            'scope':{'hadamardConjectureProved':False,'unknownOrderConstructed':False,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built eleventh-pass papers:',pages)

if __name__=='__main__':main()
