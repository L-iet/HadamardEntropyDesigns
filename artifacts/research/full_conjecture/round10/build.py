# SPDX-License-Identifier: Apache-2.0
"""Build and exactly validate the tenth research pass."""
from pathlib import Path
from datetime import datetime,timezone
import importlib.util
import hashlib
import json
import subprocess
import sys

ROOT=Path(__file__).resolve().parent

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def assemble():
    prefix=load_module('round9_build',ROOT.parent/'round9/build.py').PREFIX
    prefix=prefix.replace('Support rigidity, optimal atom exchange,\\\\and modular Hadamard-extension counts',
                          'Compatible modular codes, exact lifting,\\\\and concentration barriers')
    codes=(ROOT/'codes/codes.tex').read_text(encoding='utf-8')
    trap_path=ROOT/'code_traps/traps.tex'
    traps=trap_path.read_text(encoding='utf-8') if trap_path.exists() else ''
    incidence=(ROOT/'codes/neighbor_counts.tex').read_text(encoding='utf-8')
    modular=(ROOT/'modular/modular.tex').read_text(encoding='utf-8')
    nonlinear=(ROOT/'nonlinear/quantitative.tex').read_text(encoding='utf-8')
    exchange=(ROOT/'exchanges/bridges.tex').read_text(encoding='utf-8')
    exchange=exchange.split('\\maketitle',1)[1].split('\\end{document}',1)[0]
    exchange='\n\\section{Concentration moves and target-dependent bridges}\n'+exchange
    intro=r'''
\begin{abstract}
We derive a parity rigidity theorem for modularly orthogonal sign
families of length $4q$, $q$ odd. In a self-orthogonal residue code
containing five real orthogonal rows, all sign words are mutually
compatible. Over a prime field an exact extension gives a self-dual
neighbor preserving all old sign words; at the known order twenty,
one such change raises the sign count from eight to twenty.
A second order-twenty example is terminal: no new sign row preserves
eleven of its twelve rows. An exact two-row replacement unlocks ten
new rows and a complete matrix, again in one self-dual neighbor.
An exact neighbor-incidence identity gives a quantitative surplus
criterion; in a codimension-one retained space the entire modular
sign pool splits between just two self-dual codes.
We also classify modular false positives at orders congruent to four
modulo eight, give exact monotone concentration moves and limits of
specified-target bridge barriers, and strengthen a low-degree model
obstruction to an explicit moment-error floor.
None of these results proves a sufficiently large sign count at
unknown orders. The full conjecture and bibliographic novelty remain
unresolved.
\end{abstract}
The standing distribution target remains exact unbiased pairwise
independence on $N-4$ bits and collision at least
$1/N-1/(1024N^4)$; the proven extraction implication is in
\path{../round6/collision_stability.tex}. Here we investigate an
alternative global residue-code model as well as its obstructions.
'''
    ending=r'''
\section{The unresolved step}
The modular correction is now explicit for both order classes modulo
eight, but its positivity is not established in general.
A self-orthogonal code makes its sign words compatible once five
orthogonal rows are installed, but does not force many such words.
Self-dual neighbor moves solve a concrete artificial restriction at
order twenty; the general rule still requires a real extension and
cannot preserve all rows of a terminal frame while augmenting it.
The concentration endpoint algorithm can terminate at a suboptimal
vertex, and support relabeling preserves rather than constructs a law.

The central missing ingredient is therefore an actual construction
or lower-count theorem, or an exchange theorem that can replace
incompatible rows globally. No universal extension assertion is
assumed here. Finite checks validate explicit benchmarks; they do
not prove unknown-order existence or establish priority.
\end{document}
'''
    (ROOT/'research.tex').write_text(prefix+intro+codes+traps+incidence+modular+exchange+nonlinear+ending,encoding='utf-8',newline='\n')
    short=prefix.replace('Compatible modular codes, exact lifting,\\\\and concentration barriers',
                         'Compatible sign words and\\\\an exact self-dual code pivot')
    (ROOT/'code_pivots.tex').write_text(short+codes+traps+incidence+'\n\\end{document}\n',encoding='utf-8',newline='\n')

def main():
    assemble()
    checkers=['codes/check.py','modular/check.py','exchanges/check_exact.py','nonlinear/check.py']
    if (ROOT/'code_traps/check.py').exists():checkers.append('code_traps/check.py')
    elif (ROOT/'code_traps/verify.py').exists():checkers.append('code_traps/verify.py')
    checkers.append('codes/check_neighbors.py')
    for checker in checkers:
        result=subprocess.run([sys.executable,str(ROOT/checker)],cwd=ROOT,check=True,
                              capture_output=True,encoding='utf-8')
        destination=ROOT/'.build'/'checker-output'/Path(checker).parent.name
        destination.mkdir(parents=True,exist_ok=True)
        (destination/'output.txt').write_text(result.stdout+result.stderr,encoding='utf-8')
        print(checker,'passed')
    compiler=load_module('prior_compiler',ROOT.parent/'round3/build.py');compiler.ROOT=ROOT
    pages={name:compiler.compile_one(ROOT/name) for name in ('code_pivots.tex','research.tex')}
    files=[p for p in ROOT.rglob('*') if p.is_file() and '.build' not in p.parts
           and '__pycache__' not in p.parts and p.suffix not in ('.aux','.log','.out')
           and p!=ROOT/'verification.json']
    record={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'pages':pages,
            'checkersPassed':checkers,'typesettingChecksPassed':True,
            'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)},
            'scope':{'hadamardConjectureProved':False,'unknownOrderConstructed':False,
                     'noveltyEstablished':False,'leanFormalization':False,'gitCommits':False}}
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Built tenth-pass papers:',pages)

if __name__=='__main__':main()
