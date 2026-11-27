Codimension-two quotient geometry and exact compatible-frame optimization
20 November2026

quotients.tex gives a self-contained matrix proof of the classical
Q+(3,p) grid and applies it to signwords at N=4p. For G codimension2
inside a selfdual code and containing5 orthogonal signrows:
* All signclasses in Gperp form a weighted(p+1)x(p+1) rook grid,
  with |S(G)| common/universal classes.
* The2(p+1) selfdual extensions are exactly the rows and columns.
* Every compatible signfamily lies in one row or column. The maximum
  retained-space frame size is exactly common+maximum lineweight.
* Row-exchange and full-completion deletion costs within retainedG
  follow from linecounts and explicit crossing-point overlaps.

At order20 the first retained8 lexicographically sorted signrows give
b8,M48:4of12 extensions are full20; the average bound only gives15.
A reconstructed full code retains10 of12 oldsignrows. All one-row
deletions still span the old selfdual code, proving GLOBAL exact
augmentation and full-completion deletion cost2 without clique search.

The root's literal-first8 selection is separately checked: sorted
indices11,10,9,8,7,6,5,4. It gives b9,M51,24occupiedpoints,S2=96,
ordered orthogonal distinct-point weight588, and6full extensions.
The exact source basis, original signordering and retained indices
are embedded/recorded to avoid conflating these different choices.

Primary research context inspected: Edoukou, The weight distribution
of the functional codes defined by forms of degree2 on Hermitian
surfaces, Theorem4.2 (classical2-ruling structure):
https://www.numdam.org/article/JTNB_2009__21_1_131_0.pdf
No external code or text was copied. No novelty or all-order positivity
claim is made. The algebra and proofs here are independently derived.

check.py is standalone stdlib Python, exact finite-field/integer checks.
Run python check.py to regenerate checks.json. It reconstructs all12
codes for each retainedspace and checks every pool pair against the
grid compatibility formula and every output Gram matrix.
No Lean, git commits, or old-file edits.
