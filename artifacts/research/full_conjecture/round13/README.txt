THIRTEENTH RESEARCH PASS: FOUR DIFFERENT FORMULATIONS

Run python build.py from this directory. It reruns four exact arithmetic
checkers, assembles the papers, compiles each PDF three times, rejects
typesetting warnings and unresolved references, and hashes the artifacts.
Windows PDF compilation uses the existing WSL TeX installation.

research.pdf / research.tex: combined proofs of all four branches.
phase_route.pdf / phase_route.tex: self-contained four-phase approach.
spectral_repair.pdf / spectral_repair.tex: self-contained Gram-error results.
Each branch directory has its own exact checker and certificate.

Positive conclusions:
* Exact phase criterion rho4=1 and quantitative distance obstruction.
* Eight-root quadratic-time completion algorithm for all W(n,n-2), 4|n.
* Rank-two integer energy spectrum and unique one-entry repair at
  squared Gram error 8(n-1), the latter needing no rank assumption.
* Exact commuting/projective criteria for distinct-direction flat POVMs.

Limitations:
* A Fourier-orbit obstruction is not an order obstruction.
* The W(12,10) counterexample forbids preserving its specified entries,
  although Hadamard matrices of order 12 exist.
* No global algorithm reaches the local repair threshold in every order.
* The quantum obstruction uses fixed normalized sign-direction labels;
  arbitrary complex simulation/postprocessing is not ruled out.
* The quantum asymptotic family uses the earlier proved stability
  construction; it is not an independent all-order existence input.

The full Hadamard conjecture remains unresolved here. No unknown order
is constructed, no novelty claim is established, no Lean is changed,
and no git commits are made. Source citations are in the branch papers.
Code is original standard-library Python, Apache-2.0.
