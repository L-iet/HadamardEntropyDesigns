ARITHMETIC NORM RESEARCH — 20 NOVEMBER 2026

The addendum large_energy.tex proves three uniform statements and one
restricted-ansatz obstruction. No proof of the Hadamard conjecture is claimed.

1. For every odd positive m and every odd t >= (m^2+3)/4, there are
   four elements Ai in Z[C_m], coefficientwise odd, with sum Ai Ai*=4t.
   Ansatz: Ai=J+2xi, with sum xi=-m and sum xi^2=t.
   Hadamard's four-square transform plus Legendre's three-square theorem
   proves existence. The threshold is sharp within this particular ansatz.

2. For a prime p=3 mod4, every odd t >= (p^2+6p+21)/16 works.
   Three rows use the skew Legendre polynomial L plus odd constants;
   the fourth uses J+(3-p)/2. The J-coefficients cancel exactly, and
   the remaining equation is again an unrestricted three-square problem.
   More generally this works wherever a skew ternary L with LL*=m-J
   exists. No cyclic prime-power extension is asserted.

3. Any solution at (m,t) gives one at (m,s*t) for every positive odd s.
   An integer quaternion orthogonal-design matrix scales the norm and
   preserves coefficient parity. This cannot reduce energy to t=m.

4. All four rows cannot simultaneously belong to the restricted family
   ui L + vi + 2wi J with ui,vi odd. Its J-coefficient is 4 modulo 8,
   so it cannot be scalar. The successful family in item 2 avoids this
   restriction in the fourth row. This is not a general obstruction.

The generic theorem leaves the strip m <= t < (m^2+3)/4 unresolved,
as m varies through odd integers. The skew-prime construction lowers
the top of that strip for primes congruent to 3 modulo 4. The required
Hadamard boundary is still t=m, where the energy identity forces signs.

The generic theorem settles the entire broader fixed-m problem at m=1,3.
Together with the existing binary m=5 witness it settles m=5 as well.
The skew construction settles the entire broader fixed-m problem at m=7.
These do not constitute new all-order Hadamard matrix constructions.

REPRODUCE
  python research/full_conjecture/arithmetic/verify_large_energy.py

checks.json records 306 exact large-energy constructions, 306 exact
odd-multiplier checks and 96 skew-character constructions. Every norm
identity is checked by a direct integer cyclic-autocorrelation sum.
General proofs are in the TeX; computations are supplementary.

Primary references:
  N. C. Ankeny, Sums of three squares, Proc. AMS 8 (1957), 316-319.
  https://doi.org/10.1090/S0002-9939-1957-0085275-8
  R. E. A. C. Paley, On orthogonal matrices, J. Math. Phys. 12 (1933), 311-320.
  https://doi.org/10.1002/sapm1933121311

The addendum independently proves the required character-sum identity.
The classical three-square theorem is invoked, not reproved or imported as
code. All new script code is standard-library Python and Apache-2.0 as in
the parent directory LICENSE. Bibliographic novelty is not established.
