ROUND 12: QUANTITATIVE KNOWN-ORDER STABILITY COUNTEREXAMPLES

Files
  prime_rates.tex  TeX fragment with proofs and primary citations.
  check.py         Original exact Python standard-library checker.
  checks.json      Exact parameter and small-matrix certificates.

Key simplification
Every oddprime p gives known Hadamard order k=2(p+1): PaleyII ifp1mod4,
or doubled PaleyI ifp3mod4. Thus ordinary primegaps suffice; no arithmetic
progression theorem, irrationalrotation, GRH, or new Hadamard order.

Unconditional family
For dyadic h, X=h/2, A=ceil(X^(21/40)), take the largest prime
p<=X-A and k=2(p+1). Baker-Harman-Pintz gives g=h-k=Theta(h^(21/40))
for all sufficiently largeh. Then s=log2h<=g<h/2, so omittedslopes can
contain an additive basis. The round11 spanning-slope construction gives
an exact isotropic uniformh^2-atom strict local collisionmaximum on
n-1 bits,n=kh, with:
  relative collision deficit Theta(n^(-19/80));
  absolute collision deficit Theta(n^(-99/80));
  exact TV to all Hadamardmixtures 1-1/k=1-Theta(n^(-1/2));
  support n+Theta(n^(61/80));
  every Renyi/Shannon/minentropy excess Theta(n^(-19/80)).
The input theta21/40 is the classical published BHP exponent; no claim
that it is currently optimal is made.

Separate RH improvement
Ordinary RH alone, using Dudek's prime interval
(x-(4/pi)sqrt(x)logx,x], yields:
  relative deficit Theta(n^(-1/4)logn);
  absolute deficit Theta(n^(-5/4)logn);
  support n+Theta(n^(3/4)logn);
with the same exact TV asymptotic. RH is not used for the unconditional
construction or any finite computation.

Scope
These known-order families refute dimension-free relative-collision and
entropy stability, with quantitative rates and sublinear extra atoms.
They do not refute much tighter dimension-dependent absolute-deficit
windows, such as O(n^-4), and do not produce any unknown Hadamard order.
They use the full n-1-bit model, not an unstated atom bound for punctured
N-4-bit inputs. Novelty of the combined statements remains unestablished.

Reproduce
  python research/full_conjecture/round12/stability/check.py
The irrational exponent is checked by exact integer inequalities:
  (A-1)^40 < X^21 <= A^40.
Twenty-one dyadich values16through2^24 verify primality, both interval
bounds, spanning-basis feasibility, exact collision/distance formulas.
Small actual H12,H24,H48,H108 matrices verify PaleyII and doubled-I
constructions for both odd-prime residueclasses. Larger cases certify
parameters only, without materializing enormous distributions or matrices.
No numerical BHP asymptotic cutoff is claimed; the finite primes are
individually verified. All arithmetic is integer/Fraction, except isqrt.

Primary sources read
Baker, Harman, Pintz, The difference between consecutive primes,II(2001),
Theorem1: ordinary prime in[x-x^.525,x] for all sufficiently largex.
https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf
Paley, On Orthogonal Matrices(1933), both construction types.
https://doi.org/10.1002/sapm1933121311
Dudek, On the Riemann hypothesis and the difference between primes:
RH-conditional ordinary prime interval of width(4/pi)sqrt(x)logx.
https://arxiv.org/abs/1402.6417
No external code, oldfile edits, Lean work, commits or submissions.

Additional independent theorem: gap_transfer.tex
A uniform lower-interval gap bound G(x) for KNOWN Hadamard orders transfers
immediately to these counterexamples. Put A(h)=G(h)+log2h+1 and select a
Hadamard order near h-2A(h). Then g=h-k is between2A and3A, yielding
relative deficitTheta(A/h), absoluteTheta(A/h^3), supportexcessTheta(hA),
and exactTV1-1/k. A subpolynomial G implies relative n^-1/2+o(1), absolute
n^-3/2+o(1), and only n+n^1/2+o(1) atoms. This file assumes and clearly
states the gap input; it does not itself prove or claim that input.
It can consume the project's existing gap theorem after scope/provenance
verification by the integrating researcher. Prime_rates is independent
of such an input and remains unconditional via the publishedBHP theorem.
