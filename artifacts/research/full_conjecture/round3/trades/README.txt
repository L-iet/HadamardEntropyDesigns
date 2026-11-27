ROUND THREE — SATURATED TRADE RIGIDITY

Read rigidity.tex for the principal proved results and their full proofs.
It is a section fragment using theorem/proposition/corollary/proof,
amsmath/amssymb and hyperref. No Lean work or commits were made.

MAIN RESULT

Let n=4m, m>1 odd, and let p be the smallest prime factor of m.
A genuinely new sign vector in the span of r<n Hadamard rows forces
  p <= r^(r/2) / 2^(r-1).

The expansion coefficients have a common denominator dividing m.
Cramer's rule forces that denominator to divide every sign anchor
determinant. Removing its forced power of two and applying Hadamard's
determinant bound gives the inequality. This is a uniform paper proof,
not an extrapolation from enumerated examples.

It follows that balanced saturated OA(n,n-1,2,2) fibers can be isolated
under ALL observation trades of degree <=R, for arbitrarily large R,
even at known Hadamard orders. Use CRT+Dirichlet to choose Paley primes
q=3 mod8 and q=1 mod each odd prime <=B; then n=q+1 has B-rough odd part.
Linnik's theorem and the elementary Chebyshev estimate give an infinite
known-order sequence where every nontrivial reduced trade has volume
at least (2-o(1))*loglog(n)/logloglog(n).

These are lower bounds for positive moves BETWEEN COMPLETE ARRAYS.
They do not refute bounded row-exchange AUGMENTATION of partial arrays.
Global coordinate flips change many observations and bypass the degree
restriction. No new Hadamard existence theorem is obtained.

ADDITIONAL PROVED RESULTS

- Every normalized Hadamard matrix of order n>4 admits a reduced
  observation trade of volume n/2. This supplies a universal large move.
- At orders n>4, n=4 mod8, all 2^(n-1) coordinate translations of an
  array are distinct. Thus the isolated states above are plentiful.
- A six-row trade is explicitly verified in Paley order12.

PRIOR ART

General unbounded Markov width for binary complete-graph models is
already known, and global bounds there are far stronger than the
iterated-log bound above. See Develin--Sullivant math/0308280 and
Kral'--Norine--Pangrac arXiv0810.1979 (global Omega(d^(2-epsilon))).
The statement here concerns the particular balanced, minimum-run
saturated Hadamard fibers. Its bibliographic novelty is not established.
Linnik's least-prime theorem is taken from the primary source described
in rigidity.tex; no numerical Linnik exponent is needed.

REPRODUCE FROM D:\Papers\Hadamard

  python research/full_conjecture/round3/trades/classify.py
  python research/full_conjecture/round3/trades/check_rigidity.py

The first script exhausts all 4368 active five-face sets of the four-bit
pairwise-independent moment polytope. Its 26 vertices are classified
exactly by rational arithmetic. For every vertex it exhausts all sign
linear forms. Non-coordinate forms always use exactly four coefficients
of magnitude 1/2 and a closed quadruple. This optional finite certificate
is not used in the denominator/rough-order proofs.

The second script certifies explicit rough Paley orders by trial-division
primality tests, verifies sampled sign spans by information-coordinate
exhaustion, and checks actual Hadamard Gram matrices and positive trades.
rigidity_checks.json records the results; classification.json records
the optional polytope classification.

Examples of guaranteed minimum trade volume from the determinant bound:
  order20:  >=6; order212: >=9; order330332: >=11.
These are lower bounds, not computations of the true minimum, except
that the separate explicit order12 six-row witness makes six sharp there
when combined with the elementary five-row rigidity analysis.

All new code uses Python's standard library and is authored for this
project under the root Apache-2.0 license. No external proof code was
downloaded or copied. Mathematical papers were consulted as literature.
