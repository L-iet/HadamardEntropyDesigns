/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Polynomials
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators symmDiff
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem benchmarkPolynomial12_col6_degree : benchmarkPolynomial12 6∈lowDegreeBooleanCode 4 3 := by
  exact squarefreeBooleanPolynomial_mem (polynomialMaskTerms 4 (benchmarkPolynomialMasks12 6)) (by decide)

theorem benchmarkPolynomial12_col6_values : ∀ j : Fin 12,
  booleanValueSign (benchmarkPolynomial12 6 (benchmarkLabels12 j))=benchmarkHadamard12 j 7 := by
  intro j
  fin_cases j <;> decide

theorem benchmarkPolynomial12_col6_nonaffine : benchmarkPolynomial12 6∉lowDegreeBooleanCode 4 1 := by
  exact boolean_parallelogram_violation_not_affine (benchmarkPolynomial12 6)
    (naturalMaskSupport 4 1) (naturalMaskSupport 4 4) (by decide)

end EntropyDesigns
