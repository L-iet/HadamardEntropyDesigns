/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Polynomials
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators symmDiff
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem benchmarkPolynomial20_col10_degree : benchmarkPolynomial20 10∈lowDegreeBooleanCode 5 3 := by
  exact squarefreeBooleanPolynomial_mem (polynomialMaskTerms 5 (benchmarkPolynomialMasks20 10)) (by decide)

theorem benchmarkPolynomial20_col10_values : ∀ j : Fin 20,
  booleanValueSign (benchmarkPolynomial20 10 (benchmarkLabels20 j))=benchmarkHadamard20 j 11 := by
  intro j
  fin_cases j <;> decide

theorem benchmarkPolynomial20_col10_nonaffine : benchmarkPolynomial20 10∉lowDegreeBooleanCode 5 1 := by
  exact boolean_parallelogram_violation_not_affine (benchmarkPolynomial20 10)
    (naturalMaskSupport 5 1) (naturalMaskSupport 5 6) (by decide)

end EntropyDesigns
