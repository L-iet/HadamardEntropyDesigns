/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Polynomials
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators symmDiff
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem benchmarkPolynomial12_col0_degree : benchmarkPolynomial12 0∈lowDegreeBooleanCode 4 3 := by
  exact squarefreeBooleanPolynomial_mem (polynomialMaskTerms 4 (benchmarkPolynomialMasks12 0)) (by decide)

theorem benchmarkPolynomial12_col0_values : ∀ j : Fin 12,
  booleanValueSign (benchmarkPolynomial12 0 (benchmarkLabels12 j))=benchmarkHadamard12 j 1 := by
  intro j
  fin_cases j <;> decide

theorem benchmarkPolynomial12_col0_affine : benchmarkPolynomial12 0∈lowDegreeBooleanCode 4 1 := by
  exact squarefreeBooleanPolynomial_mem (polynomialMaskTerms 4 (benchmarkPolynomialMasks12 0)) (by decide)

end EntropyDesigns
