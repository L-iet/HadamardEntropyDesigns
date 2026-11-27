/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Polynomials
public import EntropyCubic.AffineRestriction
public import EntropyCubic.Polys12.C0
public import EntropyCubic.Polys12.C1
public import EntropyCubic.Polys12.C2
@[expose] public section
namespace EntropyDesigns
open scoped symmDiff
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem benchmarkPolynomial12_col3_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 3) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels12 (benchmarkPolynomial12 3)
   10 11 2 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial12_col4_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 4) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels12 (benchmarkPolynomial12 4)
   10 11 2 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial12_col5_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 5) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels12 (benchmarkPolynomial12 5)
   10 8 1 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial12_col6_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 6) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels12 (benchmarkPolynomial12 6)
   10 8 1 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial12_col7_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 7) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels12 (benchmarkPolynomial12 7)
   10 3 6 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial12_col8_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 8) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels12 (benchmarkPolynomial12 8)
   11 8 3 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial12_col9_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 9) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels12 (benchmarkPolynomial12 9)
   10 11 2 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial12_col10_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 10) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels12 (benchmarkPolynomial12 10)
   10 11 2 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial12_affine_extension_iff (i : Fin 11) :
 HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 i) ↔ i.val<3 := by
 fin_cases i
 · simpa using affine_seed_extension_of_mem benchmarkLabels12 (benchmarkPolynomial12 0) benchmarkPolynomial12_col0_affine
 · simpa using affine_seed_extension_of_mem benchmarkLabels12 (benchmarkPolynomial12 1) benchmarkPolynomial12_col1_affine
 · simpa using affine_seed_extension_of_mem benchmarkLabels12 (benchmarkPolynomial12 2) benchmarkPolynomial12_col2_affine
 · simpa using benchmarkPolynomial12_col3_no_affine_extension
 · simpa using benchmarkPolynomial12_col4_no_affine_extension
 · simpa using benchmarkPolynomial12_col5_no_affine_extension
 · simpa using benchmarkPolynomial12_col6_no_affine_extension
 · simpa using benchmarkPolynomial12_col7_no_affine_extension
 · simpa using benchmarkPolynomial12_col8_no_affine_extension
 · simpa using benchmarkPolynomial12_col9_no_affine_extension
 · simpa using benchmarkPolynomial12_col10_no_affine_extension

end EntropyDesigns
