/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Polynomials
public import EntropyCubic.AffineRestriction
public import EntropyCubic.Polys20.C0
public import EntropyCubic.Polys20.C1
public import EntropyCubic.Polys20.C2
public import EntropyCubic.Polys20.C3
public import EntropyCubic.Polys20.C4
@[expose] public section
namespace EntropyDesigns
open scoped symmDiff
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem benchmarkPolynomial20_col5_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 5) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 5)
   18 4 8 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col6_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 6) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 6)
   17 19 7 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col7_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 7) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 7)
   17 4 1 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col8_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 8) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 8)
   17 19 7 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col9_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 9) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 9)
   17 19 7 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col10_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 10) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 10)
   17 19 7 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col11_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 11) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 11)
   18 5 11 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col12_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 12) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 12)
   18 4 8 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col13_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 13) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 13)
   17 19 7 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col14_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 14) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 14)
   17 4 1 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col15_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 15) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 15)
   17 19 7 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col16_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 16) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 16)
   18 16 6 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col17_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 17) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 17)
   17 19 7 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_col18_no_affine_extension :
 ¬HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 18) := by
 exact boolean_restriction_parallelogram_not_affine benchmarkLabels20 (benchmarkPolynomial20 18)
   17 19 7 0 (by decide) (by decide) (by decide)

theorem benchmarkPolynomial20_affine_extension_iff (i : Fin 19) :
 HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 i) ↔ i.val<5 := by
 fin_cases i
 · simpa using affine_seed_extension_of_mem benchmarkLabels20 (benchmarkPolynomial20 0) benchmarkPolynomial20_col0_affine
 · simpa using affine_seed_extension_of_mem benchmarkLabels20 (benchmarkPolynomial20 1) benchmarkPolynomial20_col1_affine
 · simpa using affine_seed_extension_of_mem benchmarkLabels20 (benchmarkPolynomial20 2) benchmarkPolynomial20_col2_affine
 · simpa using affine_seed_extension_of_mem benchmarkLabels20 (benchmarkPolynomial20 3) benchmarkPolynomial20_col3_affine
 · simpa using affine_seed_extension_of_mem benchmarkLabels20 (benchmarkPolynomial20 4) benchmarkPolynomial20_col4_affine
 · simpa using benchmarkPolynomial20_col5_no_affine_extension
 · simpa using benchmarkPolynomial20_col6_no_affine_extension
 · simpa using benchmarkPolynomial20_col7_no_affine_extension
 · simpa using benchmarkPolynomial20_col8_no_affine_extension
 · simpa using benchmarkPolynomial20_col9_no_affine_extension
 · simpa using benchmarkPolynomial20_col10_no_affine_extension
 · simpa using benchmarkPolynomial20_col11_no_affine_extension
 · simpa using benchmarkPolynomial20_col12_no_affine_extension
 · simpa using benchmarkPolynomial20_col13_no_affine_extension
 · simpa using benchmarkPolynomial20_col14_no_affine_extension
 · simpa using benchmarkPolynomial20_col15_no_affine_extension
 · simpa using benchmarkPolynomial20_col16_no_affine_extension
 · simpa using benchmarkPolynomial20_col17_no_affine_extension
 · simpa using benchmarkPolynomial20_col18_no_affine_extension

end EntropyDesigns
