/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Matrices
public import EntropyCubic.Intrinsic12
public import EntropyCubic.Intrinsic20
public import EntropyCubic.Polys12.C0
public import EntropyCubic.Polys12.C1
public import EntropyCubic.Polys12.C2
public import EntropyCubic.Polys12.C3
public import EntropyCubic.Polys12.C4
public import EntropyCubic.Polys12.C5
public import EntropyCubic.Polys12.C6
public import EntropyCubic.Polys12.C7
public import EntropyCubic.Polys12.C8
public import EntropyCubic.Polys12.C9
public import EntropyCubic.Polys12.C10
public import EntropyCubic.Polys20.C0
public import EntropyCubic.Polys20.C1
public import EntropyCubic.Polys20.C2
public import EntropyCubic.Polys20.C3
public import EntropyCubic.Polys20.C4
public import EntropyCubic.Polys20.C5
public import EntropyCubic.Polys20.C6
public import EntropyCubic.Polys20.C7
public import EntropyCubic.Polys20.C8
public import EntropyCubic.Polys20.C9
public import EntropyCubic.Polys20.C10
public import EntropyCubic.Polys20.C11
public import EntropyCubic.Polys20.C12
public import EntropyCubic.Polys20.C13
public import EntropyCubic.Polys20.C14
public import EntropyCubic.Polys20.C15
public import EntropyCubic.Polys20.C16
public import EntropyCubic.Polys20.C17
public import EntropyCubic.Polys20.C18
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators Classical

def IsExactCubicSeedBenchmark {d r : ℕ}
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ)
    (labels : Fin (d+1) → Finset (Fin r))
    (f : Fin d → (Finset (Fin r) → ZMod 2)) (affineCount : ℕ) : Prop :=
  Matrix.IsHadamard H ∧ (∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) ∧ Function.Injective labels ∧
  (∀ i,f i∈lowDegreeBooleanCode r 3) ∧
  (∀ j i,booleanValueSign (f i (labels j))=H j i.succ) ∧
  (Finset.univ.filter (fun i => HasAffineSeedExtension labels (f i))).card=affineCount

theorem benchmarkPolynomial12_cubic : ∀ i : Fin 11,benchmarkPolynomial12 i∈lowDegreeBooleanCode 4 3 := by
 intro i
 fin_cases i
 · exact benchmarkPolynomial12_col0_degree
 · exact benchmarkPolynomial12_col1_degree
 · exact benchmarkPolynomial12_col2_degree
 · exact benchmarkPolynomial12_col3_degree
 · exact benchmarkPolynomial12_col4_degree
 · exact benchmarkPolynomial12_col5_degree
 · exact benchmarkPolynomial12_col6_degree
 · exact benchmarkPolynomial12_col7_degree
 · exact benchmarkPolynomial12_col8_degree
 · exact benchmarkPolynomial12_col9_degree
 · exact benchmarkPolynomial12_col10_degree

theorem benchmarkPolynomial12_values : ∀ j : Fin 12,∀ i : Fin 11,
 booleanValueSign (benchmarkPolynomial12 i (benchmarkLabels12 j))=benchmarkHadamard12 j i.succ := by
 intro j i
 fin_cases i
 · exact benchmarkPolynomial12_col0_values j
 · exact benchmarkPolynomial12_col1_values j
 · exact benchmarkPolynomial12_col2_values j
 · exact benchmarkPolynomial12_col3_values j
 · exact benchmarkPolynomial12_col4_values j
 · exact benchmarkPolynomial12_col5_values j
 · exact benchmarkPolynomial12_col6_values j
 · exact benchmarkPolynomial12_col7_values j
 · exact benchmarkPolynomial12_col8_values j
 · exact benchmarkPolynomial12_col9_values j
 · exact benchmarkPolynomial12_col10_values j

theorem benchmarkPolynomial12_affine_iff (i : Fin 11) :
 benchmarkPolynomial12 i∈lowDegreeBooleanCode 4 1 ↔ i.val<3 := by
 fin_cases i
 · simpa using benchmarkPolynomial12_col0_affine
 · simpa using benchmarkPolynomial12_col1_affine
 · simpa using benchmarkPolynomial12_col2_affine
 · simpa using benchmarkPolynomial12_col3_nonaffine
 · simpa using benchmarkPolynomial12_col4_nonaffine
 · simpa using benchmarkPolynomial12_col5_nonaffine
 · simpa using benchmarkPolynomial12_col6_nonaffine
 · simpa using benchmarkPolynomial12_col7_nonaffine
 · simpa using benchmarkPolynomial12_col8_nonaffine
 · simpa using benchmarkPolynomial12_col9_nonaffine
 · simpa using benchmarkPolynomial12_col10_nonaffine

theorem benchmarkPolynomial12_affine_count :
 (Finset.univ.filter (fun i : Fin 11 => benchmarkPolynomial12 i∈lowDegreeBooleanCode 4 1)).card=3 := by
 classical
 have heq : (Finset.univ.filter (fun i : Fin 11 => benchmarkPolynomial12 i∈lowDegreeBooleanCode 4 1))=
     Finset.univ.filter (fun i : Fin 11 => i.val<3) := by
   apply Finset.filter_congr
   intro i _
   exact benchmarkPolynomial12_affine_iff i
 rw [heq]
 decide

theorem benchmarkPolynomial12_affine_extension_count :
 (Finset.univ.filter (fun i : Fin 11 => HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 i))).card=3 := by
 classical
 have heq : (Finset.univ.filter (fun i : Fin 11 => HasAffineSeedExtension benchmarkLabels12 (benchmarkPolynomial12 i)))=
     Finset.univ.filter (fun i : Fin 11 => i.val<3) := by
   apply Finset.filter_congr
   intro i _
   exact benchmarkPolynomial12_affine_extension_iff i
 rw [heq]
 decide

theorem benchmark_order_12_cubic : IsExactCubicSeedBenchmark (d:=11) (r:=4)
 benchmarkHadamard12 benchmarkLabels12 benchmarkPolynomial12 3 := by
 exact ⟨benchmarkHadamard12_hadamard,benchmarkHadamard12_normalized,benchmarkLabels12_injective,
   benchmarkPolynomial12_cubic,benchmarkPolynomial12_values,benchmarkPolynomial12_affine_extension_count⟩

theorem benchmarkPolynomial20_cubic : ∀ i : Fin 19,benchmarkPolynomial20 i∈lowDegreeBooleanCode 5 3 := by
 intro i
 fin_cases i
 · exact benchmarkPolynomial20_col0_degree
 · exact benchmarkPolynomial20_col1_degree
 · exact benchmarkPolynomial20_col2_degree
 · exact benchmarkPolynomial20_col3_degree
 · exact benchmarkPolynomial20_col4_degree
 · exact benchmarkPolynomial20_col5_degree
 · exact benchmarkPolynomial20_col6_degree
 · exact benchmarkPolynomial20_col7_degree
 · exact benchmarkPolynomial20_col8_degree
 · exact benchmarkPolynomial20_col9_degree
 · exact benchmarkPolynomial20_col10_degree
 · exact benchmarkPolynomial20_col11_degree
 · exact benchmarkPolynomial20_col12_degree
 · exact benchmarkPolynomial20_col13_degree
 · exact benchmarkPolynomial20_col14_degree
 · exact benchmarkPolynomial20_col15_degree
 · exact benchmarkPolynomial20_col16_degree
 · exact benchmarkPolynomial20_col17_degree
 · exact benchmarkPolynomial20_col18_degree

theorem benchmarkPolynomial20_values : ∀ j : Fin 20,∀ i : Fin 19,
 booleanValueSign (benchmarkPolynomial20 i (benchmarkLabels20 j))=benchmarkHadamard20 j i.succ := by
 intro j i
 fin_cases i
 · exact benchmarkPolynomial20_col0_values j
 · exact benchmarkPolynomial20_col1_values j
 · exact benchmarkPolynomial20_col2_values j
 · exact benchmarkPolynomial20_col3_values j
 · exact benchmarkPolynomial20_col4_values j
 · exact benchmarkPolynomial20_col5_values j
 · exact benchmarkPolynomial20_col6_values j
 · exact benchmarkPolynomial20_col7_values j
 · exact benchmarkPolynomial20_col8_values j
 · exact benchmarkPolynomial20_col9_values j
 · exact benchmarkPolynomial20_col10_values j
 · exact benchmarkPolynomial20_col11_values j
 · exact benchmarkPolynomial20_col12_values j
 · exact benchmarkPolynomial20_col13_values j
 · exact benchmarkPolynomial20_col14_values j
 · exact benchmarkPolynomial20_col15_values j
 · exact benchmarkPolynomial20_col16_values j
 · exact benchmarkPolynomial20_col17_values j
 · exact benchmarkPolynomial20_col18_values j

theorem benchmarkPolynomial20_affine_iff (i : Fin 19) :
 benchmarkPolynomial20 i∈lowDegreeBooleanCode 5 1 ↔ i.val<5 := by
 fin_cases i
 · simpa using benchmarkPolynomial20_col0_affine
 · simpa using benchmarkPolynomial20_col1_affine
 · simpa using benchmarkPolynomial20_col2_affine
 · simpa using benchmarkPolynomial20_col3_affine
 · simpa using benchmarkPolynomial20_col4_affine
 · simpa using benchmarkPolynomial20_col5_nonaffine
 · simpa using benchmarkPolynomial20_col6_nonaffine
 · simpa using benchmarkPolynomial20_col7_nonaffine
 · simpa using benchmarkPolynomial20_col8_nonaffine
 · simpa using benchmarkPolynomial20_col9_nonaffine
 · simpa using benchmarkPolynomial20_col10_nonaffine
 · simpa using benchmarkPolynomial20_col11_nonaffine
 · simpa using benchmarkPolynomial20_col12_nonaffine
 · simpa using benchmarkPolynomial20_col13_nonaffine
 · simpa using benchmarkPolynomial20_col14_nonaffine
 · simpa using benchmarkPolynomial20_col15_nonaffine
 · simpa using benchmarkPolynomial20_col16_nonaffine
 · simpa using benchmarkPolynomial20_col17_nonaffine
 · simpa using benchmarkPolynomial20_col18_nonaffine

theorem benchmarkPolynomial20_affine_count :
 (Finset.univ.filter (fun i : Fin 19 => benchmarkPolynomial20 i∈lowDegreeBooleanCode 5 1)).card=5 := by
 classical
 have heq : (Finset.univ.filter (fun i : Fin 19 => benchmarkPolynomial20 i∈lowDegreeBooleanCode 5 1))=
     Finset.univ.filter (fun i : Fin 19 => i.val<5) := by
   apply Finset.filter_congr
   intro i _
   exact benchmarkPolynomial20_affine_iff i
 rw [heq]
 decide

theorem benchmarkPolynomial20_affine_extension_count :
 (Finset.univ.filter (fun i : Fin 19 => HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 i))).card=5 := by
 classical
 have heq : (Finset.univ.filter (fun i : Fin 19 => HasAffineSeedExtension benchmarkLabels20 (benchmarkPolynomial20 i)))=
     Finset.univ.filter (fun i : Fin 19 => i.val<5) := by
   apply Finset.filter_congr
   intro i _
   exact benchmarkPolynomial20_affine_extension_iff i
 rw [heq]
 decide

theorem benchmark_order_20_cubic : IsExactCubicSeedBenchmark (d:=19) (r:=5)
 benchmarkHadamard20 benchmarkLabels20 benchmarkPolynomial20 5 := by
 exact ⟨benchmarkHadamard20_hadamard,benchmarkHadamard20_normalized,benchmarkLabels20_injective,
   benchmarkPolynomial20_cubic,benchmarkPolynomial20_values,benchmarkPolynomial20_affine_extension_count⟩

end EntropyDesigns
