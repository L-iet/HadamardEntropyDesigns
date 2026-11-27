/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.ColumnAnchor
public import Mathlib.Tactic.Push
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
open scoped Matrix
noncomputable section

theorem row_gram_spans_columns {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℚ) (n : ℚ) (hn : n≠0) (hg : H*H.transpose=n • 1) :
    Submodule.span ℚ (Set.range H.col)=⊤ := by
  rw [←Matrix.range_mulVecLin,LinearMap.range_eq_top]
  intro y
  refine ⟨H.transpose*ᵥ(n⁻¹ • y),?_⟩
  change H*ᵥ(H.transpose*ᵥ(n⁻¹ • y))=y
  rw [Matrix.mulVec_mulVec,hg,Matrix.smul_mulVec,Matrix.one_mulVec,smul_smul]
  simp [hn]

theorem integral_gram_has_anchor {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℤ) (n : ℕ) (hn : 0<n)
    (hg : ∀ i l,(∑ j,H i j*H l j)=if i=l then (n:ℤ) else 0) :
    ∃ c : I ↪ J,(H.submatrix id c).det≠0 := by
  let A : Matrix I J ℚ := fun i j => (H i j:ℚ)
  have hA : A*A.transpose=(n:ℚ) • 1 := by
    ext i l
    change (∑ j,(H i j:ℚ)*(H l j:ℚ))=(n:ℚ)*(if i=l then 1 else 0)
    have he : (∑ j,(H i j:ℚ)*(H l j:ℚ))=if i=l then (n:ℚ) else 0 := by exact_mod_cast hg i l
    rw [he]
    split_ifs <;> simp
  have hnQ : (n:ℚ)≠0 := by exact_mod_cast hn.ne'
  obtain ⟨c,hc⟩ := spanning_columns_have_anchor A (row_gram_spans_columns A n hnQ hA)
  refine ⟨c,?_⟩
  intro hz
  apply hc
  have he : ((H.submatrix id c).det:ℚ)=(A.submatrix id c).det := by
    simpa only [A,Matrix.map,Matrix.submatrix,Matrix.of_apply] using Int.cast_det (R := ℚ) (H.submatrix id c)
  rw [←he,hz,Int.cast_zero]

end
end EntropyDesigns.DenominatorTrades
