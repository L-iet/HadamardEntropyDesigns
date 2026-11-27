/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem spanning_columns_have_anchor {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (H : Matrix I J ℚ)
    (hspan : Submodule.span ℚ (Set.range H.col)=⊤) :
    ∃ c : I ↪ J,(H.submatrix id c).det≠0 := by
  classical
  obtain ⟨K,a,ha,hs,hli⟩ := exists_linearIndependent' ℚ H.col
  letI : Finite K := Finite.of_injective a ha
  letI : Fintype K := Fintype.ofFinite K
  have htop : ⊤≤Submodule.span ℚ (Set.range (H.col∘a)) := by rw [hs,hspan]
  let b := Module.Basis.mk hli htop
  have hc : Fintype.card I=Fintype.card K := by
    calc
      Fintype.card I=Module.finrank ℚ (I → ℚ) := (Module.finrank_fintype_fun_eq_card ℚ).symm
      _=Fintype.card K := Module.finrank_eq_card_basis b
  let e : I ≃ K := Fintype.equivOfCardEq hc
  let c : I ↪ J := ⟨a∘e,ha.comp e.injective⟩
  refine ⟨c,?_⟩
  have hcols : LinearIndependent ℚ (H.submatrix id c).col := by
    change LinearIndependent ℚ ((H.col ∘ a) ∘ e)
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_col_iff_isUnit.mp hcols)).ne_zero

end
end EntropyDesigns.DenominatorTrades
