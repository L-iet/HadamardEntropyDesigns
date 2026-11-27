/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyExchangeableHierarchy.ShiftAverages
public import Mathlib.Data.ZMod.Basic
@[expose] public section
namespace EntropyDesigns.ExchangeableHierarchy
noncomputable section
open scoped BigOperators ComplexOrder

def shiftHierarchy {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (k : ℕ) :
    Matrix (Fin k → G×G) (Fin k → G×G) ℂ :=
  uniformHierarchy (shiftEnsemble (G:=G)) k

/-- A concrete finite probability ensemble of real orthogonals with pure
maximally entangled conditional factors, every level of an actual complex
density hierarchy, consistency, symmetry, uniform one-copy average, and
no flat factor. All levels use the same displayed ensemble. -/
def FullShiftHierarchy (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nontrivial G] : Prop :=
  (0<1/(Fintype.card (G × (G → Bool)):ℝ) ∧
    (∑ z : G × (G → Bool),1/(Fintype.card (G × (G → Bool)):ℝ))=1) ∧
  (∀ t : G,∀ ε : G → Bool,
    signedShift t ε ∈ Matrix.orthogonalGroup G ℝ ∧
    (∃ i j : G,signedShift t ε i j=0) ∧
    ¬∀ i j : G,(signedShift t ε i j)^2=1/(Fintype.card G:ℝ)) ∧
  (∀ t : G,∀ ε : G → Bool,
    (∑ a : G×G,shiftVector t ε a*star (shiftVector t ε a))=1 ∧
    (pureTensor 1 (shiftVector t ε)).PosSemidef ∧
    Matrix.trace (pureTensor 1 (shiftVector t ε))=1 ∧
    ∀ i a : G,(∑ j,shiftVector t ε (i,j)*star (shiftVector t ε (a,j)))=
      ((if i=a then 1/(Fintype.card G:ℝ) else 0:ℝ):ℂ)) ∧
  (∀ k : ℕ,(shiftHierarchy (G:=G) k).PosSemidef ∧ Matrix.trace (shiftHierarchy (G:=G) k)=1) ∧
  (∀ k : ℕ,∀ π : Equiv.Perm (Fin k),∀ x y : Fin k → G×G,
    shiftHierarchy k (x ∘ π) (y ∘ π)=shiftHierarchy k x y) ∧
  (∀ k : ℕ,traceFirst (shiftHierarchy (G:=G) (k+1))=shiftHierarchy k) ∧
  (∀ a b : G×G,shiftHierarchy 1 (fun _ => a) (fun _ => b)=
    ((if a=b then 1/(Fintype.card G:ℝ)^2 else 0:ℝ):ℂ))

theorem full_shift_hierarchy {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Nontrivial G] :
    FullShiftHierarchy G := by
  classical
  have hs : (0:ℝ)<Fintype.card (G × (G → Bool)) := Nat.cast_pos.mpr Fintype.card_pos
  have hmass : (∑ z : G × (G → Bool),1/(Fintype.card (G × (G → Bool)):ℝ))=1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,one_div]
    exact mul_inv_cancel₀ hs.ne'
  have hv (z : G × (G → Bool)) : (∑ a : G×G,shiftEnsemble z a*star (shiftEnsemble z a))=1 :=
    shiftVector_normalized z.1 z.2
  refine ⟨⟨one_div_pos.mpr hs,hmass⟩,?_,?_,?_,?_,?_,?_⟩
  · intro t ε
    exact ⟨signedShift_orthogonal t ε,signedShift_has_zero t ε,signedShift_not_flat t ε⟩
  · intro t ε
    exact ⟨shiftVector_normalized t ε,pureTensor_posSemidef 1 (shiftVector t ε),
      pureTensor_trace 1 (shiftVector t ε) (shiftVector_normalized t ε),shiftVector_reduced_state t ε⟩
  · intro k
    exact ⟨uniformHierarchy_posSemidef shiftEnsemble k,uniformHierarchy_trace shiftEnsemble hv k⟩
  · intro k π x y
    exact uniformHierarchy_reindex shiftEnsemble k π x y
  · intro k
    exact uniformHierarchy_consistent shiftEnsemble hv k
  · intro a b
    exact shiftEnsemble_one_copy a b

/-- Every integer dimension greater than one has a finite model of the
full counterexample; the basis group has exactly n elements. -/
theorem every_dimension_false_positive (n : ℕ) (hn : 1<n) :
    ∃ (G : Type) (hG : AddCommGroup G) (hF : Fintype G)
      (hD : DecidableEq G) (hN : Nontrivial G),
      @Fintype.card G hF=n ∧ @FullShiftHierarchy G hG hF hD hN := by
  letI : NeZero n := ⟨by omega⟩
  letI : Fact (1<n) := ⟨hn⟩
  refine ⟨ZMod n,inferInstance,inferInstance,inferInstance,inferInstance,?_,full_shift_hierarchy⟩
  exact ZMod.card n

end
end EntropyDesigns.ExchangeableHierarchy
