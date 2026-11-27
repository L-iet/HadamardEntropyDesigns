/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.HammingWeight
public import EntropyDesigns.Entropy
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Finset.Powerset
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

def CoordinatePermutationInvariant {d : ℕ} (w : (Fin d → Bool) → ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin d),∀ x : Fin d → Bool,w (fun i => x (σ i))=w x

def bitsOfSet {d : ℕ} (s : Finset (Fin d)) : Fin d → Bool := fun i => decide (i∈s)

def trueIndices {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter fun i => x i=true

def bitsSubsetEquiv (d : ℕ) : (Fin d → Bool) ≃ Finset (Fin d) where
  toFun := trueIndices
  invFun := bitsOfSet
  left_inv x := by
    funext i
    cases hx : x i <;> simp [bitsOfSet,trueIndices,hx]
  right_inv s := by
    ext i
    simp [bitsOfSet,trueIndices]

theorem hammingWeight_bitsOfSet {d : ℕ} (s : Finset (Fin d)) : hammingWeight (bitsOfSet s)=s.card := by
  unfold hammingWeight
  have he : (Finset.univ.filter fun i => bitsOfSet s i=true)=s := by
    ext i
    simp [bitsOfSet]
  rw [he]

def hammingSlice (d k : ℕ) : Finset (Fin d → Bool) := by
  classical
  exact Finset.univ.filter fun x => hammingWeight x=k

theorem hammingSlice_card (d k : ℕ) : (hammingSlice d k).card=Nat.choose d k := by
  classical
  have he : (hammingSlice d k).map (bitsSubsetEquiv d).toEmbedding=
      Finset.univ.powersetCard k := by
    ext s
    simp only [Finset.mem_map_equiv,hammingSlice,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_powersetCard]
    change hammingWeight (bitsOfSet s)=k ↔ s⊆Finset.univ ∧ s.card=k
    simp [hammingWeight_bitsOfSet]
  have hc := congrArg Finset.card he
  simpa only [Finset.card_map,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin] using hc

theorem equal_weight_coordinate_permutation {d : ℕ} (x y : Fin d → Bool)
    (hxy : hammingWeight x=hammingWeight y) :
    ∃ σ : Equiv.Perm (Fin d),x=fun i => y (σ i) := by
  classical
  let e : {i : Fin d // x i=true} ≃ {i : Fin d // y i=true} :=
    Fintype.equivOfCardEq (by simpa [Fintype.card_subtype, hammingWeight] using hxy)
  let σ := e.extendSubtype
  have hi (i : Fin d) : x i=true ↔ y (σ i)=true := by
    by_cases hx : x i=true
    · exact ⟨fun _ => e.extendSubtype_mem i hx,fun _ => hx⟩
    · have hy : y (σ i)≠true := e.extendSubtype_not_mem i hx
      exact ⟨fun h => False.elim (hx h),fun h => False.elim (hy h)⟩
  refine ⟨σ,?_⟩
  funext i
  have h := hi i
  cases hx : x i <;> cases hy : y (σ i) <;> simp_all

theorem symmetric_equal_weight {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hsym : CoordinatePermutationInvariant w) (x y : Fin d → Bool)
    (hxy : hammingWeight x=hammingWeight y) : w x=w y := by
  obtain ⟨σ,hσ⟩ := equal_weight_coordinate_permutation x y hxy
  rw [hσ]
  exact hsym σ y

theorem symmetric_atom_slice_cap {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (hsym : CoordinatePermutationInvariant w)
    (x : Fin d → Bool) : (Nat.choose d (hammingWeight x) : ℝ)*w x≤1 := by
  classical
  let S := hammingSlice d (hammingWeight x)
  have hc : ∀ y∈S,w y=w x := by
    intro y hy
    have he : hammingWeight y=hammingWeight x := (Finset.mem_filter.mp hy).2
    exact symmetric_equal_weight w hsym y x he
  have hsum : (∑ y∈S,w y)=(Nat.choose d (hammingWeight x) : ℝ)*w x := by
    calc
      _ = ∑ _∈S,w x := Finset.sum_congr rfl (fun y hy => hc y hy)
      _ = _ := by simp [S,hammingSlice_card]
  have hle : (∑ y∈S,w y)≤∑ y,w y := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro y _ _
    exact hw y
  rw [hmass,hsum] at hle
  exact hle

theorem symmetric_shannon_slice_lower {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (hsym : CoordinatePermutationInvariant w) :
    (∑ x,w x*Real.log (Nat.choose d (hammingWeight x) : ℝ))≤shannon w := by
  classical
  have ht (x : Fin d → Bool) : w x*Real.log (Nat.choose d (hammingWeight x) : ℝ)≤
      -(w x*Real.log (w x)) := by
    by_cases hz : w x=0
    · simp [hz]
    · have hp : 0<w x := lt_of_le_of_ne (hw x) (Ne.symm hz)
      have hcx : 0<(hammingSlice d (hammingWeight x)).card :=
        Finset.card_pos.mpr ⟨x,by simp [hammingSlice]⟩
      rw [hammingSlice_card] at hcx
      have hC : (0:ℝ)<Nat.choose d (hammingWeight x) := by exact_mod_cast hcx
      have hc := symmetric_atom_slice_cap w hw hmass hsym x
      have hl := Real.log_le_log (mul_pos hC hp) hc
      rw [Real.log_mul hC.ne' hp.ne',Real.log_one] at hl
      have hm := mul_le_mul_of_nonneg_left hl (hw x)
      nlinarith
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => ht x)
  simpa only [shannon,Finset.sum_neg_distrib] using hs

end
end EntropyDesigns.SymmetricEntropy
