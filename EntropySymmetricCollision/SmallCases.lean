/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetric.OrbitEntropy
public import EntropyDesigns.SharpEntropyTheorem
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def WeightSelected {d : ℕ} (S : Finset (Fin d → Bool)) (k : ℕ) : Prop :=
  ∃ x∈S,hammingWeight x=k

theorem invariant_support_fiber_card {d : ℕ} (S : Finset (Fin d → Bool))
    (hS : ∀ x y : Fin d → Bool,hammingWeight x=hammingWeight y → (x∈S ↔ y∈S))
    (k : ℕ) : (S.filter (fun x => hammingWeight x=k)).card=
      if WeightSelected S k then Nat.choose d k else 0 := by
  classical
  by_cases h : WeightSelected S k
  · obtain ⟨x,hx,hxk⟩ := h
    have he : S.filter (fun x => hammingWeight x=k)=hammingSlice d k := by
      ext y
      simp only [Finset.mem_filter,hammingSlice,Finset.mem_univ,true_and]
      constructor
      · exact fun h => h.2
      · intro hy
        exact ⟨(hS x y (hxk.trans hy.symm)).mp hx,hy⟩
    rw [he,hammingSlice_card,if_pos ⟨x,hx,hxk⟩]
  · have he : S.filter (fun x => hammingWeight x=k)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨x,(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
    simp [he,h]

theorem invariant_support_card {d : ℕ} (S : Finset (Fin d → Bool))
    (hS : ∀ x y : Fin d → Bool,hammingWeight x=hammingWeight y → (x∈S ↔ y∈S)) :
    S.card=∑ k∈Finset.range (d+1),if WeightSelected S k then Nat.choose d k else 0 := by
  classical
  have hf (k : ℕ) : (S.filter (fun x => hammingWeight x=k)).card=
      if WeightSelected S k then Nat.choose d k else 0 := by
    by_cases h : WeightSelected S k
    · obtain ⟨x,hx,hxk⟩ := h
      have he : S.filter (fun x => hammingWeight x=k)=hammingSlice d k := by
        ext y
        simp only [Finset.mem_filter,hammingSlice,Finset.mem_univ,true_and]
        constructor
        · exact fun h => h.2
        · intro hy
          exact ⟨(hS x y (hxk.trans hy.symm)).mp hx,hy⟩
      rw [he,hammingSlice_card,if_pos ⟨x,hx,hxk⟩]
    · have he : S.filter (fun x => hammingWeight x=k)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact h ⟨x,(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
      simp [he,h]
  rw [Finset.card_eq_sum_card_fiberwise (f:=hammingWeight) (t:=Finset.range (d+1)) (by
    intro x hx
    have hk : hammingWeight x≤d := by
      unfold hammingWeight
      simpa using Finset.card_le_card (Finset.filter_subset (fun i : Fin d => x i=true) Finset.univ)
    exact Finset.mem_range.mpr (by omega))]
  exact Finset.sum_congr rfl (fun k _ => hf k)

theorem five_bit_invariant_support_not_eight (S : Finset (Fin 5 → Bool))
    (hS : ∀ x y : Fin 5 → Bool,hammingWeight x=hammingWeight y → (x∈S ↔ y∈S)) :
    S.card≠8 := by
  classical
  intro he
  have hh := invariant_support_card S hS
  rw [he] at hh
  norm_num [Finset.sum_range_succ,Nat.choose] at hh
  split_ifs at hh <;> norm_num at hh

theorem five_bit_symmetric_no_attainment
    (w : (Fin 5 → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    collision w≠1/8 := by
  classical
  intro he
  have he' : collision w=1/(roundedDimension (5+1):ℝ) := by simpa [roundedDimension] using he
  have hc := (sharp_sign_cube_equality_completion (by omega : 2≤5) w hw hmass hmean hpair he').2.1
  norm_num [roundedDimension] at hc
  apply five_bit_invariant_support_not_eight (Finset.univ.filter fun x => w x≠0) _ hc
  intro x y hxy
  have hh := symmetric_equal_weight w hsym x y hxy
  simp [hh]


theorem invariant_support_weight_sum {d : ℕ} (S : Finset (Fin d → Bool))
    (hS : ∀ x y : Fin d → Bool,hammingWeight x=hammingWeight y → (x∈S ↔ y∈S))
    (f : ℕ → ℝ) :
    (∑ x∈S,f (hammingWeight x))=
      ∑ k∈Finset.range (d+1),if WeightSelected S k then (Nat.choose d k:ℝ)*f k else 0 := by
  classical
  have hmap : ∀ x∈S,hammingWeight x∈Finset.range (d+1) := by
    intro x _
    have hk : hammingWeight x≤d := by
      unfold hammingWeight
      simpa using Finset.card_le_card (Finset.filter_subset (fun i : Fin d => x i=true) Finset.univ)
    exact Finset.mem_range.mpr (by omega)
  rw [←Finset.sum_fiberwise_of_maps_to' hmap f]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_const, nsmul_eq_mul,invariant_support_fiber_card S hS k]
  by_cases hk : WeightSelected S k <;> simp [hk]

theorem six_bit_symmetric_no_attainment
    (w : (Fin 6 → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    collision w≠1/8 := by
  classical
  intro he
  have he' : collision w=1/(roundedDimension (6+1):ℝ) := by simpa [roundedDimension] using he
  have hh := sharp_sign_cube_equality_completion (by omega : 2≤6) w hw hmass hmean hpair he'
  have huniform : ∀ x,w x=0 ∨ w x=1/8 := by simpa [roundedDimension] using hh.1
  let S := Finset.univ.filter fun x : Fin 6 → Bool => w x≠0
  have hcard : S.card=8 := by simpa [S,roundedDimension] using hh.2.1
  have hS : ∀ x y : Fin 6 → Bool,hammingWeight x=hammingWeight y → (x∈S ↔ y∈S) := by
    intro x y hxy
    have he := symmetric_equal_weight w hsym x y hxy
    simp [S,he]
  have hc := invariant_support_card S hS
  rw [hcard] at hc
  have h1 := (hamming_moments w hmass hmean hpair).1
  have hpoint (x : Fin 6 → Bool) :
      (if w x≠0 then (hammingWeight x:ℝ) else 0)=8*(w x*(hammingWeight x:ℝ)) := by
    rcases huniform x with h|h <;> simp [h] <;> ring
  have hsum : (∑ x∈S,(hammingWeight x:ℝ))=24 := by
    simp only [S,Finset.sum_filter]
    simp_rw [hpoint]
    rw [←Finset.mul_sum,h1]
    norm_num
  have hq := invariant_support_weight_sum S hS (fun k => (k:ℝ))
  rw [hsum] at hq
  norm_num [Finset.sum_range_succ,Nat.choose] at hc hq
  split_ifs at hc hq <;> norm_num at *

end
end EntropyDesigns.SymmetricEntropy
