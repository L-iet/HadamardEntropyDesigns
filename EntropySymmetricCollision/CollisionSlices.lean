/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetric.OrbitEntropy
public import EntropySymmetricCollision.CollisionMoments
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

theorem symmetric_atom_region_cap {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hw : ∀ x,0≤w x) (hsym : CoordinatePermutationInvariant w)
    (T : Finset (Fin d → Bool)) (x : Fin d → Bool)
    (hT : hammingSlice d (hammingWeight x)⊆T) :
    (Nat.choose d (hammingWeight x):ℝ)*w x≤∑ y∈T,w y := by
  classical
  have he : (∑ y∈hammingSlice d (hammingWeight x),w y)=
      (Nat.choose d (hammingWeight x):ℝ)*w x := by
    calc
      _ = ∑ _∈hammingSlice d (hammingWeight x),w x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact symmetric_equal_weight w hsym y x (Finset.mem_filter.mp hy).2
      _ = _ := by simp [hammingSlice_card]
  rw [←he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hT (fun y _ _ => hw y)

theorem symmetric_region_collision_cap {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hw : ∀ x,0≤w x) (hsym : CoordinatePermutationInvariant w)
    (T : Finset (Fin d → Bool)) (M : ℝ)
    (horbit : ∀ x∈T,hammingSlice d (hammingWeight x)⊆T)
    (hsize : ∀ x∈T,M≤(Nat.choose d (hammingWeight x):ℝ)) :
    M*(∑ x∈T,(w x)^2)≤(∑ x∈T,w x)^2 := by
  classical
  have hcap (x : Fin d → Bool) (hx : x∈T) : M*w x≤∑ y∈T,w y :=
    (mul_le_mul_of_nonneg_right (hsize x hx) (hw x)).trans
      (symmetric_atom_region_cap w hw hsym T x (horbit x hx))
  have hh := Finset.sum_le_sum (s:=T) (fun x hx =>
    mul_le_mul_of_nonneg_right (hcap x hx) (hw x))
  have he (x : Fin d → Bool) : M*w x*w x=M*(w x)^2 := by ring
  simp_rw [he] at hh
  rw [←Finset.mul_sum,←Finset.mul_sum] at hh
  nlinarith

theorem choose_two_le_middle {d k : ℕ} (hk : 2≤k) (hkd : k≤d-2) :
    Nat.choose d 2≤Nat.choose d k := by
  have hsmall : ∀ j,2≤j → j≤d/2 → Nat.choose d 2≤Nat.choose d j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; rfl
    | succ j hj ih =>
      intro hhalf
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  by_cases h : k≤d/2
  · exact hsmall k hk h
  · have hkd' : k≤d := by omega
    rw [←Nat.choose_symm hkd']
    exact hsmall (d-k) (by omega) (by omega)

end
end EntropyDesigns.SymmetricEntropy
