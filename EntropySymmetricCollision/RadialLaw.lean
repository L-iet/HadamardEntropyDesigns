/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetricCollision.SymmetricConstructions
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

theorem sum_weight_function (d : ℕ) (f : ℕ → ℝ) :
    (∑ x : Fin d → Bool,f (hammingWeight x))=
      ∑ k∈Finset.range (d+1),(Nat.choose d k:ℝ)*f k := by
  classical
  have hmap : ∀ x∈(Finset.univ : Finset (Fin d → Bool)),hammingWeight x∈Finset.range (d+1) := by
    intro x _
    have hk : hammingWeight x≤d := by
      unfold hammingWeight
      simpa using Finset.card_le_card (Finset.filter_subset (fun i : Fin d => x i=true) Finset.univ)
    exact Finset.mem_range.mpr (by omega)
  rw [←Finset.sum_fiberwise_of_maps_to' hmap f]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change ((hammingSlice d k).card:ℝ)*f k=(Nat.choose d k:ℝ)*f k
  rw [hammingSlice_card]

def radialLaw (d : ℕ) (a : ℕ → ℝ) (x : Fin d → Bool) : ℝ :=
  a (hammingWeight x)/(Nat.choose d (hammingWeight x):ℝ)

theorem radialLaw_symmetric (d : ℕ) (a : ℕ → ℝ) : CoordinatePermutationInvariant (radialLaw d a) := by
  intro σ x
  simp only [radialLaw,hammingWeight_perm]

theorem radialLaw_nonneg (d : ℕ) (a : ℕ → ℝ) (ha : ∀ k,0≤a k) :
    ∀ x,0≤radialLaw d a x := by
  intro x
  exact div_nonneg (ha _) (Nat.cast_nonneg _)

theorem radialLaw_moment (d : ℕ) (a f : ℕ → ℝ) :
    (∑ x,radialLaw d a x*f (hammingWeight x))=∑ k∈Finset.range (d+1),a k*f k := by
  classical
  unfold radialLaw
  rw [sum_weight_function d (fun k => a k/(Nat.choose d k:ℝ)*f k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hp : (0:ℝ)<Nat.choose d k := by
    exact_mod_cast Nat.choose_pos (show k≤d by have := Finset.mem_range.mp hk; omega)
  field_simp

theorem radialLaw_collision (d : ℕ) (a : ℕ → ℝ) :
    collision (radialLaw d a)=∑ k∈Finset.range (d+1),(a k)^2/(Nat.choose d k:ℝ) := by
  classical
  unfold collision radialLaw
  rw [sum_weight_function d (fun k => (a k/(Nat.choose d k:ℝ))^2)]
  apply Finset.sum_congr rfl
  intro k hk
  have hp : (0:ℝ)<Nat.choose d k := by
    exact_mod_cast Nat.choose_pos (show k≤d by have := Finset.mem_range.mp hk; omega)
  field_simp

end
end EntropyDesigns.SymmetricEntropy
