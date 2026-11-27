/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetricCollision.RadialLaw
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

def twoSliceWeights (d k : ℕ) (a b : ℝ) (j : ℕ) : ℝ :=
  (if j=d then a else 0)+(if j=k then b else 0)

def threeSliceWeights (d k : ℕ) (a b c : ℝ) (j : ℕ) : ℝ :=
  (if j=0 then a else 0)+(if j=d then b else 0)+(if j=k then c else 0)

theorem twoSliceWeights_nonneg (d k : ℕ) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    ∀ j,0≤twoSliceWeights d k a b j := by
  intro j
  unfold twoSliceWeights
  split_ifs <;> linarith

theorem threeSliceWeights_nonneg (d k : ℕ) {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    ∀ j,0≤threeSliceWeights d k a b c j := by
  intro j
  unfold threeSliceWeights
  split_ifs <;> linarith

theorem twoSlice_moment (d k : ℕ) (hk : k≤d) (a b : ℝ) (f : ℕ → ℝ) :
    (∑ x,radialLaw d (twoSliceWeights d k a b) x*f (hammingWeight x))=a*f d+b*f k := by
  classical
  rw [radialLaw_moment]
  simp only [twoSliceWeights,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib]
  simp [show k<d+1 by omega]

theorem threeSlice_moment (d k : ℕ) (hk : k≤d) (a b c : ℝ) (f : ℕ → ℝ) :
    (∑ x,radialLaw d (threeSliceWeights d k a b c) x*f (hammingWeight x))=
      a*f 0+b*f d+c*f k := by
  classical
  rw [radialLaw_moment]
  simp only [threeSliceWeights,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib]
  simp [show k<d+1 by omega]

theorem twoSlice_collision (d k : ℕ) (hk : k<d) (a b : ℝ) :
    collision (radialLaw d (twoSliceWeights d k a b))=a^2+b^2/(Nat.choose d k:ℝ) := by
  classical
  rw [radialLaw_collision]
  have he (j : ℕ) : (twoSliceWeights d k a b j)^2/(Nat.choose d j:ℝ)=
      (if j=d then a^2 else 0)+(if j=k then b^2/(Nat.choose d k:ℝ) else 0) := by
    by_cases hjd : j=d
    · subst j
      simp [twoSliceWeights,Ne.symm (Nat.ne_of_lt hk)]
    · by_cases hjk : j=k
      · subst j
        simp [twoSliceWeights,Nat.ne_of_lt hk]
      · simp [twoSliceWeights,hjd,hjk]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp [show k<d+1 by omega]

theorem threeSlice_collision (d k : ℕ) (hk0 : 0<k) (hk : k<d) (a b c : ℝ) :
    collision (radialLaw d (threeSliceWeights d k a b c))=
      a^2+b^2+c^2/(Nat.choose d k:ℝ) := by
  classical
  rw [radialLaw_collision]
  have he (j : ℕ) : (threeSliceWeights d k a b c j)^2/(Nat.choose d j:ℝ)=
      (if j=0 then a^2 else 0)+(if j=d then b^2 else 0)+
        (if j=k then c^2/(Nat.choose d k:ℝ) else 0) := by
    by_cases hj0 : j=0
    · subst j
      simp [threeSliceWeights,show (0:ℕ)≠d by omega,show (0:ℕ)≠k by omega]
    · by_cases hjd : j=d
      · subst j
        simp [threeSliceWeights,show d≠0 by omega,Ne.symm (Nat.ne_of_lt hk)]
      · by_cases hjk : j=k
        · subst j
          simp [threeSliceWeights,show k≠0 by omega,Nat.ne_of_lt hk]
        · simp [threeSliceWeights,hj0,hjd,hjk]
  simp_rw [he]
  simp only [Finset.sum_add_distrib]
  simp [show k<d+1 by omega]

end
end EntropyDesigns.SymmetricEntropy
