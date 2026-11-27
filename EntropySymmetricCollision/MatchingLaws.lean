/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetricCollision.SliceMixtures
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

def IsSymmetricPairwiseLaw {d : ℕ} (w : (Fin d → Bool) → ℝ) : Prop :=
  (∀ x,0≤w x) ∧ (∑ x,w x=1) ∧ CoordinatePermutationInvariant w ∧
    (∀ i,∑ x,w x*(bitSign (x i):ℝ)=0) ∧
    (∀ i j,i≠j → ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)=0)

def oddSymmetricLaw (m : ℕ) : (Fin (2*m+1) → Bool) → ℝ :=
  radialLaw (2*m+1) (twoSliceWeights (2*m+1) m (1/(2*(m:ℝ)+2)) ((2*(m:ℝ)+1)/(2*(m:ℝ)+2)))

def evenSymmetricLaw (m : ℕ) : (Fin (2*m) → Bool) → ℝ :=
  radialLaw (2*m) (threeSliceWeights (2*m) m (1/(4*(m:ℝ))) (1/(4*(m:ℝ))) (1-1/(2*(m:ℝ))))

theorem oddSymmetricLaw_valid (m : ℕ) (hm : 1≤m) : IsSymmetricPairwiseLaw (oddSymmetricLaw m) := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<2*(m:ℝ)+2 := by linarith
  have hs : CoordinatePermutationInvariant (oddSymmetricLaw m) := radialLaw_symmetric _ _
  have hmass : (∑ x,oddSymmetricLaw m x)=1 := by
    have hh := twoSlice_moment (2*m+1) m (by omega)
      (1/(2*(m:ℝ)+2)) ((2*(m:ℝ)+1)/(2*(m:ℝ)+2)) (fun _ => 1)
    simp only [mul_one] at hh
    change (∑ x,radialLaw _ _ x)=1
    rw [hh]
    field_simp
    <;> ring
  have h1 : (∑ x,oddSymmetricLaw m x*(hammingWeight x:ℝ))=((2*m+1:ℕ):ℝ)/2 := by
    have hh := twoSlice_moment (2*m+1) m (by omega)
      (1/(2*(m:ℝ)+2)) ((2*(m:ℝ)+1)/(2*(m:ℝ)+2)) (fun k => (k:ℝ))
    change (∑ x,radialLaw _ _ x*(hammingWeight x:ℝ))=_
    rw [hh]
    push_cast
    field_simp
    <;> ring
  have h2 : (∑ x,oddSymmetricLaw m x*(hammingWeight x:ℝ)^2)=
      ((2*m+1:ℕ):ℝ)*(((2*m+1:ℕ):ℝ)+1)/4 := by
    have hh := twoSlice_moment (2*m+1) m (by omega)
      (1/(2*(m:ℝ)+2)) ((2*(m:ℝ)+1)/(2*(m:ℝ)+2)) (fun k => (k:ℝ)^2)
    change (∑ x,radialLaw _ _ x*(hammingWeight x:ℝ)^2)=_
    rw [hh]
    push_cast
    field_simp
    <;> ring
  refine ⟨radialLaw_nonneg _ _ (twoSliceWeights_nonneg _ _ (by positivity) (by positivity)),hmass,hs,?_⟩
  exact symmetric_hamming_moments_suffice (by omega) _ hmass hs h1 h2

theorem evenSymmetricLaw_valid (m : ℕ) (hm : 1≤m) : IsSymmetricPairwiseLaw (evenSymmetricLaw m) := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hs : CoordinatePermutationInvariant (evenSymmetricLaw m) := radialLaw_symmetric _ _
  have hcoef : 0≤1-1/(2*(m:ℝ)) := by
    have hh : (1:ℝ)/(2*(m:ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hmass : (∑ x,evenSymmetricLaw m x)=1 := by
    have hh := threeSlice_moment (2*m) m (by omega)
      (1/(4*(m:ℝ))) (1/(4*(m:ℝ))) (1-1/(2*(m:ℝ))) (fun _ => 1)
    simp only [mul_one] at hh
    change (∑ x,radialLaw _ _ x)=1
    rw [hh]
    field_simp
    <;> ring
  have h1 : (∑ x,evenSymmetricLaw m x*(hammingWeight x:ℝ))=((2*m:ℕ):ℝ)/2 := by
    have hh := threeSlice_moment (2*m) m (by omega)
      (1/(4*(m:ℝ))) (1/(4*(m:ℝ))) (1-1/(2*(m:ℝ))) (fun k => (k:ℝ))
    change (∑ x,radialLaw _ _ x*(hammingWeight x:ℝ))=_
    rw [hh]
    push_cast
    field_simp
    <;> ring
  have h2 : (∑ x,evenSymmetricLaw m x*(hammingWeight x:ℝ)^2)=
      ((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)+1)/4 := by
    have hh := threeSlice_moment (2*m) m (by omega)
      (1/(4*(m:ℝ))) (1/(4*(m:ℝ))) (1-1/(2*(m:ℝ))) (fun k => (k:ℝ)^2)
    change (∑ x,radialLaw _ _ x*(hammingWeight x:ℝ)^2)=_
    rw [hh]
    push_cast
    field_simp
    <;> ring
  refine ⟨radialLaw_nonneg _ _ (threeSliceWeights_nonneg _ _ (by positivity) (by positivity) hcoef),hmass,hs,?_⟩
  exact symmetric_hamming_moments_suffice (by omega) _ hmass hs h1 h2

theorem oddSymmetricLaw_collision (m : ℕ) : collision (oddSymmetricLaw m)=
    (1/(2*(m:ℝ)+2))^2+((2*(m:ℝ)+1)/(2*(m:ℝ)+2))^2/(Nat.choose (2*m+1) m:ℝ) :=
  twoSlice_collision _ _ (by omega) _ _

theorem evenSymmetricLaw_collision (m : ℕ) (hm : 1≤m) : collision (evenSymmetricLaw m)=
    2*(1/(4*(m:ℝ)))^2+(1-1/(2*(m:ℝ)))^2/(Nat.choose (2*m) m:ℝ) := by
  have hh := threeSlice_collision (2*m) m (by omega) (by omega)
    (1/(4*(m:ℝ))) (1/(4*(m:ℝ))) (1-1/(2*(m:ℝ)))
  simpa only [evenSymmetricLaw,two_mul] using hh

end
end EntropyDesigns.SymmetricEntropy
