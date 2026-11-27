/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetric.OrbitEntropy
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

def coordinateSpinSum {d : ℕ} (x : Fin d → Bool) : ℝ := ∑ i,(bitSign (x i):ℝ)

theorem coordinateSpinSum_perm {d : ℕ} (x : Fin d → Bool) (σ : Equiv.Perm (Fin d)) :
    coordinateSpinSum (fun i => x (σ i))=coordinateSpinSum x := by
  exact Equiv.sum_comp σ (fun i => (bitSign (x i):ℝ))

theorem weighted_permutation_sum {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hsym : CoordinatePermutationInvariant w) (σ : Equiv.Perm (Fin d))
    (f : (Fin d → Bool) → ℝ) :
    (∑ x,w x*f (fun i => x (σ i)))=∑ x,w x*f x := by
  classical
  let e := Equiv.arrowCongr σ.symm (Equiv.refl Bool)
  have he (x : Fin d → Bool) : e x=fun i => x (σ i) := rfl
  have hh := Equiv.sum_comp e (fun x => w x*f x)
  simp_rw [he,hsym σ] at hh
  exact hh

theorem symmetric_mean_equal {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hsym : CoordinatePermutationInvariant w) (i j : Fin d) :
    (∑ x,w x*(bitSign (x i):ℝ))=∑ x,w x*(bitSign (x j):ℝ) := by
  have hh := weighted_permutation_sum w hsym (Equiv.swap i j) (fun x => (bitSign (x i):ℝ))
  simpa using hh.symm

theorem symmetric_row_equal {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hsym : CoordinatePermutationInvariant w) (i j : Fin d) :
    (∑ x,w x*((bitSign (x i):ℝ)*coordinateSpinSum x))=
      ∑ x,w x*((bitSign (x j):ℝ)*coordinateSpinSum x) := by
  have hh := weighted_permutation_sum w hsym (Equiv.swap i j)
    (fun x => (bitSign (x i):ℝ)*coordinateSpinSum x)
  simpa only [Equiv.swap_apply_left,coordinateSpinSum_perm] using hh.symm

theorem symmetric_pair_equal_fixed {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hsym : CoordinatePermutationInvariant w) (i j k : Fin d) (hij : i≠j) (hik : i≠k) :
    (∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ))=
      ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x k):ℝ) := by
  have hh := weighted_permutation_sum w hsym (Equiv.swap j k)
    (fun x => (bitSign (x i):ℝ)*(bitSign (x j):ℝ))
  have hi : Equiv.swap j k i=i := Equiv.swap_apply_of_ne_of_ne hij hik
  simpa only [hi,Equiv.swap_apply_left,mul_assoc] using hh.symm

theorem symmetric_spin_moments_suffice {d : ℕ} (hd : 2≤d)
    (w : (Fin d → Bool) → ℝ) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hfirst : ∑ x,w x*coordinateSpinSum x=0)
    (hsecond : ∑ x,w x*(coordinateSpinSum x)^2=(d:ℝ)) :
    (∀ i,∑ x,w x*(bitSign (x i):ℝ)=0) ∧
      (∀ i j,i≠j → ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)=0) := by
  classical
  have hdR : (2:ℝ)≤d := by exact_mod_cast hd
  have hmeans (i : Fin d) : (∑ x,w x*(bitSign (x i):ℝ))=0 := by
    have he : (∑ j : Fin d,∑ x,w x*(bitSign (x j):ℝ))=0 := by
      rw [Finset.sum_comm]
      simpa only [coordinateSpinSum,Finset.mul_sum] using hfirst
    have hc (j : Fin d) := symmetric_mean_equal w hsym j i
    simp_rw [hc] at he
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
    nlinarith
  have hrows (i : Fin d) : (∑ x,w x*((bitSign (x i):ℝ)*coordinateSpinSum x))=1 := by
    have he : (∑ j : Fin d,∑ x,w x*((bitSign (x j):ℝ)*coordinateSpinSum x))=(d:ℝ) := by
      rw [Finset.sum_comm]
      have hx (x : Fin d → Bool) :
          (∑ j,w x*((bitSign (x j):ℝ)*coordinateSpinSum x))=w x*(coordinateSpinSum x)^2 := by
        simp only [mul_assoc,←Finset.sum_mul,←Finset.mul_sum,coordinateSpinSum]
        ring
      simp_rw [hx]
      exact hsecond
    have hc (j : Fin d) := symmetric_row_equal w hsym j i
    simp_rw [hc] at he
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
    nlinarith
  refine ⟨hmeans,?_⟩
  intro i j hij
  let c : ℝ := ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)
  have hp (k : Fin d) : (∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x k):ℝ))=if k=i then 1 else c := by
    by_cases hki : k=i
    · subst k
      have hx (x : Fin d → Bool) : w x*(bitSign (x i):ℝ)*(bitSign (x i):ℝ)=w x := by
        cases h : x i <;> simp [h,bitSign]
      simp_rw [hx]
      simp [hmass]
    · rw [if_neg hki]
      exact symmetric_pair_equal_fixed w hsym i k j (Ne.symm hki) hij
  have he : (∑ k : Fin d,if k=i then (1:ℝ) else c)=1 := by
    simp_rw [←hp]
    rw [Finset.sum_comm]
    have hx (x : Fin d → Bool) :
        (∑ k,w x*(bitSign (x i):ℝ)*(bitSign (x k):ℝ))=
          w x*((bitSign (x i):ℝ)*coordinateSpinSum x) := by
      simp only [←Finset.mul_sum,coordinateSpinSum]
      ring
    simp_rw [hx]
    exact hrows i
  have hsum : (∑ k : Fin d,if k=i then (1:ℝ) else c)=1+((d:ℝ)-1)*c := by
    have he (k : Fin d) : (if k=i then (1:ℝ) else c)=c+(if k=i then 1-c else 0) := by
      split_ifs <;> ring
    simp_rw [he]
    simp [Finset.sum_add_distrib]
    ring
  rw [hsum] at he
  change c=0
  nlinarith


theorem symmetric_hamming_moments_suffice {d : ℕ} (hd : 2≤d)
    (w : (Fin d → Bool) → ℝ) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hfirst : ∑ x,w x*(hammingWeight x:ℝ)=(d:ℝ)/2)
    (hsecond : ∑ x,w x*(hammingWeight x:ℝ)^2=(d:ℝ)*((d:ℝ)+1)/4) :
    (∀ i,∑ x,w x*(bitSign (x i):ℝ)=0) ∧
      (∀ i j,i≠j → ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)=0) := by
  have hx (x : Fin d → Bool) : coordinateSpinSum x=(d:ℝ)-2*(hammingWeight x:ℝ) := by
    have hh := hammingWeight_spin_sum x
    change 2*(hammingWeight x:ℝ)=(d:ℝ)-coordinateSpinSum x at hh
    linarith
  apply symmetric_spin_moments_suffice hd w hmass hsym
  · simp_rw [hx]
    have ht (x : Fin d → Bool) : w x*((d:ℝ)-2*(hammingWeight x:ℝ))=
        (d:ℝ)*w x-2*(w x*(hammingWeight x:ℝ)) := by ring
    simp_rw [ht]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,hmass,hfirst]
    ring
  · simp_rw [hx]
    have ht (x : Fin d → Bool) : w x*((d:ℝ)-2*(hammingWeight x:ℝ))^2=
        (d:ℝ)^2*w x-4*(d:ℝ)*(w x*(hammingWeight x:ℝ))+4*(w x*(hammingWeight x:ℝ)^2) := by ring
    simp_rw [ht]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,
      ←Finset.mul_sum,hmass,hfirst,hsecond]
    ring

end
end EntropyDesigns.SymmetricEntropy
