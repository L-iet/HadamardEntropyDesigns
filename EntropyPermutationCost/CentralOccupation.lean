/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.CubeIsolation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.PermutationCost
open scoped BigOperators

 theorem positive_weight_point_below_average {α : Type*} [Fintype α]
    (w f : α → ℝ) (hw : ∀ x,0≤w x) (hm : ∑ x,w x=1)
    (a : ℝ) (ha : ∑ x,w x*f x=a) : ∃ x,0<w x ∧ f x≤a := by
  classical
  by_contra h
  have hlarge (x : α) (hx : 0<w x) : a<f x := by
    by_contra he
    exact h ⟨x,hx,le_of_not_gt he⟩
  have hg (x : α) : 0≤w x*(f x-a) := by
    by_cases hz : w x=0
    · simp [hz]
    · exact (mul_pos (lt_of_le_of_ne (hw x) (Ne.symm hz))
        (sub_pos.mpr (hlarge x (lt_of_le_of_ne (hw x) (Ne.symm hz))))).le
  obtain ⟨x,_,hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => hw x)).mp
    (show 0<∑ x,w x by rw [hm];norm_num)
  have hsum : 0<∑ y,w y*(f y-a) :=
    (Finset.sum_pos_iff_of_nonneg (fun y _ => hg y)).mpr
      ⟨x,Finset.mem_univ _,mul_pos hx (sub_pos.mpr (hlarge x hx))⟩
  simp_rw [mul_sub] at hsum
  rw [Finset.sum_sub_distrib,ha,←Finset.sum_mul,hm,one_mul] at hsum
  linarith

 theorem occupied_central_weight {N d : ℕ} (hd : 2≤d) (hN : 0<N)
    (rows : Fin N → Fin d → Bool) (hOA : IsBinaryStrengthTwo rows) :
    ∃ r : Fin N,(2*(hammingWeight (rows r):ℝ)-(d:ℝ))^2≤(d:ℝ) := by
  obtain ⟨hf,hp⟩ := strength_two_all_moments hd rows hOA
  obtain ⟨w,hw,hm,hmean,hpair,hsupp⟩ := cube_law_of_integer_array hN rows hf hp
  obtain ⟨h1,h2⟩ := hamming_moments w hm hmean hpair
  have hs : (∑ x,w x*(2*(hammingWeight x:ℝ)-(d:ℝ))^2)=(d:ℝ) := by
    have ht (x : Fin d → Bool) :
        w x*(2*(hammingWeight x:ℝ)-(d:ℝ))^2=
        4*(w x*(hammingWeight x:ℝ)^2)-4*(d:ℝ)*(w x*(hammingWeight x:ℝ))+
          (d:ℝ)^2*w x := by ring
    simp_rw [ht]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
      ←Finset.mul_sum,←Finset.mul_sum,h1,h2,hm]
    ring
  obtain ⟨x,hx,hbound⟩ := positive_weight_point_below_average w
    (fun x => (2*(hammingWeight x:ℝ)-(d:ℝ))^2) hw hm d hs
  obtain ⟨r,hr⟩ := hsupp x hx
  exact ⟨r,by simpa only [hr] using hbound⟩

end EntropyDesigns.PermutationCost
