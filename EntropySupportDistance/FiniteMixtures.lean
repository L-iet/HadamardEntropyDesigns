/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SourceDistanceLower
public import Mathlib.Analysis.Convex.Combination
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def finiteAverage {I A : Type*} [Fintype I] (q : I → A → ℝ) : A → ℝ :=
  fun x => ∑ i,(1/(Fintype.card I:ℝ))*q i x

theorem finiteAverage_mem_convexHull {I A : Type*} [Fintype I] [Nonempty I]
    (C : Set (A → ℝ)) (q : I → A → ℝ) (hq : ∀ i,q i∈C) : finiteAverage q∈convexHull ℝ C := by
  classical
  have hn : (Fintype.card I:ℝ)≠0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card I≠0)
  have hw : (∑ _i : I,(1/(Fintype.card I:ℝ)))=1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have h := (convex_convexHull ℝ C).sum_mem
    (t:=Finset.univ) (w:=fun _ : I => 1/(Fintype.card I:ℝ))
    (z:=q) (fun _ _ => by positivity) hw
    (fun i _ => subset_convexHull ℝ C (hq i))
  convert h using 1
  funext x
  simp [finiteAverage,Finset.sum_apply,smul_eq_mul]

theorem finiteAverage_probability {I A : Type*} [Fintype I] [Nonempty I] [Fintype A]
    (q : I → A → ℝ) (hq : ∀ i,(∀ x,0≤q i x) ∧ ∑ x,q i x=1) :
    (∀ x,0≤finiteAverage q x) ∧ ∑ x,finiteAverage q x=1 := by
  classical
  constructor
  · intro x
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (by positivity) ((hq i).1 x)
  · unfold finiteAverage
    rw [Finset.sum_comm]
    have he : (∑ i : I,∑ x : A,(1/(Fintype.card I:ℝ))*q i x)=
        ∑ _i : I,1/(Fintype.card I:ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [←Finset.mul_sum,(hq i).2,mul_one]
    rw [he]
    have hn : (Fintype.card I:ℝ)≠0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card I≠0)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp

theorem variation_of_scaled_support {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) (p q : A → ℝ) (beta : ℝ) (hbeta : beta≤1)
    (hp : ∀ x,0≤p x) (hq : ∀ x,0≤q x)
    (hpm : ∑ x,p x=1) (hqm : ∑ x,q x=1)
    (hsupport : ∀ x,x∉S → p x=0) (hscale : ∀ x,x∈S → q x=beta*p x) :
    totalVariation p q=1-beta := by
  classical
  have hpS : (∑ x∈S,p x)=1 := by
    rw [←hpm]
    exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hsupport x hx)
  have hqS : (∑ x∈S,q x)=beta := by
    calc
      _ = ∑ x∈S,beta*p x := Finset.sum_congr rfl (fun x hx => hscale x hx)
      _ = beta*(∑ x∈S,p x) := (Finset.mul_sum S p beta).symm
      _ = beta := by rw [hpS,mul_one]
  have habs (x : A) : |p x-q x|=p x+q x-2*(if x∈S then q x else 0) := by
    by_cases hx : x∈S
    · have hnon : 0≤p x-q x := by rw [hscale x hx];nlinarith [hp x]
      rw [abs_of_nonneg hnon]
      simp [hx]
      ring
    · rw [hsupport x hx]
      simp [hx,abs_of_nonneg (hq x)]
  unfold totalVariation
  simp_rw [habs]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hpm,hqm,←Finset.mul_sum]
  have hfilter : Finset.univ.filter (fun x : A => x∈S)=S := by ext x;simp
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,hfilter,hqS]
  ring

end
end EntropyDesigns.SupportFace
