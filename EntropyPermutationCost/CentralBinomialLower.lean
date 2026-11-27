/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPermutationCost.PermutationLayers
public import Mathlib.Data.Nat.Choose.Basic
@[expose] public section
namespace EntropyDesigns.PermutationCost
open scoped Classical

def IsCentralWeight (d k : ℕ) : Prop :=
  k≤d ∧ (2*(k:ℝ)-(d:ℝ))^2≤(d:ℝ)

 theorem central_weight_exists (d : ℕ) : ∃ k,IsCentralWeight d k := by
  refine ⟨d/2,Nat.div_le_self _ _,?_⟩
  obtain hm | hm := Nat.mod_two_eq_zero_or_one d
  · have he : d=2*(d/2) := by omega
    have heR : (d:ℝ)=2*((d/2:ℕ):ℝ) := by exact_mod_cast he
    rw [heR]
    nlinarith [Nat.cast_nonneg (d/2) (α:=ℝ)]
  · have he : d=2*(d/2)+1 := by omega
    have heR : (d:ℝ)=2*((d/2:ℕ):ℝ)+1 := by exact_mod_cast he
    rw [heR]
    nlinarith [Nat.cast_nonneg (d/2) (α:=ℝ)]

noncomputable def leastCentralWeight (d : ℕ) : ℕ := Nat.find (central_weight_exists d)

 theorem least_central_weight_spec (d : ℕ) : IsCentralWeight d (leastCentralWeight d) :=
  Nat.find_spec (central_weight_exists d)

 theorem least_central_weight_le {d k : ℕ} (hk : IsCentralWeight d k) :
    leastCentralWeight d≤k := Nat.find_min' (central_weight_exists d) hk

 theorem central_weight_reflection {d k : ℕ} (hk : IsCentralWeight d k) :
    IsCentralWeight d (d-k) := by
  refine ⟨Nat.sub_le _ _,?_⟩
  rw [Nat.cast_sub hk.1]
  have he : (2*((d:ℝ)-(k:ℝ))-(d:ℝ))^2=(2*(k:ℝ)-(d:ℝ))^2 := by ring
  rw [he]
  exact hk.2

 theorem choose_mono_below_middle (d a b : ℕ) (hab : a≤b) (hb : b≤d/2) :
    d.choose a≤d.choose b := by
  induction b generalizing a with
  | zero =>
    have he : a=0 := by omega
    subst a
    exact le_rfl
  | succ b ih =>
    by_cases he : a=b+1
    · subst a;exact le_rfl
    · exact (ih a (by omega) (by omega)).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))

 theorem central_binomial_lower {d k : ℕ} (hk : IsCentralWeight d k) :
    d.choose (leastCentralWeight d)≤d.choose k := by
  by_cases hmid : k≤d/2
  · exact choose_mono_below_middle d _ _ (least_central_weight_le hk) hmid
  · have hreflect := central_weight_reflection hk
    have hb : d-k≤d/2 := by omega
    have hh := choose_mono_below_middle d _ _ (least_central_weight_le hreflect) hb
    simpa only [Nat.choose_symm hk.1] using hh

 theorem symmetric_strength_two_exact_binomial_lower {N d : ℕ}
    (hd : 2≤d) (hN : 0<N) (rows : Fin N → Fin d → Bool)
    (hOA : IsBinaryStrengthTwo rows) (hsym : IsFullyPermutationSymmetric rows) :
    d.choose (leastCentralWeight d)≤N := by
  obtain ⟨k,hkd,hcentral,hbound⟩ := permutation_symmetric_central_layer_bound hd hN rows hOA hsym
  exact (central_binomial_lower ⟨hkd,hcentral⟩).trans hbound

end EntropyDesigns.PermutationCost
