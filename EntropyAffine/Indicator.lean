/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Weight
@[expose] public section
namespace EntropyDesigns
noncomputable section

theorem affine_support_card_options {r : ℕ} (hr : 0<r)
    (S : Finset (Finset (Fin r))) (hg : booleanSupportIndicator S∈lowDegreeBooleanCode r 1) :
    S.card=0 ∨ S.card=2^(r-1) ∨ S.card=2^r := by
  have hsum := affine_boolean_sign_sum (booleanSupportIndicator S) hg
  rw [booleanSupportIndicator_sign_sum] at hsum
  have hpow : (2 : ℤ)^r=2*(2 : ℤ)^(r-1) := by
    have he : r=(r-1)+1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ]
    ring
  rcases hsum with hsum|hsum|hsum
  · right; left
    have hh : (S.card : ℤ)=((2^(r-1) : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast hh
  · left
    have hh : (S.card : ℤ)=0 := by linarith
    exact_mod_cast hh
  · right; right
    have hh : (S.card : ℤ)=((2^r : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast hh

theorem residue_four_support_indicator_not_affine {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hres : S.card%8=4) :
    booleanSupportIndicator S∉lowDegreeBooleanCode r 1 := by
  intro hg
  have hfull : 8∣2^r := by
    have he : r=3+(r-3) := by omega
    rw [he,pow_add]
    change 8∣8*2^(r-3)
    exact dvd_mul_right 8 _
  have hhalf : 8∣2^(r-1) := by
    have he : r-1=3+(r-4) := by omega
    rw [he,pow_add]
    change 8∣8*2^(r-4)
    exact dvd_mul_right 8 _
  rcases affine_support_card_options (by omega) S hg with h|h|h
  · rw [h] at hres
    norm_num at hres
  · rw [h,Nat.mod_eq_zero_of_dvd hhalf] at hres
    norm_num at hres
  · rw [h,Nat.mod_eq_zero_of_dvd hfull] at hres
    norm_num at hres

end
end EntropyDesigns
