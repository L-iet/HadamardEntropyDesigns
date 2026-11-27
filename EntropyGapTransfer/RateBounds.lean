/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyGapTransfer.DyadicBuffer
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.GapTransfer
open Filter Asymptotics
open scoped Topology

theorem gap_rate_bounds (h k A : ℝ) (hh : 0<h) (ha : 0≤A)
    (hhalf : h/2<k) (hkh : k<h) (hlow : 2*A≤h-k) (hupp : h-k≤3*A) :
    (2*A/h≤1-k/h ∧ 1-k/h≤3*A/h) ∧
    (2*A/h^3≤1/(k*h)-1/h^2 ∧ 1/(k*h)-1/h^2≤6*A/h^3) ∧
    (2*h*A≤h^2-k*h ∧ h^2-k*h≤3*h*A) := by
  have hk : 0<k := by linarith
  have hg : 0≤h-k := by linarith
  have hrel : 1-k/h=(h-k)/h := by rw [sub_div,div_self hh.ne']
  have habs : 1/(k*h)-1/h^2=(h-k)/(k*h^2) := by
    field_simp <;> ring
  have hden : k*h^2≤h^3 := by
    have hm := mul_le_mul_of_nonneg_right hkh.le (sq_nonneg h)
    nlinarith
  have hden' : h^3/2≤k*h^2 := by
    have hm := mul_le_mul_of_nonneg_right hhalf.le (sq_nonneg h)
    nlinarith
  refine ⟨?_,⟨?_,?_⟩,?_,?_⟩
  · rw [hrel]
    exact ⟨div_le_div_of_nonneg_right hlow hh.le,div_le_div_of_nonneg_right hupp hh.le⟩
  · rw [habs]
    exact (div_le_div_of_nonneg_right hlow (pow_nonneg hh.le 3)).trans
      (div_le_div_of_nonneg_left hg (mul_pos hk (pow_pos hh 2)) hden)
  · rw [habs]
    calc
      (h-k)/(k*h^2) ≤ (h-k)/(h^3/2) :=
        div_le_div_of_nonneg_left hg (by positivity) hden'
      _ ≤ 3*A/(h^3/2) := div_le_div_of_nonneg_right hupp (by positivity)
      _ = 6*A/h^3 := by
        rw [div_div_eq_mul_div]
        congr 1
        ring
  · have hm := mul_le_mul_of_nonneg_left hlow hh.le
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hupp hh.le
    nlinarith

theorem isTheta_of_nonnegative_bounds (f g : ℕ → ℝ) (c C : ℝ) (hc : 0<c)
    (hg : ∀ i,0≤g i) (hlow : ∀ i,c*g i≤f i) (hupp : ∀ i,f i≤C*g i) :
    f =Θ[atTop] g := by
  have hf (i : ℕ) : 0≤f i := (mul_nonneg hc.le (hg i)).trans (hlow i)
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [] with i
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hf i),abs_of_nonneg (hg i)] using hupp i
  · apply Asymptotics.IsBigO.of_bound (1/c)
    filter_upwards [] with i
    have hh : g i≤f i/c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlow i)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hf i),abs_of_nonneg (hg i),
      one_div,div_eq_mul_inv,mul_one,mul_comm] using hh

end EntropyDesigns.GapTransfer
