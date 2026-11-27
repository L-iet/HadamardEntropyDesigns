/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentration.StrictBarrier
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.Concentration
noncomputable section
open SupportFace Interpolation

theorem face_optimum_small_outside_collision {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q)
    (hb : 0<outsideLawMass (observedAtoms p) q)
    (hsmall : outsideLawMass (observedAtoms p) q<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1))) :
    collision q<collision p := by
  let m : ℝ := ((2:ℝ)^s)^2
  let b : ℝ := outsideLawMass (observedAtoms p) q
  have hm : 0<m := by dsimp [m];positivity
  have hbpos : 0<b := hb
  have hs : b<2/(m*(m+1)) := hsmall
  have hineq := (face_optimum_barrier_bound hk e i0 p hp hsupport hcollision q hq).2
  change collision q-1/m≤ -2*b/m+(m+1)*b^2 at hineq
  have hcancel : (m+1)*(2/(m*(m+1)))=2/m := by field_simp <;> ring
  have hscaled := mul_lt_mul_of_pos_left hs (show 0<m+1 by linarith)
  rw [hcancel] at hscaled
  have hneg : -2/m+(m+1)*b<0 := by rw [neg_div];linarith
  have hdrop := mul_neg_of_pos_of_neg hbpos hneg
  have hform : -2*b/m+(m+1)*b^2=b*(-2/m+(m+1)*b) := by ring
  rw [hform] at hineq
  rw [hcollision]
  change collision q<1/m
  linarith

theorem face_optimum_better_requires_outside_mass {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s))
    (i0 : Fin k) (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p)
    (hsupport : sourceSupported e i0 p) (hcollision : collision p=1/((2:ℝ)^s)^2)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) (hbetter : collision p<collision q) :
    2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1))≤outsideLawMass (observedAtoms p) q := by
  classical
  have hbnonneg : 0≤outsideLawMass (observedAtoms p) q := Finset.sum_nonneg (fun y _ => hq.1 y)
  have hbpos : 0<outsideLawMass (observedAtoms p) q := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) hbnonneg
    have hineq := (face_optimum_barrier_bound hk e i0 p hp hsupport hcollision q hq).2
    rw [hz] at hineq
    simp only [mul_zero,zero_mul,zero_div,zero_pow (by decide : 2≠0),add_zero] at hineq
    rw [hcollision] at hbetter
    linarith
  by_contra h
  have hsmall := lt_of_not_ge h
  have hdrop := face_optimum_small_outside_collision hk e i0 p hp hsupport hcollision q hq hbpos hsmall
  linarith

end
end EntropyDesigns.Concentration
