/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentration.FaceInterpolation
public import EntropyConcentration.UnitInterpolation
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns.Concentration
noncomputable section
open SupportFace
open Interpolation
open scoped BigOperators

theorem face_optimum_barrier_bound {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) :
    ‖q-p‖≤outsideLawMass (observedAtoms p) q ∧
      collision q-1/((2:ℝ)^s)^2≤
        -2*outsideLawMass (observedAtoms p) q/((2:ℝ)^s)^2+
          (((2:ℝ)^s)^2+1)*(outsideLawMass (observedAtoms p) q)^2 := by
  classical
  let i : Fin k := ⟨0,by omega⟩
  let j : Fin k := ⟨1,by omega⟩
  have hij : i≠j := by intro h;have hv := congrArg Fin.val h;change 0=1 at hv;omega
  obtain ⟨L,hinterp,hbound,hmoment⟩ := face_optimum_interpolation hk e i0 p hp hsupport hcollision i j hij
  obtain ⟨hcard,hcanon⟩ := face_optimal_atoms_uniform hk e i0 p hp hsupport hcollision
  have hpos : 0<(observedAtoms p).card := by rw [hcard];positivity
  have hcardR : ((observedAtoms p).card:ℝ)=((2:ℝ)^s)^2 := by exact_mod_cast hcard
  obtain ⟨hnorm,hC⟩ := unit_interpolation_collision_bound (observedAtoms p) hpos p q L
    hcanon hp.2.1 hq.1 hq.2.1 hinterp hbound (hmoment q hq)
  rw [hcollision,hcardR] at hC
  have hb : 0≤outsideLawMass (observedAtoms p) q := Finset.sum_nonneg (fun y _ => hq.1 y)
  refine ⟨hnorm,?_⟩
  calc
    _≤outsideLawMass (observedAtoms p) q*
        (-2/((2:ℝ)^s)^2+(((2:ℝ)^s)^2+1)*‖q-p‖) := hC
    _≤outsideLawMass (observedAtoms p) q*
        (-2/((2:ℝ)^s)^2+(((2:ℝ)^s)^2+1)*outsideLawMass (observedAtoms p) q) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (-2/((2:ℝ)^s)^2)) (mul_le_mul_of_nonneg_left hnorm
          (show (0:ℝ)≤((2:ℝ)^s)^2+1 by positivity))) hb
    _=_ := by ring

theorem face_optimum_strict_local_collision {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2) :
    0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
      ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
        ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p := by
  classical
  let i : Fin k := ⟨0,by omega⟩
  let j : Fin k := ⟨1,by omega⟩
  have hij : i≠j := by intro h;have hv := congrArg Fin.val h;change 0=1 at hv;omega
  obtain ⟨L,hinterp,hbound,hmoment⟩ := face_optimum_interpolation hk e i0 p hp hsupport hcollision i j hij
  obtain ⟨hcard,hcanon⟩ := face_optimal_atoms_uniform hk e i0 p hp hsupport hcollision
  have hpos : 0<(observedAtoms p).card := by rw [hcard];positivity
  have hcardR : ((observedAtoms p).card:ℝ)=((2:ℝ)^s)^2 := by exact_mod_cast hcard
  refine ⟨by positivity,?_⟩
  intro q hq hqp hclose
  apply unit_interpolation_strict_radius (observedAtoms p) hpos p q L hcanon hp.2.1
    hq.1 hq.2.1 hinterp hbound (hmoment q hq) hqp
  simpa only [hcardR] using hclose

theorem face_optimum_path_barrier {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2)
    (path : ℝ → (SourceOutcome k s i0 → ℝ)) (hcont : ContinuousOn path (Set.Icc 0 1))
    (hstart : path 0=p) (hend : collision p<collision (path 1))
    (hlaw : ∀ t∈Set.Icc (0:ℝ) 1,sourceFeasible i0 (path t)) :
    ∃ t∈Set.Icc (0:ℝ) 1,collision (path t)≤
      1/((2:ℝ)^s)^2-1/((((2:ℝ)^s)^2)^2*(((2:ℝ)^s)^2+1)) := by
  classical
  let i : Fin k := ⟨0,by omega⟩
  let j : Fin k := ⟨1,by omega⟩
  have hij : i≠j := by intro h;have hv := congrArg Fin.val h;change 0=1 at hv;omega
  obtain ⟨L,hinterp,hbound,hmoment⟩ := face_optimum_interpolation hk e i0 p hp hsupport hcollision i j hij
  obtain ⟨hcard,hcanon⟩ := face_optimal_atoms_uniform hk e i0 p hp hsupport hcollision
  have hpos : 0<(observedAtoms p).card := by rw [hcard];positivity
  have hcardR : ((observedAtoms p).card:ℝ)=((2:ℝ)^s)^2 := by exact_mod_cast hcard
  have h := unit_interpolation_path_barrier (observedAtoms p) hpos p L hcanon hp.2.1
    hinterp hbound path hcont hstart hend (fun t ht =>
      ⟨(hlaw t ht).1,(hlaw t ht).2.1,hmoment (path t) (hlaw t ht)⟩)
  simpa only [hcollision,hcardR] using h

end
end EntropyDesigns.Concentration
