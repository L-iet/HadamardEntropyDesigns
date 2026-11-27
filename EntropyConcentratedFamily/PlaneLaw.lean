/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentratedFamily.FiniteFieldSupports
public import EntropySupportFace.FieldAttainment
public import EntropyDesigns.WalshSubset
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace
open scoped BigOperators

theorem plane_uniform_feasible {k s : ℕ} (hk : 2≤k) (hs : s≠0) (e : Finset (Fin s))
    (he : e.Nonempty) (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    sourceFeasible i0 (uniformFiniteLaw (planeSupport hs e i0 t)) := by
  classical
  let F := GaloisField 2 s
  letI : Fintype F := Fintype.ofFinite F
  let f : F × F → SourceOutcome k s i0 := fun z => sourceCode e i0 (fieldSlopeSeeds hs t z)
  let w : F × F → ℝ := fun _ => 1/(Fintype.card (F × F):ℝ)
  let q := pushLaw f w
  have hm := uniform_binary_character_moments (fieldObservable hs e i0 t)
    (fieldObservable_nonzero hs e he i0 t ht) (fieldObservable_injective hs e he i0 t ht)
  have hsign (z : F × F) (c : SourceCoordinate k s i0) :
      (bitSign (f z c):ℝ)=binarySign (fieldObservable hs e i0 t c z) := by
    change (bitSign (sourceCode e i0 (fieldSlopeSeeds hs t z) c):ℝ)=_
    rw [sourceCode_sign]
    exact fieldObservable_character hs e i0 t z c
  have hf : Function.Injective f := (sourceCode_injective e i0).comp (fieldSlopeSeeds_injective hk hs t ht)
  have hfeasible : sourceFeasible i0 q := by
    refine ⟨pushLaw_nonneg f w hm.1,(pushLaw_mass f w).trans hm.2.1,?_,?_⟩
    · intro c
      have hp := pushLaw_moment (α:=F × F) (β:=SourceOutcome k s i0) f w (fun y => (bitSign (y c):ℝ))
      change (∑ y,pushLaw f w y*(bitSign (y c):ℝ))=0
      rw [hp]
      simpa only [hsign,w] using hm.2.2.1 c
    · intro c d hcd
      have hp := pushLaw_moment (α:=F × F) (β:=SourceOutcome k s i0) f w
        (fun y => (bitSign (y c):ℝ)*(bitSign (y d):ℝ))
      change (∑ y,pushLaw f w y*(bitSign (y c):ℝ)*(bitSign (y d):ℝ))=0
      simp only [mul_assoc]
      rw [hp]
      simpa only [hsign,w,mul_assoc] using hm.2.2.2 c d hcd
  have hFcard : Fintype.card F=2^s := by
    simpa only [Nat.card_eq_fintype_card] using (GaloisField.card (p:=2) (n:=s) hs)
  have hPcard : Fintype.card (F × F)=(2^s)^2 := by simp [hFcard,pow_two]
  have heq : q=uniformFiniteLaw (planeSupport hs e i0 t) := by
    funext y
    by_cases hy : y∈planeSupport hs e i0 t
    · obtain ⟨z,hz⟩ := (mem_planeSupport hs e i0 t y).mp hy
      have hfy : f z=y := hz
      calc
        q y=q (f z) := by rw [hfy]
        _=w z := pushLaw_injective_value f hf w z
        _=uniformFiniteLaw (planeSupport hs e i0 t) y := by
          simp only [w,uniformFiniteLaw,hy,ite_true,planeSupport_card hk hs e i0 t ht,hPcard]
    · have hzero : pushLaw f w y=0 := by
        unfold pushLaw
        apply Finset.sum_eq_zero
        intro z _
        have hn : f z≠y := by
          intro h
          exact hy ((mem_planeSupport hs e i0 t y).mpr ⟨z,h⟩)
        simp only [hn,ite_false]
      simpa only [uniformFiniteLaw,hy,ite_false] using hzero
  rw [←heq]
  exact hfeasible

theorem plane_uniform_source_supported {k s : ℕ} (hs : s≠0) (e : Finset (Fin s))
    (i0 : Fin k) (t : Fin k → GaloisField 2 s) :
    sourceSupported e i0 (uniformFiniteLaw (planeSupport hs e i0 t)) := by
  classical
  intro y hy
  have hn : y∉planeSupport hs e i0 t := by
    intro hm
    obtain ⟨z,hz⟩ := (mem_planeSupport hs e i0 t y).mp hm
    exact hy ⟨fieldSlopeSeeds hs t z,hz⟩
  simp [uniformFiniteLaw,hn]

theorem plane_uniform_collision {k s : ℕ} (hk : 2≤k) (hs : s≠0) (e : Finset (Fin s))
    (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    collision (uniformFiniteLaw (planeSupport hs e i0 t))=1/((2:ℝ)^s)^2 := by
  have hpos : 0<(planeSupport hs e i0 t).card := by rw [planeSupport_card hk hs e i0 t ht];positivity
  rw [uniformFiniteLaw_collision _ hpos,planeSupport_card hk hs e i0 t ht]
  simp

end
end EntropyDesigns.ConcentratedFamily
