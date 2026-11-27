/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentration.ObservedAtoms
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.Concentration
noncomputable section
open SupportFace
open scoped BigOperators

theorem face_optimum_interpolation {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2) (i j : Fin k) (hij : i≠j) :
    ∃ L : observedAtoms p → SourceOutcome k s i0 → ℝ,
      (∀ a : observedAtoms p,∀ y∈observedAtoms p,L a y=if y=a.val then 1 else 0) ∧
      (∀ a y,|L a y|≤1) ∧
      (∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q →
        ∀ a,(∑ y,q y*L a y)=(∑ y,p y*L a y)) := by
  classical
  let L : observedAtoms p → SourceOutcome k s i0 → ℝ := fun a =>
    pairKernel i j ((atomSeed e i0 p hsupport a) i,(atomSeed e i0 p hsupport a) j)
  have hproj := (source_collision_equality_oa hk e i0 p hp hsupport hcollision).2.2 i j hij
  refine ⟨L,?_,?_,?_⟩
  · intro a y hy
    let b : observedAtoms p := ⟨y,hy⟩
    have ha := atomSeed_code e i0 p hsupport a
    have hb : sourceCode e i0 (atomSeed e i0 p hsupport b)=y := atomSeed_code e i0 p hsupport b
    have hiff : ((atomSeed e i0 p hsupport a) i,(atomSeed e i0 p hsupport a) j)=
        ((atomSeed e i0 p hsupport b) i,(atomSeed e i0 p hsupport b) j) ↔ y=a.val := by
      constructor
      · intro heq
        let aa : {x : BlockSeeds k s // sourcePullback e i0 p x≠0} :=
          ⟨atomSeed e i0 p hsupport a,atomSeed_active e i0 p hsupport a⟩
        let bb : {x : BlockSeeds k s // sourcePullback e i0 p x≠0} :=
          ⟨atomSeed e i0 p hsupport b,atomSeed_active e i0 p hsupport b⟩
        have hab : aa=bb := hproj.1 heq
        have hseed : atomSeed e i0 p hsupport a=atomSeed e i0 p hsupport b :=
          congrArg (fun z : {x : BlockSeeds k s // sourcePullback e i0 p x≠0} => z.val) hab
        exact hb.symm.trans ((congrArg (sourceCode e i0) hseed).symm.trans ha)
      · intro hya
        have hseed := sourceCode_injective e i0 ((ha.trans hya.symm).trans hb.symm)
        exact congrArg (fun x : BlockSeeds k s => (x i,x j)) hseed
    calc
      L a y=pairKernel i j ((atomSeed e i0 p hsupport a) i,(atomSeed e i0 p hsupport a) j)
        (sourceCode e i0 (atomSeed e i0 p hsupport b)) := by rw [hb]
      _=if ((atomSeed e i0 p hsupport a) i,(atomSeed e i0 p hsupport a) j)=
          ((atomSeed e i0 p hsupport b) i,(atomSeed e i0 p hsupport b) j) then 1 else 0 :=
        pairKernel_source e i0 i j _ _
      _=if y=a.val then 1 else 0 := by simp only [hiff]
  · intro a y
    exact pairKernel_bound i j _ y
  · intro q hq a
    let v : PairSeed s := ((atomSeed e i0 p hsupport a) i,(atomSeed e i0 p hsupport a) j)
    change (∑ y,q y*pairKernel i j v y)=(∑ y,p y*pairKernel i j v y)
    exact (pairKernel_moment i0 i j hij q hq v).trans (pairKernel_moment i0 i j hij p hp v).symm

end
end EntropyDesigns.Concentration
