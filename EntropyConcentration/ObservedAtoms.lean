/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentration.PairKernelMoment
public import EntropySupportFace.SourceConsequences
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.Concentration
noncomputable section
open SupportFace

def observedAtoms {k s : ℕ} {i0 : Fin k} (p : SourceOutcome k s i0 → ℝ) :
    Finset (SourceOutcome k s i0) := Finset.univ.filter (fun y => p y≠0)

theorem atomSeed_exists {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hsupport : sourceSupported e i0 p) (a : observedAtoms p) :
    ∃ x : BlockSeeds k s,sourceCode e i0 x=a.val := by
  by_contra h
  exact (Finset.mem_filter.mp a.property).2 (hsupport a.val h)

def atomSeed {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hsupport : sourceSupported e i0 p) (a : observedAtoms p) :
    BlockSeeds k s := Classical.choose (atomSeed_exists e i0 p hsupport a)

theorem atomSeed_code {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hsupport : sourceSupported e i0 p) (a : observedAtoms p) :
    sourceCode e i0 (atomSeed e i0 p hsupport a)=a.val :=
  Classical.choose_spec (atomSeed_exists e i0 p hsupport a)

theorem atomSeed_active {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hsupport : sourceSupported e i0 p) (a : observedAtoms p) :
    sourcePullback e i0 p (atomSeed e i0 p hsupport a)≠0 := by
  change p (sourceCode e i0 (atomSeed e i0 p hsupport a))≠0
  rw [atomSeed_code]
  exact (Finset.mem_filter.mp a.property).2

theorem face_optimal_atoms_uniform {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2) :
    (observedAtoms p).card=(2^s)^2 ∧
      ∀ y,p y=if y∈observedAtoms p then 1/((observedAtoms p).card:ℝ) else 0 := by
  classical
  obtain ⟨hweights,hcard,_⟩ := source_collision_equality_oa hk e i0 p hp hsupport hcollision
  let E : observedAtoms p ≃ {y : SourceOutcome k s i0 // p y≠0} :=
    { toFun := fun y => ⟨y.val,(Finset.mem_filter.mp y.property).2⟩
      invFun := fun y => ⟨y.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,y.property⟩⟩
      left_inv := fun y => by apply Subtype.ext;rfl
      right_inv := fun y => by apply Subtype.ext;rfl }
  have hC : (observedAtoms p).card=(2^s)^2 := by
    calc
      _=Fintype.card {y : SourceOutcome k s i0 // p y≠0} := by simpa only [Fintype.card_coe] using Fintype.card_congr E
      _=(2^s)^2 := by simpa only [Nat.card_eq_fintype_card] using hcard
  refine ⟨hC,?_⟩
  intro y
  by_cases hy : p y=0
  · simp [observedAtoms,hy]
  · have hm : y∈observedAtoms p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩
    rw [if_pos hm,hC]
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using (hweights y).resolve_left hy

end
end EntropyDesigns.Concentration
