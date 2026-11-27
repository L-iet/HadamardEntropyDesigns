/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.BinaryCharacters
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
@[expose] public section
namespace EntropyDesigns.SupportFace
noncomputable section

def boolBinaryEquiv (s : ℕ) : (Fin s → Bool) ≃ (Fin s → ZMod 2) :=
  Equiv.ofBijective binarySeed binarySeed_bijective

def fieldCoordinates (s : ℕ) (hs : s≠0) : GaloisField 2 s ≃ₗ[ZMod 2] (Fin s → ZMod 2) :=
  LinearEquiv.ofFinrankEq (R:=ZMod 2) (GaloisField 2 s) (Fin s → ZMod 2)
    (by rw [GaloisField.finrank 2 hs,Module.finrank_fin_fun])

def fieldSeedEquiv (s : ℕ) (hs : s≠0) : GaloisField 2 s ≃ (Fin s → Bool) :=
  (fieldCoordinates s hs).toEquiv.trans (boolBinaryEquiv s).symm

theorem binarySeed_fieldSeedEquiv (s : ℕ) (hs : s≠0) (a : GaloisField 2 s) :
    binarySeed (fieldSeedEquiv s hs a)=fieldCoordinates s hs a :=
  (boolBinaryEquiv s).apply_symm_apply _

def maskFieldFunctional {s : ℕ} (hs : s≠0) (S : Finset (Fin s)) :
    GaloisField 2 s →ₗ[ZMod 2] ZMod 2 :=
  (maskFunctional S).comp (fieldCoordinates s hs).toLinearMap

theorem maskFieldFunctional_nonzero {s : ℕ} (hs : s≠0) (S : Finset (Fin s)) (hS : S.Nonempty) :
    maskFieldFunctional hs S≠0 := by
  intro h
  apply maskFunctional_nonzero S hS
  apply LinearMap.ext
  intro z
  obtain ⟨a,ha⟩ := (fieldCoordinates s hs).surjective z
  have hv := LinearMap.congr_fun h a
  change maskFunctional S (fieldCoordinates s hs a)=0 at hv
  rw [ha] at hv
  exact hv

theorem field_seed_walsh_character {s : ℕ} (hs : s≠0) (S : Finset (Fin s)) (a : GaloisField 2 s) :
    (walshChar S (fieldSeedEquiv s hs a):ℝ)=binarySign (maskFieldFunctional hs S a) := by
  rw [walshChar_binaryFunctional,binarySeed_fieldSeedEquiv]
  by_cases h : maskFieldFunctional hs S a=0 <;>
    simp [binarySign,maskFieldFunctional] at h ⊢ <;> simp [h]
end
end EntropyDesigns.SupportFace
