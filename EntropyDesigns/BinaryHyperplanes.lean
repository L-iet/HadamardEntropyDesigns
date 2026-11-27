module

public import EntropyDesigns.CharacterLevels
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Character levels are affine hyperplanes over the binary field -/

@[expose] public section
namespace EntropyDesigns

def binarySeed {d : ℕ} (x : Fin d → Bool) : Fin d → ZMod 2 :=
  fun i => if x i then 1 else 0

def maskFunctional {d : ℕ} (c : Finset (Fin d)) : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun z := ∑ i ∈ c, z i
  map_add' z w := by simp [Finset.sum_add_distrib]
  map_smul' a z := by simp [Finset.mul_sum]

theorem binaryField_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt := ZMod.val_lt a
  have hcases : a.val = 0 ∨ a.val = 1 := by omega
  rcases hcases with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    simpa [ZMod.val_one_eq_one_mod] using h

theorem binarySeed_bijective {d : ℕ} : Function.Bijective (@binarySeed d) := by
  constructor
  · intro x y h
    funext i
    have hi := congrFun h i
    cases hx : x i <;> cases hy : y i <;> simp_all [binarySeed]
  · intro z
    refine ⟨fun i => decide (z i = 1), ?_⟩
    funext i
    rcases binaryField_cases (z i) with h | h <;> simp [binarySeed, h]

theorem walshChar_binaryFunctional {d : ℕ} (c : Finset (Fin d)) (x : Fin d → Bool) :
    walshChar c x = if maskFunctional c (binarySeed x) = 0 then 1 else -1 := by
  classical
  induction c using Finset.induction_on with
  | empty => simp [walshChar, maskFunctional]
  | @insert j c hj ih =>
    have hchar : walshChar (insert j c) x = bitSign (x j) * walshChar c x := by
      simp [walshChar, hj]
    have hfunctional : maskFunctional (insert j c) (binarySeed x) =
        binarySeed x j + maskFunctional c (binarySeed x) := by
      simp [maskFunctional, hj]
    rw [hchar, ih, hfunctional]
    rcases binaryField_cases (maskFunctional c (binarySeed x)) with h | h <;>
      cases hx : x j <;> norm_num [binarySeed, bitSign, hx, h,
        show (1 : ZMod 2) + 1 = 0 by decide]

theorem characterLevel_linear_fiber {d : ℕ} (c : Finset (Fin d)) (x : Fin d → Bool) :
    (x ∈ characterLevel c 1 ↔ maskFunctional c (binarySeed x) = 0) ∧
    (x ∈ characterLevel c (-1) ↔ maskFunctional c (binarySeed x) = 1) := by
  classical
  simp only [characterLevel, Finset.mem_filter, Finset.mem_univ, true_and,
    walshChar_binaryFunctional]
  rcases binaryField_cases (maskFunctional c (binarySeed x)) with h | h <;> norm_num [h]

theorem maskFunctional_surjective {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty) :
    Function.Surjective (maskFunctional c) := by
  classical
  obtain ⟨j, hj⟩ := hc
  intro a
  refine ⟨fun i => if i = j then a else 0, ?_⟩
  simp [maskFunctional, hj]

theorem maskFunctional_nonzero {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty) :
    maskFunctional c ≠ 0 := by
  intro hzero
  obtain ⟨z, hz⟩ := maskFunctional_surjective c hc 1
  rw [hzero] at hz
  norm_num at hz

theorem maskFunctional_kernel_dimension {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty) :
    Module.finrank (ZMod 2) (LinearMap.ker (maskFunctional c)) = d - 1 := by
  have h := (maskFunctional c).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (maskFunctional_surjective c hc)] at h
  simp only [finrank_top, Module.finrank_self, Module.finrank_pi, Fintype.card_fin] at h
  omega

end EntropyDesigns
