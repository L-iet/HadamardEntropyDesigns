module

public import EntropyDesigns.MissingDirection
public import EntropyDesigns.Pushforward

/-! # Spanning binary observables preserve distinct seeds and collision -/

@[expose] public section
namespace EntropyDesigns

def seedDotFunctional {d : ℕ} (z : Fin d → ZMod 2) : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun a := ∑ i, a i * z i
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, mul_assoc]

theorem seedDotFunctional_mask {d : ℕ} (S : Finset (Fin d)) (z : Fin d → ZMod 2) :
    seedDotFunctional z (binarySeed (maskSeed S)) = maskFunctional S z := by
  simp [seedDotFunctional, binarySeed, maskSeed, maskFunctional]

theorem walshChar_eq_iff_binaryFunctional_eq {d : ℕ} (S : Finset (Fin d))
    (x y : Fin d → Bool) :
    walshChar S x = walshChar S y ↔ maskFunctional S (binarySeed x) = maskFunctional S (binarySeed y) := by
  rw [walshChar_binaryFunctional, walshChar_binaryFunctional]
  rcases binaryField_cases (maskFunctional S (binarySeed x)) with hx | hx <;>
    rcases binaryField_cases (maskFunctional S (binarySeed y)) with hy | hy <;> norm_num [hx, hy]

theorem spanning_characters_injective {d : ℕ} (B : Finset (Finset (Fin d)))
    (hspan : Submodule.span (ZMod 2)
      (Set.range (fun S : B => binarySeed (maskSeed S.val))) = ⊤) :
    Function.Injective (fun x : Fin d → Bool => fun S : B => walshChar S.val x) := by
  intro x y h
  let F := seedDotFunctional (binarySeed x - binarySeed y)
  have hkill : Submodule.span (ZMod 2)
      (Set.range (fun S : B => binarySeed (maskSeed S.val))) ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro v ⟨S, rfl⟩
    change seedDotFunctional (binarySeed x - binarySeed y) (binarySeed (maskSeed S.val)) = 0
    rw [seedDotFunctional_mask, map_sub]
    exact sub_eq_zero.mpr ((walshChar_eq_iff_binaryFunctional_eq S.val x y).mp (congrFun h S))
  rw [hspan] at hkill
  have hseed : binarySeed x = binarySeed y := by
    funext i
    have hzero : F (fun j => if j = i then 1 else 0) = 0 :=
      hkill (Submodule.mem_top)
    have hi : binarySeed x i - binarySeed y i = 0 := by
      simpa [F, seedDotFunctional] using hzero
    exact sub_eq_zero.mp hi
  exact binarySeed_bijective.1 hseed

def characterCode {d : ℕ} (B : Finset (Finset (Fin d))) (x : Fin d → Bool) : B → Bool :=
  fun S => decide (walshChar S.val x = -1)

theorem characterCode_sign {d : ℕ} (B : Finset (Finset (Fin d))) (x : Fin d → Bool) (S : B) :
    bitSign (characterCode B x S) = walshChar S.val x := by
  rcases walshChar_sign S.val x with h | h <;> norm_num [characterCode, bitSign, h]

theorem characterCode_injective {d : ℕ} (B : Finset (Finset (Fin d)))
    (hspan : Submodule.span (ZMod 2)
      (Set.range (fun S : B => binarySeed (maskSeed S.val))) = ⊤) :
    Function.Injective (characterCode B) := by
  intro x y h
  apply spanning_characters_injective B hspan
  funext S
  change walshChar S.val x = walshChar S.val y
  rw [← characterCode_sign B x S, ← characterCode_sign B y S, congrFun h S]

theorem pushLaw_injective_value {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : α → ℝ) (a : α) :
    pushLaw f w (f a) = w a := by
  classical
  simp [pushLaw, hf.eq_iff]

theorem pushLaw_injective_collision {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : α → ℝ) : collision (pushLaw f w) = collision w := by
  have h := pushLaw_moment f w (pushLaw f w)
  simp only [pushLaw_injective_value f hf w, ← pow_two] at h
  exact h

theorem characterCode_collision {d : ℕ} (B : Finset (Finset (Fin d)))
    (hspan : Submodule.span (ZMod 2)
      (Set.range (fun S : B => binarySeed (maskSeed S.val))) = ⊤)
    (w : (Fin d → Bool) → ℝ) : collision (pushLaw (characterCode B) w) = collision w := by
  classical
  exact pushLaw_injective_collision _ (characterCode_injective B hspan) w

end EntropyDesigns
