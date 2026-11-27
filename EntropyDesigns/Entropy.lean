module

public import EntropyDesigns.ResidueBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Collision and Shannon entropy consequences of the sharp bound -/

@[expose] public section
namespace EntropyDesigns

noncomputable def shannon {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  -(∑ a, w a * Real.log (w a))

noncomputable def collisionEntropy {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  -Real.log (collision w)

theorem collision_pos {α : Type*} [Fintype α] (w : α → ℝ)
    (_hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) :
    0 < collision w := by
  classical
  have hex : ∃ a, 0 < w a := by
    by_contra h
    push Not at h
    have hs : (∑ a, w a) ≤ 0 := Finset.sum_nonpos fun a _ => h a
    linarith
  obtain ⟨a, ha⟩ := hex
  have hle : w a ^ 2 ≤ collision w :=
    Finset.single_le_sum (fun b _ => sq_nonneg (w b)) (Finset.mem_univ a)
  nlinarith

/-- Shannon entropy dominates collision entropy, including zero-weight atoms. -/
theorem shannon_ge_collision_entropy {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) :
    collisionEntropy w ≤ shannon w := by
  have hc := collision_pos w hw hmass
  have hterm : ∀ a, w a * Real.log (w a) ≤
      w a * Real.log (collision w) + w a * (w a / collision w - 1) := by
    intro a
    by_cases hz : w a = 0
    · simp [hz]
    · have hp : 0 < w a := lt_of_le_of_ne (hw a) (Ne.symm hz)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hp hc)
      rw [Real.log_div hp.ne' hc.ne'] at hlog
      have hm := mul_le_mul_of_nonneg_left hlog (hw a)
      nlinarith
  have hrest : (∑ a, w a * (w a / collision w - 1)) = 0 := by
    simp_rw [mul_sub, mul_one, ← mul_div_assoc, ← sq]
    rw [Finset.sum_sub_distrib]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    change collision w * (collision w)⁻¹ - (∑ a, w a) = 0
    rw [mul_inv_cancel₀ hc.ne', hmass, sub_self]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hterm a)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, one_mul, hrest, add_zero] at hs
  exact neg_le_neg hs

theorem log_entropy_of_collision_cap {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    {N : ℝ} (_hN : 0 < N) (hcap : collision w ≤ 1 / N) :
    Real.log N ≤ collisionEntropy w ∧ Real.log N ≤ shannon w := by
  have hc := collision_pos w hw hmass
  have hl := Real.log_le_log hc hcap
  have he : Real.log (1 / N) = -Real.log N := by simp [one_div]
  rw [he] at hl
  have hcollision : Real.log N ≤ collisionEntropy w := by
    unfold collisionEntropy
    linarith
  exact ⟨hcollision, hcollision.trans (shannon_ge_collision_entropy w hw hmass)⟩

/-- The complete sharp collision and Shannon entropy inequalities for finite
isotropic sign frames. Equality-to-Hadamard completion is a separate target. -/
theorem sharp_frame_entropy_bounds {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    collision w ≤ 1 / (roundedDimension n : ℝ) ∧
      Real.log (roundedDimension n) ≤ collisionEntropy w ∧
      Real.log (roundedDimension n) ≤ shannon w := by
  have hcap := sharp_frame_collision_bound hn A w hsign hw hmass hiso
  have hN : (0 : ℝ) < roundedDimension n := by
    have : 0 < roundedDimension n := by unfold roundedDimension; omega
    exact_mod_cast this
  exact ⟨hcap, log_entropy_of_collision_cap w hw hmass hN hcap⟩

end EntropyDesigns
