module

public import EntropyDesigns.UniformEquality

/-! # Exact finite pushforward of laws and moments -/

@[expose] public section
namespace EntropyDesigns

def pushLaw {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (w : α → ℝ) (b : β) : ℝ :=
  ∑ a, if f a = b then w a else 0

theorem pushLaw_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ∀ b, 0 ≤ pushLaw f w b := by
  intro b
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hw a
  · exact le_rfl

theorem pushLaw_mass {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (w : α → ℝ) :
    (∑ b, pushLaw f w b) = ∑ a, w a := by
  unfold pushLaw
  rw [Finset.sum_comm]
  simp

theorem pushLaw_moment {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (w : α → ℝ) (g : β → ℝ) :
    (∑ b, pushLaw f w b * g b) = ∑ a, w a * g (f a) := by
  unfold pushLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem pushLaw_injective_weights {α β : Type*}
    [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : α → ℝ) (c : ℝ)
    (huniform : ∀ a, w a = c) :
    ∀ b, pushLaw f w b = 0 ∨ pushLaw f w b = c := by
  classical
  intro b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, ha⟩ := h
    right
    unfold pushLaw
    rw [Finset.sum_eq_single a]
    · simp [ha, huniform]
    · intro a' _ hne
      have hnot : f a' ≠ b := fun h' => hne (hf (h'.trans ha.symm))
      simp [hnot]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ a))
  · left
    unfold pushLaw
    apply Finset.sum_eq_zero
    intro a _
    have hnot : f a ≠ b := fun h' => h ⟨a, h'⟩
    simp [hnot]

/-- Turn a finite injective sign frame with zero first and pair moments into
an actual Boolean-cube law, preserving its exact uniform entropy. -/
theorem cube_law_of_uniform_sign_frame {α : Type*} [Fintype α]
    {d : ℕ} (x : α → Fin d → ℤ) (hinj : Function.Injective x)
    (hsign : ∀ a i, x a i = 1 ∨ x a i = -1)
    (hcard : 0 < Fintype.card α)
    (hmean : ∀ i, ∑ a, (x a i : ℝ) = 0)
    (hpair : ∀ i j, i ≠ j → ∑ a, (x a i : ℝ) * (x a j : ℝ) = 0) :
    ∃ w : (Fin d → Bool) → ℝ,
      (∀ b, 0 ≤ w b) ∧ (∑ b, w b = 1) ∧
      (∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) ∧
      (∀ i j, i ≠ j →
        ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) ∧
      collision w = 1 / (Fintype.card α : ℝ) ∧
      collisionEntropy w = Real.log (Fintype.card α) ∧
      shannon w = Real.log (Fintype.card α) := by
  classical
  let code : α → Fin d → Bool := fun a i => decide (x a i = -1)
  have hcode : ∀ a i, bitSign (code a i) = x a i := by
    intro a i
    rcases hsign a i with h | h <;> simp [code, bitSign, h]
  have hcodeinj : Function.Injective code := by
    intro a b hab
    apply hinj
    funext i
    rw [← hcode a i, ← hcode b i, hab]
  let c : ℝ := 1 / (Fintype.card α : ℝ)
  let w := pushLaw code (fun _ => c)
  have hNR : (0 : ℝ) < Fintype.card α := by exact_mod_cast hcard
  have hc : 0 ≤ c := le_of_lt (div_pos zero_lt_one hNR)
  have hmass : ∑ b, w b = 1 := by
    rw [pushLaw_mass]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [c]
    exact mul_one_div_cancel hNR.ne'
  have huniform : ∀ b, w b = 0 ∨ w b = c :=
    pushLaw_injective_weights code hcodeinj (fun _ => c) c (fun _ => rfl)
  refine ⟨w, pushLaw_nonneg code _ (fun _ => hc), hmass, ?_, ?_,
    entropy_of_uniform_weights w hNR hmass huniform⟩
  · intro i
    calc
      ∑ b, w b * (bitSign (b i) : ℝ) =
          ∑ a, c * (x a i : ℝ) := by
        rw [pushLaw_moment]
        simp_rw [hcode]
      _ = c * (∑ a, (x a i : ℝ)) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hmean]; ring
  · intro i j hij
    calc
      ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) =
          ∑ b, w b * ((bitSign (b i) : ℝ) * (bitSign (b j) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ∑ a, c * ((x a i : ℝ) * (x a j : ℝ)) := by
        rw [pushLaw_moment]
        simp_rw [hcode]
      _ = c * (∑ a, (x a i : ℝ) * (x a j : ℝ)) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hpair i j hij]; ring

end EntropyDesigns
