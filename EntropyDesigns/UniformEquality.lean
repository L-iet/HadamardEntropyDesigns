module

public import EntropyDesigns.SignLaws

/-! # Uniformity in saturated nonnegative moment bounds -/

@[expose] public section
namespace EntropyDesigns

/-- Equality in a diagonal kernel estimate, when every row has the same
weighted moment, forces every positive atom to have the same weight. -/
theorem uniform_of_saturated_kernel {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) (d k : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hP : ∀ a b, 0 ≤ P a b)
    (hd : 0 < d) (hdiag : ∀ a, P a a = d)
    (hmoment : ∀ a, ∑ b, w b * P a b = k)
    (heq : collision w = k / d) :
    ∀ a, w a = 0 ∨ w a = k / d := by
  have hcap : ∀ a, w a ≤ k / d := by
    intro a
    apply (le_div_iff₀ hd).2
    calc
      w a * d = w a * P a a := by rw [hdiag]
      _ ≤ ∑ b, w b * P a b :=
        Finset.single_le_sum (fun b _ => mul_nonneg (hw b) (hP a b))
          (Finset.mem_univ a)
      _ = k := hmoment a
  exact equality_forces_capped_weights w (k / d) hw hmass hcap heq

/-- Saturation of the odd-dimensional bound forces uniform positive weights. -/
theorem uniform_of_saturated_supported_kernel {α : Type*}
    [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) (d k : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hP : ∀ a b, 0 ≤ P a b) (hd : 0 < d)
    (hdiag : ∀ a, P a a = d)
    (hmoment : ∀ a, w a ≠ 0 → ∑ b, w b * P a b = k)
    (heq : collision w = k / d) :
    ∀ a, w a = 0 ∨ w a = k / d := by
  have hcap : ∀ a, w a ≤ k / d := by
    intro a
    by_cases ha : w a = 0
    · rw [ha, ← heq]
      exact Finset.sum_nonneg (fun a _ => sq_nonneg (w a))
    · apply (le_div_iff₀ hd).2
      calc
        w a * d = w a * P a a := by rw [hdiag]
        _ ≤ ∑ b, w b * P a b :=
          Finset.single_le_sum (fun b _ => mul_nonneg (hw b) (hP a b))
            (Finset.mem_univ a)
        _ = k := hmoment a ha
  exact equality_forces_capped_weights w (k / d) hw hmass hcap heq

/-- Saturation of the odd-dimensional bound forces uniform positive weights. -/
theorem odd_frame_equality_uniform {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (heq : collision w = 1 / ((n : ℝ) + 1)) :
    ∀ a, w a = 0 ∨ w a = 1 / ((n : ℝ) + 1) := by
  let P := fun a b => (intInner A a b : ℝ) ^ 2 - 1
  have hP : ∀ a b, 0 ≤ P a b := by
    intro a b
    have hint := odd_sign_sum_square_ge_one Finset.univ
      (fun i => A a i * A b i) (inner_product_signs A hsign a b) (by simpa using hodd)
    have hr : (1 : ℝ) ≤ (intInner A a b : ℝ) ^ 2 := by exact_mod_cast hint
    exact sub_nonneg.mpr hr
  have hd : ∀ a, P a a = (n : ℝ) ^ 2 - 1 := by
    intro a
    simp [P, intInner_diag A hsign]
  have hm : ∀ a, ∑ b, w b * P a b = (n : ℝ) - 1 := by
    intro a
    dsimp [P]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, pointwise_intInner_moment A w hsign hiso a]
    simpa using congrArg (fun r : ℝ => (n : ℝ) - r) hmass
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hfactor : ((n : ℝ) - 1) / ((n : ℝ) ^ 2 - 1) = 1 / ((n : ℝ) + 1) := by
    apply (div_eq_div_iff (by nlinarith) (by linarith)).2
    ring
  have h := uniform_of_saturated_kernel w P ((n : ℝ) ^ 2 - 1) ((n : ℝ) - 1)
    hw hmass hP (by nlinarith) hd hm (by rw [hfactor]; exact heq)
  simpa only [hfactor] using h

/-- Saturation in dimension two modulo four also forces uniform weights. -/
theorem residue_two_frame_equality_uniform {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 2 < n) (hres : n % 4 = 2)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (heq : collision w = 1 / ((n : ℝ) + 2)) :
    ∀ a, w a = 0 ∨ w a = 1 / ((n : ℝ) + 2) := by
  let ε := fun a => (intParity A a : ℝ)
  let P := fun a b => ((intInner A a b : ℝ) ^ 2 - 2) - 2 * (ε a * ε b)
  have hε : ∀ a, ε a ^ 2 = 1 := by
    intro a
    rcases intParity_sign A hsign a with h | h <;> simp [ε, h]
  have hP : ∀ a b, 0 ≤ P a b := by
    intro a b
    have hint := residue_two_sign_square_lower Finset.univ
      (fun i => A a i * A b i) (inner_product_signs A hsign a b) (by simpa using hres)
    simp only [parity_product] at hint
    change (2 : ℤ) + 2 * (intParity A a * intParity A b) ≤ intInner A a b ^ 2 at hint
    have hr : (2 : ℝ) + 2 * (ε a * ε b) ≤ (intInner A a b : ℝ) ^ 2 := by
      dsimp [ε]
      exact_mod_cast hint
    dsimp [P]
    linarith
  have hd : ∀ a, P a a = (n : ℝ) ^ 2 - 4 := by
    intro a
    dsimp [P]
    rw [intInner_diag A hsign]
    simp only [Int.cast_natCast]
    nlinarith [hε a]
  have hm : weightedTotal w (fun a b => (intInner A a b : ℝ) ^ 2) = n :=
    weightedTotal_of_pointwise_moment w _ _ hmass
      (pointwise_intInner_moment A w hsign hiso)
  have hp : weightedTotal w P =
      (n : ℝ) - 2 - 2 * (∑ a, w a * ε a) ^ 2 := by
    dsimp [P]
    rw [weightedTotal_sub, weightedTotal_sub, weightedTotal_smul,
      hm, weightedTotal_const w hmass, weightedTotal_rank_one]
  have hb := weighted_diagonal_lower w P ((n : ℝ) ^ 2 - 4) hw hP hd
  rw [hp, heq] at hb
  have hnR : (2 : ℝ) < n := by exact_mod_cast hn
  have hfactor : (1 / ((n : ℝ) + 2)) * ((n : ℝ) ^ 2 - 4) = n - 2 := by
    apply (mul_left_cancel₀ (by linarith : (n : ℝ) + 2 ≠ 0))
    field_simp
    ring
  have hfactor' : ((n : ℝ) - 2) / ((n : ℝ) ^ 2 - 4) = 1 / ((n : ℝ) + 2) := by
    apply (div_eq_div_iff (by nlinarith) (by linarith)).2
    ring
  have hmean : (∑ a, w a * ε a) = 0 := by
    rw [hfactor] at hb
    nlinarith [sq_nonneg (∑ a, w a * ε a)]
  have hpoint : ∀ a, ∑ b, w b * P a b = (n : ℝ) - 2 := by
    intro a
    have hzero : ∑ b, w b * (2 * (ε a * ε b)) = 0 := by
      calc
        _ = (2 * ε a) * (∑ b, w b * ε b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = 0 := by rw [hmean, mul_zero]
    have hconst : (∑ b, w b * 2) = 2 := by rw [← Finset.sum_mul, hmass, one_mul]
    dsimp [P]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      pointwise_intInner_moment A w hsign hiso a, hconst, hzero, sub_zero]
  have h := uniform_of_saturated_kernel w P ((n : ℝ) ^ 2 - 4) ((n : ℝ) - 2)
    hw hmass hP (by nlinarith) hd hpoint (by rw [hfactor']; exact heq)
  simpa only [hfactor'] using h

theorem residue_one_frame_equality_uniform {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (heq : collision w = 1 / ((n : ℝ) + 3)) :
    ∀ a, w a = 0 ∨ w a = 1 / ((n : ℝ) + 3) := by
  let ε := fun a => (intParity A a : ℝ)
  let v := fun a i => (A a i : ℝ)
  let P := fun a b => ((intInner A a b : ℝ) ^ 2 +
    2 * (ε a * ε b * (intInner A a b : ℝ))) - 3
  have hε : ∀ a, ε a ^ 2 = 1 := by
    intro a
    rcases intParity_sign A hsign a with h | h <;> simp [ε, h]
  have hP : ∀ a b, 0 ≤ P a b := by
    intro a b
    have hq := switched_sign_sum_mod_four Finset.univ
      (fun i => A a i * A b i) (inner_product_signs A hsign a b) (by simpa using hres)
    have hint := residue_one_polynomial_nonneg _ hq
    simp only [parity_product] at hint
    change (0 : ℤ) ≤ (intParity A a * intParity A b * intInner A a b) ^ 2 +
      2 * (intParity A a * intParity A b * intInner A a b) - 3 at hint
    have hr : (0 : ℝ) ≤ (ε a * ε b * (intInner A a b : ℝ)) ^ 2 +
        2 * (ε a * ε b * (intInner A a b : ℝ)) - 3 := by
      dsimp [ε]
      exact_mod_cast hint
    have hq2 : (ε a * ε b * (intInner A a b : ℝ)) ^ 2 =
        (intInner A a b : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, hε a, hε b]
      ring
    rw [hq2] at hr
    exact hr
  have hd : ∀ a, P a a = (n : ℝ) ^ 2 + 2 * n - 3 := by
    intro a
    dsimp [P]
    rw [intInner_diag A hsign]
    simp only [Int.cast_natCast]
    have hs : ε a * ε a = 1 := by nlinarith [hε a]
    rw [hs]
    ring
  have hm : weightedTotal w (fun a b => (intInner A a b : ℝ) ^ 2) = n :=
    weightedTotal_of_pointwise_moment w _ _ hmass
      (pointwise_intInner_moment A w hsign hiso)
  have ht : weightedTotal w (fun a b => ε a * ε b * (intInner A a b : ℝ)) =
      ∑ i, projectionCoefficients w ε v i ^ 2 := by
    simp_rw [intInner_cast]
    exact weighted_twisted_inner w ε v
  have hp : weightedTotal w P =
      (n : ℝ) + 2 * (∑ i, projectionCoefficients w ε v i ^ 2) - 3 := by
    dsimp [P]
    rw [weightedTotal_sub, weightedTotal_add, weightedTotal_smul,
      hm, ht, weightedTotal_const w hmass]
  have hbessel := bessel_of_coordinate_isotropy w ε v hw hiso
  have hεmass : ∑ a, w a * ε a ^ 2 = 1 := by
    simp_rw [hε, mul_one]
    exact hmass
  rw [hεmass] at hbessel
  have hb := weighted_diagonal_lower w P ((n : ℝ) ^ 2 + 2 * n - 3) hw hP hd
  rw [hp] at hb
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hfactor : (1 / ((n : ℝ) + 3)) * ((n : ℝ) ^ 2 + 2 * n - 3) = n - 1 := by
    apply (mul_left_cancel₀ (by linarith : (n : ℝ) + 3 ≠ 0))
    field_simp
    ring
  rw [heq, hfactor] at hb
  have hnorm : (∑ i, projectionCoefficients w ε v i ^ 2) = 1 := by linarith
  have hsupport := bessel_equality_on_support w ε v hw hiso
    (by rw [hεmass]; exact hnorm)
  have hpoint : ∀ a, w a ≠ 0 → ∑ b, w b * P a b = (n : ℝ) - 1 := by
    intro a ha
    have htwist : (∑ b, w b * (ε a * ε b * (intInner A a b : ℝ))) = 1 := by
      simp_rw [intInner_cast]
      rw [pointwise_twisted_inner w ε v a, ← hsupport a ha]
      nlinarith [hε a]
    have htwo : (∑ b, w b * (2 * (ε a * ε b * (intInner A a b : ℝ)))) = 2 := by
      calc
        _ = 2 * (∑ b, w b * (ε a * ε b * (intInner A a b : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = 2 := by rw [htwist]; ring
    have hconst : (∑ b, w b * 3) = 3 := by rw [← Finset.sum_mul, hmass, one_mul]
    dsimp [P]
    simp_rw [mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      pointwise_intInner_moment A w hsign hiso a, htwo, hconst]
    ring
  have hfactor' : ((n : ℝ) - 1) / ((n : ℝ) ^ 2 + 2 * n - 3) =
      1 / ((n : ℝ) + 3) := by
    apply (div_eq_div_iff (by nlinarith) (by linarith)).2
    ring
  have h := uniform_of_saturated_supported_kernel w P
    ((n : ℝ) ^ 2 + 2 * n - 3) ((n : ℝ) - 1)
    hw hmass hP (by nlinarith) hd hpoint (by rw [hfactor']; exact heq)
  simpa only [hfactor'] using h

/-- In every residue class, saturation forces equal nonzero weights. -/
theorem sharp_frame_equality_uniform {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (heq : collision w = 1 / (roundedDimension n : ℝ)) :
    ∀ a, w a = 0 ∨ w a = 1 / (roundedDimension n : ℝ) := by
  have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · have hdim : roundedDimension n = n := by unfold roundedDimension; omega
    rw [hdim] at heq ⊢
    apply equality_forces_capped_weights w _ hw hmass _ heq
    apply atom_bound_of_moment n (by omega) w (fun a b => (intInner A a b : ℝ)) hw
    · intro a
      simp [intInner_diag A hsign]
    · exact pointwise_intInner_moment A w hsign hiso
  · have hdim : roundedDimension n = n + 3 := by unfold roundedDimension; omega
    simp only [hdim, Nat.cast_add, Nat.cast_ofNat] at heq ⊢
    exact residue_one_frame_equality_uniform (by omega) h A w hsign hw hmass hiso heq
  · have hdim : roundedDimension n = n + 2 := by unfold roundedDimension; omega
    simp only [hdim, Nat.cast_add, Nat.cast_ofNat] at heq ⊢
    exact residue_two_frame_equality_uniform (by omega) h A w hsign hw hmass hiso heq
  · have hdim : roundedDimension n = n + 1 := by unfold roundedDimension; omega
    simp only [hdim, Nat.cast_add, Nat.cast_one] at heq ⊢
    exact odd_frame_equality_uniform (by omega) (by omega) A w hsign hw hmass hiso heq

/-- Uniform nonzero weights in a probability law determine its exact support. -/
theorem support_card_of_uniform_weights {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (N : ℕ) (hN : 0 < N) (hmass : ∑ a, w a = 1)
    (huniform : ∀ a, w a = 0 ∨ w a = 1 / (N : ℝ)) :
    (Finset.univ.filter (fun a => w a ≠ 0)).card = N := by
  classical
  let s := Finset.univ.filter (fun a => w a ≠ 0)
  have hsum : ∑ a ∈ s, w a = 1 := by
    calc
      ∑ a ∈ s, w a = ∑ a, w a := by
        dsimp [s]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : w a = 0 <;> simp [ha]
      _ = 1 := hmass
  have hvalue : (∑ a ∈ s, w a) = (s.card : ℝ) * (1 / (N : ℝ)) := by
    calc
      ∑ a ∈ s, w a = ∑ _a ∈ s, (1 / (N : ℝ)) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hne : w a ≠ 0 := (Finset.mem_filter.mp ha).2
        exact (huniform a).resolve_left hne
      _ = _ := by simp
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hratio : (s.card : ℝ) / N = 1 := by
    rw [div_eq_mul_one_div]
    rw [← hvalue, hsum]
  have hcard : (s.card : ℝ) = (N : ℝ) := (div_eq_one_iff_eq hNR).mp hratio
  exact_mod_cast hcard

/-- An equality frame has exactly the rounded number of nonzero atoms. -/
theorem sharp_frame_equality_support_card {α : Type*}
    [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (heq : collision w = 1 / (roundedDimension n : ℝ)) :
    (Finset.univ.filter (fun a => w a ≠ 0)).card = roundedDimension n := by
  apply support_card_of_uniform_weights w (roundedDimension n) _ hmass
    (sharp_frame_equality_uniform hn A w hsign hw hmass hiso heq)
  unfold roundedDimension
  omega

/-- Attaining the sharp Shannon bound also attains the collision bound. -/
theorem shannon_equality_forces_collision_equality {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    {N : ℝ} (hN : 0 < N) (hcap : collision w ≤ 1 / N)
    (heq : shannon w = Real.log N) :
    collision w = 1 / N := by
  have hc := collision_pos w hw hmass
  have hlower := (log_entropy_of_collision_cap w hw hmass hN hcap).1
  have hupper := shannon_ge_collision_entropy w hw hmass
  rw [heq] at hupper
  have he : collisionEntropy w = Real.log N := le_antisymm hupper hlower
  apply Real.log_injOn_pos hc (div_pos zero_lt_one hN)
  rw [show Real.log (1 / N) = -Real.log N by simp [one_div]]
  unfold collisionEntropy at he
  linarith

/-- Equal nonzero atom weights determine both entropy values exactly. -/
theorem entropy_of_uniform_weights {α : Type*} [Fintype α]
    (w : α → ℝ) {N : ℝ} (_hN : 0 < N) (hmass : ∑ a, w a = 1)
    (huniform : ∀ a, w a = 0 ∨ w a = 1 / N) :
    collision w = 1 / N ∧ collisionEntropy w = Real.log N ∧
      shannon w = Real.log N := by
  have hcollision : collision w = 1 / N := by
    unfold collision
    calc
      ∑ a, w a ^ 2 = ∑ a, w a * (1 / N) := by
        apply Finset.sum_congr rfl
        intro a _
        rcases huniform a with h | h <;> rw [h] <;> ring
      _ = 1 / N := by rw [← Finset.sum_mul, hmass, one_mul]
  have hshannon : shannon w = Real.log N := by
    unfold shannon
    have hterm : ∀ a, w a * Real.log (w a) = w a * Real.log (1 / N) := by
      intro a
      rcases huniform a with h | h <;> simp [h]
    simp_rw [hterm]
    rw [← Finset.sum_mul, hmass, one_mul]
    simp [one_div]
  exact ⟨hcollision, by simp [collisionEntropy, hcollision, one_div], hshannon⟩

/-- On actual isotropic frames, Shannon equality and collision equality coincide. -/
theorem sharp_frame_entropy_equality_iff {α : Type*}
    [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    shannon w = Real.log (roundedDimension n) ↔
      collision w = 1 / (roundedDimension n : ℝ) := by
  have hN : (0 : ℝ) < roundedDimension n := by
    have : 0 < roundedDimension n := by unfold roundedDimension; omega
    exact_mod_cast this
  constructor
  · exact shannon_equality_forces_collision_equality w hw hmass hN
      (sharp_frame_collision_bound hn A w hsign hw hmass hiso)
  · intro heq
    exact (entropy_of_uniform_weights w hN hmass
      (sharp_frame_equality_uniform hn A w hsign hw hmass hiso heq)).2.2

/-- Exact unweighted column Gram on the equality support. -/
theorem sharp_frame_equality_support_gram {α : Type*}
    [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (heq : collision w = 1 / (roundedDimension n : ℝ)) (i j : Fin n) :
    (∑ a ∈ Finset.univ.filter (fun a => w a ≠ 0),
      (A a i : ℝ) * (A a j : ℝ)) =
      if i = j then (roundedDimension n : ℝ) else 0 := by
  classical
  let N : ℝ := roundedDimension n
  have hN : N ≠ 0 := by
    change (roundedDimension n : ℝ) ≠ 0
    have : 0 < roundedDimension n := by unfold roundedDimension; omega
    exact_mod_cast this.ne'
  have huniform := sharp_frame_equality_uniform hn A w hsign hw hmass hiso heq
  calc
    _ = ∑ a, N * (w a * (A a i : ℝ) * (A a j : ℝ)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : w a = 0
      · simp [ha]
      · have hval : w a = 1 / N := (huniform a).resolve_left ha
        rw [ite_eq_left ha, hval]
        field_simp
    _ = N * (∑ a, w a * (A a i : ℝ) * (A a j : ℝ)) := by rw [Finset.mul_sum]
    _ = _ := by rw [hiso]; split_ifs <;> simp [N]

end EntropyDesigns
