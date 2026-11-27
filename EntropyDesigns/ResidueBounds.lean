module

public import EntropyDesigns.Projection
public import EntropyDesigns.SignArithmetic

/-! # Residue-sensitive collision bounds for actual integer sign frames -/

@[expose] public section
namespace EntropyDesigns

def intInner {α : Type*} {n : ℕ} (A : α → Fin n → ℤ) (a b : α) : ℤ :=
  ∑ i, A a i * A b i

def intParity {α : Type*} {n : ℕ} (A : α → Fin n → ℤ) (a : α) : ℤ :=
  ∏ i, A a i

theorem intParity_sign {α : Type*} {n : ℕ} (A : α → Fin n → ℤ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (a : α) :
    intParity A a = 1 ∨ intParity A a = -1 :=
  prod_sign Finset.univ (A a) (fun i _ => hsign a i)

theorem inner_product_signs {α : Type*} {n : ℕ} (A : α → Fin n → ℤ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (a b : α) :
    ∀ i ∈ (Finset.univ : Finset (Fin n)), A a i * A b i = 1 ∨ A a i * A b i = -1 := by
  intro i _
  rcases hsign a i with h | h <;> rcases hsign b i with h' | h' <;> simp [h, h']

theorem intInner_diag {α : Type*} {n : ℕ} (A : α → Fin n → ℤ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (a : α) :
    intInner A a a = n := by
  unfold intInner
  calc
    ∑ i, A a i * A a i = ∑ _ : Fin n, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hsign a i with h | h <;> simp [h]
    _ = n := by simp

theorem intInner_cast {α : Type*} {n : ℕ} (A : α → Fin n → ℤ) (a b : α) :
    (intInner A a b : ℝ) = inner (fun a i => (A a i : ℝ)) a b := by
  simp [intInner, inner]

theorem parity_product {α : Type*} {n : ℕ} (A : α → Fin n → ℤ) (a b : α) :
    (∏ i, A a i * A b i) = intParity A a * intParity A b := by
  simp [intParity, Finset.prod_mul_distrib]

theorem pointwise_intInner_moment {α : Type*} [Fintype α] {n : ℕ}
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) (a : α) :
    ∑ b, w b * (intInner A a b : ℝ) ^ 2 = n := by
  simp_rw [intInner_cast]
  rw [moment_of_coordinate_isotropy _ w hiso a]
  calc
    ∑ i, (A a i : ℝ) ^ 2 = ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hsign a i with h | h <;> simp [h]
    _ = n := by simp

/-- The sharp collision bound in dimension three modulo four; in fact the
same estimate holds in every odd dimension greater than one. -/
theorem odd_frame_collision_bound {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    collision w ≤ 1 / ((n : ℝ) + 1) := by
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
  have hm : weightedTotal w (fun a b => (intInner A a b : ℝ) ^ 2) = n :=
    weightedTotal_of_pointwise_moment w _ _ hmass
      (pointwise_intInner_moment A w hsign hiso)
  have hp : weightedTotal w P = (n : ℝ) - 1 := by
    dsimp [P]
    rw [weightedTotal_sub, hm, weightedTotal_const w hmass]
  have hb := weighted_diagonal_lower w P ((n : ℝ) ^ 2 - 1) hw hP hd
  rw [hp] at hb
  exact odd_dimension_collision_arithmetic (by exact_mod_cast hn) hb

/-- The sharp collision bound in dimension two modulo four. -/
theorem residue_two_frame_collision_bound {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 2 < n) (hres : n % 4 = 2)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    collision w ≤ 1 / ((n : ℝ) + 2) := by
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
  rw [hp] at hb
  apply residue_two_collision_arithmetic (by exact_mod_cast hn)
  nlinarith [sq_nonneg (∑ a, w a * ε a)]

/-- The parity-switched polynomial and finite Bessel inequality give the
sharp collision estimate in dimension one modulo four. -/
theorem residue_one_frame_collision_bound {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    collision w ≤ 1 / ((n : ℝ) + 3) := by
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
  apply residue_one_collision_arithmetic (by exact_mod_cast hn)
  linarith

/-- The least multiple of four at least the augmented dimension. -/
def roundedDimension (n : ℕ) : ℕ := 4 * ((n + 3) / 4)

/-- Full residue-sensitive collision inequality for a finite isotropic sign
frame of dimension at least three. No Hadamard-existence assumption is used. -/
theorem sharp_frame_collision_bound {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    collision w ≤ 1 / (roundedDimension n : ℝ) := by
  have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · have hdim : roundedDimension n = n := by unfold roundedDimension; omega
    rw [hdim]
    apply collision_bound_of_isotropic_sign_frame n (by omega) (fun a i => (A a i : ℝ))
      w _ hw hmass hiso
    intro a i
    rcases hsign a i with h | h <;> simp [h]
  · have hdim : roundedDimension n = n + 3 := by unfold roundedDimension; omega
    rw [hdim]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      residue_one_frame_collision_bound (by omega) h A w hsign hw hmass hiso
  · have hdim : roundedDimension n = n + 2 := by unfold roundedDimension; omega
    rw [hdim]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      residue_two_frame_collision_bound (by omega) h A w hsign hw hmass hiso
  · have hdim : roundedDimension n = n + 1 := by unfold roundedDimension; omega
    rw [hdim]
    simpa only [Nat.cast_add, Nat.cast_one] using
      odd_frame_collision_bound (by omega) (by omega) A w hsign hw hmass hiso

end EntropyDesigns
