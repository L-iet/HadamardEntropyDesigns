module

public import EntropyDesigns.EqualityGeometry
public import Mathlib.Analysis.Real.Sqrt

/-! # Exact nonnegative kernel defects -/

@[expose] public section
namespace EntropyDesigns

def offDiagonalTotal {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) : ℝ :=
  ∑ a, ∑ b, if a = b then 0 else w a * w b * P a b

theorem offDiagonalTotal_identity {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) (D : ℝ)
    (hdiag : ∀ a, P a a = D) :
    offDiagonalTotal w P = weightedTotal w P - collision w * D := by
  have hsplit : ∀ a b, (if a = b then (0 : ℝ) else w a * w b * P a b) =
      w a * w b * P a b - if a = b then w a ^ 2 * D else 0 := by
    intro a b
    by_cases h : a = b
    · subst b
      simp only [ite_true, hdiag]
      ring
    · simp [h]
  unfold offDiagonalTotal
  simp_rw [hsplit, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]
  rfl

theorem offDiagonalTotal_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hP : ∀ a b, 0 ≤ P a b) :
    0 ≤ offDiagonalTotal w P := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (hw a) (hw b)) (hP a b)

/-- Exact squared residual identity underlying both Bessel and stability. -/
theorem projection_residual_identity {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (w ε : α → ℝ) (v : α → ι → ℝ)
    (hiso : ∀ i j, ∑ a, w a * v a i * v a j = if i = j then 1 else 0) :
    (∑ a, w a * (ε a - ∑ i, projectionCoefficients w ε v i * v a i) ^ 2) =
      (∑ a, w a * ε a ^ 2) - ∑ i, projectionCoefficients w ε v i ^ 2 := by
  let z := projectionCoefficients w ε v
  let L := fun a => ∑ i, z i * v a i
  have hcross : ∑ a, w a * ε a * L a = ∑ i, z i ^ 2 :=
    projection_cross_moment w ε v
  have hsecond : ∑ a, w a * L a ^ 2 = ∑ i, z i ^ 2 :=
    linear_form_second_moment v w z hiso
  have hmiddle : ∑ a, w a * (2 * ε a * L a) =
      2 * ∑ a, w a * ε a * L a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  change (∑ a, w a * (ε a - L a) ^ 2) = _
  simp_rw [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hmiddle, hcross, hsecond]
  ring

def residueKernel {α : Type*} {n : ℕ} (A : α → Fin n → ℤ) (a b : α) : ℝ :=
  (intInner A a b : ℝ) ^ 2 +
    2 * ((intParity A a : ℝ) * (intParity A b : ℝ) * (intInner A a b : ℝ)) - 3

def parityResidual {α : Type*} [Fintype α] {n : ℕ}
    (A : α → Fin n → ℤ) (w : α → ℝ) (a : α) : ℝ :=
  (intParity A a : ℝ) -
    ∑ i, projectionCoefficients w (fun a => (intParity A a : ℝ))
      (fun a i => (A a i : ℝ)) i * (A a i : ℝ)

theorem residue_one_polynomial_gap (q : ℤ) (hq : q % 4 = 1)
    (h₁ : q ≠ -3) (h₂ : q ≠ 1) : 32 ≤ q ^ 2 + 2 * q - 3 := by
  have hcases : q ≤ -7 ∨ 5 ≤ q := by omega
  rcases hcases with h | h <;> nlinarith

theorem residue_frame_defect_decomposition {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :

    (((n : ℝ) ^ 2 + 2 * n - 3) *
      (1 / ((n : ℝ) + 3) - collision w) =
      2 * (∑ a, w a * parityResidual A w a ^ 2) +
        offDiagonalTotal w (residueKernel A)) ∧
    0 ≤ (∑ a, w a * parityResidual A w a ^ 2) ∧
    0 ≤ offDiagonalTotal w (residueKernel A) := by
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
  have hεmass : ∑ a, w a * ε a ^ 2 = 1 := by
    simp_rw [hε, mul_one]
    exact hmass
  have hres : (∑ a, w a * parityResidual A w a ^ 2) =
      1 - ∑ i, projectionCoefficients w ε v i ^ 2 := by
    change (∑ a, w a * (ε a - ∑ i, projectionCoefficients w ε v i * v a i) ^ 2) = _
    rw [projection_residual_identity w ε v hiso, hεmass]
  have hoff : offDiagonalTotal w P =
      (n : ℝ) + 2 * (∑ i, projectionCoefficients w ε v i ^ 2) - 3 -
        collision w * ((n : ℝ) ^ 2 + 2 * n - 3) := by
    rw [offDiagonalTotal_identity w P _ hd, hp]
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hfactor : (1 / ((n : ℝ) + 3)) * ((n : ℝ) ^ 2 + 2 * n - 3) = n - 1 := by
    apply (mul_left_cancel₀ (by linarith : (n : ℝ) + 3 ≠ 0))
    field_simp
    ring
  refine ⟨?_, Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (sq_nonneg _)),
    offDiagonalTotal_nonneg w P hw hP⟩
  change ((n : ℝ) ^ 2 + 2 * n - 3) * (1 / ((n : ℝ) + 3) - collision w) =
    2 * (∑ a, w a * parityResidual A w a ^ 2) + offDiagonalTotal w P
  rw [hoff, hres]
  nlinarith [hfactor]

/-- Weighted Cauchy--Schwarz, retaining zero-weight atoms. -/
theorem weighted_abs_le_sqrt_second_moment {α : Type*} [Fintype α]
    (w h : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) :
    (∑ a, w a * |h a|) ≤ Real.sqrt (∑ a, w a * h a ^ 2) := by
  have hc := Real.sum_sqrt_mul_sqrt_le Finset.univ hw
    (fun a => mul_nonneg (hw a) (sq_nonneg (h a)))
  rw [hmass, Real.sqrt_one, one_mul] at hc
  have ht : ∀ a, Real.sqrt (w a) * Real.sqrt (w a * h a ^ 2) = w a * |h a| := by
    intro a
    rw [Real.sqrt_mul (hw a), Real.sqrt_sq_eq_abs, ← mul_assoc,
      Real.mul_self_sqrt (hw a)]
  simp_rw [ht] at hc
  exact hc

def offDiagonalRow {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) (a : α) : ℝ :=
  ∑ b, if a = b then 0 else w b * P a b

theorem offDiagonalRow_identity {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) (a : α) :
    offDiagonalRow w P a = (∑ b, w b * P a b) - w a * P a a := by
  have hs : ∀ b, (if a = b then (0 : ℝ) else w b * P a b) =
      w b * P a b - if a = b then w a * P a a else 0 := by
    intro b
    by_cases h : a = b
    · subst b
      simp
    · simp [h]
  unfold offDiagonalRow
  simp_rw [hs]
  rw [Finset.sum_sub_distrib]
  simp

theorem offDiagonalRow_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hP : ∀ a b, 0 ≤ P a b) (a : α) :
    0 ≤ offDiagonalRow w P a := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hw b) (hP a b)

theorem offDiagonalTotal_rows {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) :
    offDiagonalTotal w P = ∑ a, w a * offDiagonalRow w P a := by
  unfold offDiagonalTotal offDiagonalRow
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

theorem residueKernel_pointwise {α : Type*} [Fintype α]
    {n : ℕ} (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) (a : α) :
    (∑ b, w b * residueKernel A a b) =
      (n : ℝ) - 1 - 2 * (intParity A a : ℝ) * parityResidual A w a := by
  let ε := fun a => (intParity A a : ℝ)
  let v := fun a i => (A a i : ℝ)
  have hε : ε a ^ 2 = 1 := by
    rcases intParity_sign A hsign a with h | h <;> simp [ε, h]
  have hcross : (∑ b, w b * ((intParity A a : ℝ) *
      (intParity A b : ℝ) * (intInner A a b : ℝ))) =
      ε a * (∑ i, projectionCoefficients w ε v i * v a i) := by
    simp_rw [intInner_cast]
    exact pointwise_twisted_inner w ε v a
  have htwo : (∑ b, w b * (2 * ((intParity A a : ℝ) *
      (intParity A b : ℝ) * (intInner A a b : ℝ)))) =
      2 * (ε a * (∑ i, projectionCoefficients w ε v i * v a i)) := by
    calc
      _ = ∑ b, 2 * (w b * ((intParity A a : ℝ) *
          (intParity A b : ℝ) * (intInner A a b : ℝ))) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [← Finset.mul_sum, hcross]
  have hconst : (∑ b, w b * 3) = 3 := by rw [← Finset.sum_mul, hmass, one_mul]
  unfold residueKernel
  simp_rw [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    pointwise_intInner_moment A w hsign hiso a, htwo, hconst]
  change (n : ℝ) + 2 * (ε a * _) - 3 = n - 1 - 2 * ε a *
    (ε a - ∑ i, projectionCoefficients w ε v i * v a i)
  nlinarith [hε]

/-- Quantitative weighted stability from an exact nonnegative defect identity. -/
theorem weighted_defect_deviation_bound {α : Type*} [Fintype α]
    (w ε h b : α → ℝ) (D c δ : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hb : ∀ a, 0 ≤ b a)
    (hD : 0 < D)
    (hpoint : ∀ a, D * (w a - c) = -2 * ε a * h a - b a)
    (hdefect : D * δ = 2 * (∑ a, w a * h a ^ 2) + ∑ a, w a * b a) :
    (∑ a, w a * |w a - c|) ≤ Real.sqrt (2 * δ / D) + δ := by
  let X := ∑ a, w a * |h a|
  let E := ∑ a, w a * h a ^ 2
  let B := ∑ a, w a * b a
  have hX : 0 ≤ X := Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (abs_nonneg _)
  have hE : 0 ≤ E := Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (sq_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (hb a)
  have hcauchy : X ≤ Real.sqrt E := weighted_abs_le_sqrt_second_moment w h hw hmass
  have hXsq : X ^ 2 ≤ E := by nlinarith [Real.sq_sqrt hE]
  have hδ : D * δ = 2 * E + B := hdefect
  have hterm : ∀ a, D * |w a - c| ≤ 2 * |h a| + b a := by
    intro a
    have hεabs : |ε a| = 1 := by rcases hε a with he | he <;> simp [he]
    calc
      D * |w a - c| = |D * (w a - c)| := by rw [abs_mul, abs_of_pos hD]
      _ = |-2 * ε a * h a - b a| := congrArg abs (hpoint a)
      _ ≤ |-2 * ε a * h a| + |-(b a)| := abs_add_le _ _
      _ = 2 * |h a| + b a := by
        simp only [abs_mul, abs_neg, hεabs, abs_of_nonneg (hb a)]
        norm_num
  have hsum : (∑ a, w a * |w a - c|) * D ≤ 2 * X + B := by
    have hs := Finset.sum_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset α)) =>
        mul_le_mul_of_nonneg_left (hterm a) (hw a))
    calc
      _ = ∑ a, w a * (D * |w a - c|) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ ∑ a, w a * (2 * |h a| + b a) := hs
      _ = 2 * X + B := by
        dsimp [X,B]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        ring
  have hsquare : (2 * X / D) ^ 2 ≤ 2 * δ / D := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hD)).mp
    have hleft : (2 * X / D) ^ 2 * D ^ 2 = 4 * X ^ 2 := by
      field_simp
      ring
    have hright : (2 * δ / D) * D ^ 2 = 2 * δ * D := by
      field_simp
    rw [hleft, hright]
    nlinarith
  have hroot : 2 * X / D ≤ Real.sqrt (2 * δ / D) :=
    Real.le_sqrt_of_sq_le hsquare
  have hBbound : B / D ≤ δ := (div_le_iff₀ hD).2 (by nlinarith)
  have hlinear : (∑ a, w a * |w a - c|) ≤ (2 * X + B) / D :=
    (le_div_iff₀ hD).2 hsum
  rw [add_div] at hlinear
  exact hlinear.trans (add_le_add hroot hBbound)

theorem twisted_intInner_mod_four {α : Type*} {n : ℕ}
    (hres : n % 4 = 1) (A : α → Fin n → ℤ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (a b : α) :
    (intParity A a * intParity A b * intInner A a b) % 4 = 1 := by
  have h := switched_sign_sum_mod_four Finset.univ
    (fun i => A a i * A b i) (inner_product_signs A hsign a b) (by simpa using hres)
  rw [parity_product] at h
  exact h

theorem residueKernel_polynomial {α : Type*} {n : ℕ}
    (A : α → Fin n → ℤ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (a b : α) :
    residueKernel A a b =
      ((intParity A a * intParity A b * intInner A a b : ℤ) : ℝ) ^ 2 +
      2 * ((intParity A a * intParity A b * intInner A a b : ℤ) : ℝ) - 3 := by
  have ha : (intParity A a : ℝ) ^ 2 = 1 := by
    rcases intParity_sign A hsign a with h | h <;> simp [h]
  have hb : (intParity A b : ℝ) ^ 2 = 1 := by
    rcases intParity_sign A hsign b with h | h <;> simp [h]
  simp only [Int.cast_mul]
  rw [mul_pow, mul_pow, ha, hb]
  unfold residueKernel
  ring

theorem residueKernel_nonneg {α : Type*} {n : ℕ}
    (hres : n % 4 = 1) (A : α → Fin n → ℤ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (a b : α) :
    0 ≤ residueKernel A a b := by
  rw [residueKernel_polynomial A hsign]
  exact_mod_cast residue_one_polynomial_nonneg _ (twisted_intInner_mod_four hres A hsign a b)

theorem residueKernel_diagonal {α : Type*} {n : ℕ}
    (A : α → Fin n → ℤ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (a : α) :
    residueKernel A a a = (n : ℝ) ^ 2 + 2 * n - 3 := by
  have ha : (intParity A a : ℝ) ^ 2 = 1 := by
    rcases intParity_sign A hsign a with h | h <;> simp [h]
  unfold residueKernel
  rw [intInner_diag A hsign]
  simp only [Int.cast_natCast]
  nlinarith [ha]

/-- The paper's weighted distance-to-uniform bound for actual isotropic sign frames. -/
theorem residue_frame_weight_deviation {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    (∑ a, w a * |w a - 1 / ((n : ℝ) + 3)|) ≤
      Real.sqrt (2 * (1 / ((n : ℝ) + 3) - collision w) /
        ((n : ℝ) ^ 2 + 2 * n - 3)) +
      (1 / ((n : ℝ) + 3) - collision w) := by
  let D := (n : ℝ) ^ 2 + 2 * n - 3
  let ε := fun a => (intParity A a : ℝ)
  let b := offDiagonalRow w (residueKernel A)
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 < D := by dsimp [D]; nlinarith
  have hε : ∀ a, ε a = 1 ∨ ε a = -1 := by
    intro a
    rcases intParity_sign A hsign a with h | h <;> simp [ε,h]
  have hb : ∀ a, 0 ≤ b a :=
    offDiagonalRow_nonneg w (residueKernel A) hw (residueKernel_nonneg hres A hsign)
  have hfactor : D * (1 / ((n : ℝ) + 3)) = n - 1 := by
    apply (mul_left_cancel₀ (by linarith : (n : ℝ) + 3 ≠ 0))
    dsimp [D]
    field_simp
    ring
  have hpoint : ∀ a, D * (w a - 1 / ((n : ℝ) + 3)) =
      -2 * ε a * parityResidual A w a - b a := by
    intro a
    have hrow := offDiagonalRow_identity w (residueKernel A) a
    rw [residueKernel_pointwise A w hsign hmass hiso a,
      residueKernel_diagonal A hsign a] at hrow
    change b a = (n : ℝ) - 1 - 2 * ε a * parityResidual A w a - w a * D at hrow
    nlinarith [hfactor]
  have hdefect := (residue_frame_defect_decomposition hn hres A w hsign hw hmass hiso).1
  rw [offDiagonalTotal_rows] at hdefect
  exact weighted_defect_deviation_bound w ε (parityResidual A w) b D
    (1 / ((n : ℝ) + 3)) (1 / ((n : ℝ) + 3) - collision w)
    hw hmass hε hb hD hpoint hdefect

theorem offDiagonalTotal_mono {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P Q : α → α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hPQ : ∀ a b, P a b ≤ Q a b) :
    offDiagonalTotal w P ≤ offDiagonalTotal w Q := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  split_ifs
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left (hPQ a b) (mul_nonneg (hw a) (hw b))

theorem offDiagonalTotal_smul {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) (c : ℝ) :
    offDiagonalTotal w (fun a b => c * P a b) = c * offDiagonalTotal w P := by
  unfold offDiagonalTotal
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

def badPairMass {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (A : α → Fin n → ℤ) (w : α → ℝ) : ℝ :=
  offDiagonalTotal w (fun a b =>
    if intParity A a * intParity A b * intInner A a b = -3 ∨
      intParity A a * intParity A b * intInner A a b = 1 then 0 else 1)

/-- Exceptional ordered pairs consume at least thirty-two units of kernel defect. -/
theorem residue_frame_bad_pair_mass {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    badPairMass A w ≤
      ((n : ℝ) ^ 2 + 2 * n - 3) * (1 / ((n : ℝ) + 3) - collision w) / 32 := by
  let B : α → α → ℝ := fun a b =>
    if intParity A a * intParity A b * intInner A a b = -3 ∨
      intParity A a * intParity A b * intInner A a b = 1 then 0 else 1
  have hentry : ∀ a b, 32 * B a b ≤ residueKernel A a b := by
    intro a b
    dsimp [B]
    split_ifs with h
    · simpa using residueKernel_nonneg hres A hsign a b
    · have h₁ : intParity A a * intParity A b * intInner A a b ≠ -3 :=
        fun he => h (Or.inl he)
      have h₂ : intParity A a * intParity A b * intInner A a b ≠ 1 :=
        fun he => h (Or.inr he)
      rw [mul_one, residueKernel_polynomial A hsign]
      exact_mod_cast residue_one_polynomial_gap _
        (twisted_intInner_mod_four hres A hsign a b) h₁ h₂
  have hbound := offDiagonalTotal_mono w (fun a b => 32 * B a b)
    (residueKernel A) hw hentry
  rw [offDiagonalTotal_smul] at hbound
  have hdefect := residue_frame_defect_decomposition hn hres A w hsign hw hmass hiso
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).2
  change offDiagonalTotal w B * 32 ≤ _
  nlinarith [hdefect.1, hdefect.2.1]

theorem residue_frame_deficit_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    0 ≤ 1 / ((n : ℝ) + 3) - collision w :=
  sub_nonneg.mpr (residue_one_frame_collision_bound hn hres A w hsign hw hmass hiso)

end EntropyDesigns
