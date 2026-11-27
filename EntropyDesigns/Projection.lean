module

public import EntropyDesigns.WeightedKernels

/-! # Finite weighted orthogonal projection and the parity-twisted kernel -/

@[expose] public section
namespace EntropyDesigns

theorem linear_form_second_moment {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (v : α → ι → ℝ) (w : α → ℝ) (x : ι → ℝ)
    (hiso : ∀ i j, ∑ a, w a * v a i * v a j = if i = j then 1 else 0) :
    ∑ a, w a * (∑ i, x i * v a i) ^ 2 = ∑ i, x i ^ 2 := by
  calc
    ∑ a, w a * (∑ i, x i * v a i) ^ 2 =
        ∑ a, ∑ i, ∑ j, w a * (x i * v a i) * (x j * v a j) := by
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, ∑ a, w a * (x i * v a i) * (x j * v a j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (x i * x j) * (∑ a, w a * v a i * v a j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ i, x i ^ 2 := by simp_rw [hiso]; simp [pow_two]

/-- Coefficients of an observable in the finite weighted orthonormal coordinates. -/
def projectionCoefficients {α ι : Type*} [Fintype α]
    (w ε : α → ℝ) (v : α → ι → ℝ) : ι → ℝ :=
  fun i => ∑ a, w a * ε a * v a i

theorem projection_cross_moment {α ι : Type*} [Fintype α] [Fintype ι]
    (w ε : α → ℝ) (v : α → ι → ℝ) :
    ∑ a, w a * ε a * (∑ i, projectionCoefficients w ε v i * v a i) =
      ∑ i, projectionCoefficients w ε v i ^ 2 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    ∑ a, w a * ε a * (projectionCoefficients w ε v i * v a i) =
        projectionCoefficients w ε v i * ∑ a, w a * ε a * v a i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = projectionCoefficients w ε v i ^ 2 := by
      simp [projectionCoefficients, pow_two]

/-- Finite weighted Bessel inequality, proved by the squared residual expansion. -/
theorem bessel_of_coordinate_isotropy {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (w ε : α → ℝ) (v : α → ι → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hiso : ∀ i j, ∑ a, w a * v a i * v a j = if i = j then 1 else 0) :
    (∑ i, projectionCoefficients w ε v i ^ 2) ≤ ∑ a, w a * ε a ^ 2 := by
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
  have hexpand : ∑ a, w a * (ε a - L a) ^ 2 =
      (∑ a, w a * ε a ^ 2) - (∑ i, z i ^ 2) := by
    simp_rw [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [hmiddle, hcross, hsecond]
    ring
  have hnonneg : 0 ≤ ∑ a, w a * (ε a - L a) ^ 2 :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (sq_nonneg _)
  rw [hexpand] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Equality in Bessel forces the observable to equal its projection wherever
the probability weight is positive. -/
theorem bessel_equality_on_support {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (w ε : α → ℝ) (v : α → ι → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hiso : ∀ i j, ∑ a, w a * v a i * v a j = if i = j then 1 else 0)
    (heq : (∑ i, projectionCoefficients w ε v i ^ 2) = ∑ a, w a * ε a ^ 2) :
    ∀ a, w a ≠ 0 → ε a = ∑ i, projectionCoefficients w ε v i * v a i := by
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
  have hzero : ∑ a, w a * (ε a - L a) ^ 2 = 0 := by
    simp_rw [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [hmiddle, hcross, hsecond]
    change (∑ a, w a * ε a ^ 2) - 2 * (∑ i, z i ^ 2) +
      (∑ i, z i ^ 2) = 0
    dsimp [z]
    linarith [heq]
  intro a ha
  have ht : w a * (ε a - L a) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => mul_nonneg (hw b) (sq_nonneg _))).mp hzero a (Finset.mem_univ a)
  have hs : (ε a - L a) ^ 2 = 0 := (mul_eq_zero.mp ht).resolve_left ha
  have : ε a - L a = 0 := sq_eq_zero_iff.mp hs
  exact sub_eq_zero.mp this

theorem weightedTotal_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (w : α → ℝ) (P : ι → α → α → ℝ) :
    weightedTotal w (fun a b => ∑ i, P i a b) =
      ∑ i, weightedTotal w (P i) := by
  unfold weightedTotal
  simp_rw [Finset.mul_sum]
  calc
    (∑ a, ∑ b, ∑ i, w a * w b * P i a b) =
        ∑ a, ∑ i, ∑ b, w a * w b * P i a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ a, ∑ b, w a * w b * P i a b := by rw [Finset.sum_comm]

/-- The parity-twisted first moment is the squared projection norm. -/
theorem pointwise_twisted_inner {α ι : Type*} [Fintype α] [Fintype ι]
    (w ε : α → ℝ) (v : α → ι → ℝ) (a : α) :
    (∑ b, w b * (ε a * ε b * inner v a b)) =
      ε a * (∑ i, projectionCoefficients w ε v i * v a i) := by
  unfold inner projectionCoefficients
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The parity-switched two-point expectation is the squared projection norm. -/
theorem weighted_twisted_inner {α ι : Type*} [Fintype α] [Fintype ι]
    (w ε : α → ℝ) (v : α → ι → ℝ) :
    weightedTotal w (fun a b => ε a * ε b * inner v a b) =
      ∑ i, projectionCoefficients w ε v i ^ 2 := by
  have heq : (fun a b => ε a * ε b * inner v a b) =
      (fun a b => ∑ i, (ε a * v a i) * (ε b * v b i)) := by
    funext a b
    unfold inner
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, weightedTotal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedTotal_rank_one]
  congr 1
  unfold projectionCoefficients
  apply Finset.sum_congr rfl
  intro a _
  ring

end EntropyDesigns
