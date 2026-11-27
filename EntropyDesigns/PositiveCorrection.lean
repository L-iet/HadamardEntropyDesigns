module

public import EntropyDesigns.SupportReduction
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Exact correction on a full-row-rank support -/

@[expose] public section
namespace EntropyDesigns

noncomputable def supportRightInverse {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (A : Matrix ι α ℝ) : Matrix α ι ℝ :=
  A.transpose * (A * A.transpose)⁻¹

theorem supportRightInverse_identity {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (A : Matrix ι α ℝ) (hA : A.rank = Fintype.card ι) :
    A * supportRightInverse A = 1 := by
  have hgram : (A * A.transpose).rank = Fintype.card ι :=
    (Matrix.rank_self_mul_transpose A).trans hA
  have hunit : IsUnit (A * A.transpose) :=
    Matrix.mulVec_surjective_iff_isUnit.mp
      (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hgram)
  unfold supportRightInverse
  rw [← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

noncomputable def supportCorrection {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ) : α → ℝ :=
  p - (supportRightInverse A).mulVec (A.mulVec p - b)

theorem supportCorrection_exact {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hA : A.rank = Fintype.card ι) :
    A.mulVec (supportCorrection A b p) = b := by
  unfold supportCorrection
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, supportRightInverse_identity A hA,
    Matrix.one_mulVec]
  abel

noncomputable def supportCondition {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] (A : Matrix ι α ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => ∑ i, |supportRightInverse A a i|)

theorem supportCorrection_distance {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ)
    (p : α → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hres : ∀ i, |A.mulVec p i - b i| ≤ τ) (a : α) :
    |supportCorrection A b p a - p a| ≤ supportCondition A * τ := by
  have hrow : (∑ i, |supportRightInverse A a i|) ≤ supportCondition A :=
    Finset.le_sup' (fun a => ∑ i, |supportRightInverse A a i|) (Finset.mem_univ a)
  have hbound : |(supportRightInverse A).mulVec (A.mulVec p - b) a| ≤
      (∑ i, |supportRightInverse A a i|) * τ := by
    unfold Matrix.mulVec dotProduct
    calc
      |∑ i, supportRightInverse A a i * (A.mulVec p - b) i| ≤
          ∑ i, |supportRightInverse A a i * (A.mulVec p - b) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |supportRightInverse A a i| * τ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hres i) (abs_nonneg _)
      _ = (∑ i, |supportRightInverse A a i|) * τ := (Finset.sum_mul _ _ _).symm
  have hsub : supportCorrection A b p a - p a =
      -((supportRightInverse A).mulVec (A.mulVec p - b) a) := by
    simp [supportCorrection]
  rw [hsub, abs_neg]
  exact hbound.trans (mul_le_mul_of_nonneg_right hrow hτ)

theorem supportCorrection_nonneg {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ)
    (p : α → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hres : ∀ i, |A.mulVec p i - b i| ≤ τ)
    (hmargin : ∀ a, supportCondition A * τ ≤ p a) :
    ∀ a, 0 ≤ supportCorrection A b p a := by
  intro a
  have h := (abs_le.mp (supportCorrection_distance A b p τ hτ hres a)).1
  linarith [hmargin a]

theorem supportCorrection_mass {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hA : A.rank = Fintype.card ι) (i₀ : ι)
    (hconstant : ∀ a, A i₀ a = 1) (hb : b i₀ = 1) :
    ∑ a, supportCorrection A b p a = 1 := by
  have h := congrFun (supportCorrection_exact A b p hA) i₀
  simpa [Matrix.mulVec, dotProduct, hconstant, hb] using h

theorem probability_collision_perturbation {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1)
    (η : ℝ) (hbound : ∀ a, |q a - p a| ≤ η) :
    collision p - 2 * η ≤ collision q := by
  have hcross : -η ≤ lawOverlap p (q - p) := by
    have hpoint : ∀ a, -η * p a ≤ p a * (q - p) a := by
      intro a
      have h := mul_le_mul_of_nonneg_left (abs_le.mp (hbound a)).1 (hp a)
      dsimp only [Pi.sub_apply]
      nlinarith
    have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
    simpa [← Finset.mul_sum, hmass, lawOverlap] using h
  have h := collision_direction_expansion p (q - p) 1
  have heq : (fun a => p a + 1 * (q - p) a) = q := by
    funext a
    simp
  rw [heq] at h
  have hnonneg : 0 ≤ collision (q - p) :=
    Finset.sum_nonneg (fun a _ => sq_nonneg ((q - p) a))
  nlinarith

theorem supportCorrection_variation {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ)
    (p : α → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hres : ∀ i, |A.mulVec p i - b i| ≤ τ) :
    (∑ a, |supportCorrection A b p a - p a|) / 2 ≤
      Fintype.card α * supportCondition A * τ / 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ => supportCorrection_distance A b p τ hτ hres a)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  nlinarith

theorem supportCorrection_collision_lower {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ)
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1)
    (τ : ℝ) (hτ : 0 ≤ τ) (hres : ∀ i, |A.mulVec p i - b i| ≤ τ) :
    collision p - 2 * supportCondition A * τ ≤ collision (supportCorrection A b p) := by
  simpa [mul_assoc] using probability_collision_perturbation p (supportCorrection A b p)
    hp hmass (supportCondition A * τ) (supportCorrection_distance A b p τ hτ hres)

theorem full_rank_positive_correction {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ)
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1)
    (hA : A.rank = Fintype.card ι) (i₀ : ι)
    (hconstant : ∀ a, A i₀ a = 1) (hb : b i₀ = 1)
    (τ : ℝ) (hτ : 0 ≤ τ) (hres : ∀ i, |A.mulVec p i - b i| ≤ τ)
    (hmargin : ∀ a, supportCondition A * τ ≤ p a) :
    (∀ a, 0 ≤ supportCorrection A b p a) ∧
    (∑ a, supportCorrection A b p a = 1) ∧
    A.mulVec (supportCorrection A b p) = b ∧
    (∀ a, |supportCorrection A b p a - p a| ≤ supportCondition A * τ) ∧
    (∑ a, |supportCorrection A b p a - p a|) / 2 ≤
      Fintype.card α * supportCondition A * τ / 2 ∧
    collision p - 2 * supportCondition A * τ ≤ collision (supportCorrection A b p) :=
  ⟨supportCorrection_nonneg A b p τ hτ hres hmargin,
    supportCorrection_mass A b p hA i₀ hconstant hb,
    supportCorrection_exact A b p hA,
    supportCorrection_distance A b p τ hτ hres,
    supportCorrection_variation A b p τ hτ hres,
    supportCorrection_collision_lower A b p hp hmass τ hτ hres⟩

end EntropyDesigns
