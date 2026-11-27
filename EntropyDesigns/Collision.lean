module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Collision estimates from a finite isotropic second-moment certificate

These are supporting lemmas for the entropy/design paper. They do not assert
the residue-sensitive principal bound or its Hadamard completion theorem.
-/

@[expose] public section

namespace EntropyDesigns

/-- Coordinate inner product, with the ordinary finite real-vector meaning. -/
def inner {α ι : Type*} [Fintype ι] (v : α → ι → ℝ) (a b : α) : ℝ :=
  ∑ i, v a i * v b i

/-- Coordinate isotropy implies the pointwise second-moment identity. -/
theorem moment_of_coordinate_isotropy {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (v : α → ι → ℝ) (w : α → ℝ)
    (hiso : ∀ i j, ∑ b, w b * v b i * v b j = if i = j then 1 else 0)
    (a : α) :
    ∑ b, w b * inner v a b ^ 2 = ∑ i, v a i ^ 2 := by
  unfold inner
  calc
    ∑ b, w b * (∑ i, v a i * v b i) ^ 2 =
        ∑ b, ∑ i, ∑ j, w b * (v a i * v b i) * (v a j * v b j) := by
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, ∑ b, w b * (v a i * v b i) * (v a j * v b j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (v a i * v a j) * (∑ b, w b * v b i * v b j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ i, v a i ^ 2 := by simp_rw [hiso]; simp [pow_two]

/-- The collision probability of a finite weighted law. -/
def collision {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  ∑ a, w a ^ 2

/-- A pointwise second-moment certificate gives the usual frame atom bound. -/
theorem atom_bound_of_moment {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (hn : 0 < n) (w : α → ℝ) (inner : α → α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hdiag : ∀ a, inner a a = n)
    (hmoment : ∀ a, ∑ b, w b * (inner a b) ^ 2 = n) (a : α) :
    w a ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : w a * (n : ℝ) ^ 2 ≤ n := by
    calc
      w a * (n : ℝ) ^ 2 = w a * (inner a a) ^ 2 := by rw [hdiag]
      _ ≤ ∑ b, w b * (inner a b) ^ 2 :=
        Finset.single_le_sum (fun b _ => mul_nonneg (hw b) (sq_nonneg _))
          (Finset.mem_univ a)
      _ = n := hmoment a
  apply (le_div_iff₀ hn').2
  apply (mul_le_mul_iff_left₀ hn').mp
  nlinarith [hs]

/-- Uniform atom bounds imply a collision bound for any probability law. -/
theorem collision_le_of_atom_bound {α : Type*} [Fintype α]
    (w : α → ℝ) (c : ℝ) (hw : ∀ a, 0 ≤ w a)
    (hmass : ∑ a, w a = 1) (hbound : ∀ a, w a ≤ c) :
    collision w ≤ c := by
  unfold collision
  calc
    ∑ a, w a ^ 2 ≤ ∑ a, w a * c := Finset.sum_le_sum fun a _ => by
      have := mul_le_mul_of_nonneg_left (hbound a) (hw a)
      nlinarith
    _ = c := by rw [← Finset.sum_mul, hmass, one_mul]

/-- The standard inverse-dimension collision bound from the frame certificate. -/
theorem collision_bound_of_moment {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (hn : 0 < n) (w : α → ℝ) (inner : α → α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hdiag : ∀ a, inner a a = n)
    (hmoment : ∀ a, ∑ b, w b * (inner a b) ^ 2 = n) :
    collision w ≤ 1 / (n : ℝ) :=
  collision_le_of_atom_bound w _ hw hmass
    (atom_bound_of_moment n hn w inner hw hdiag hmoment)

/-- The usual inverse-dimension collision bound for an actual finite isotropic
sign frame. The sharper residue-sensitive theorem is not asserted here. -/
theorem collision_bound_of_isotropic_sign_frame {α : Type*}
    [Fintype α] [DecidableEq α] (n : ℕ) (hn : 0 < n)
    (v : α → Fin n → ℝ) (w : α → ℝ)
    (hsign : ∀ a i, v a i = 1 ∨ v a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ b, w b * v b i * v b j = if i = j then 1 else 0) :
    collision w ≤ 1 / (n : ℝ) := by
  have hnorm : ∀ a, ∑ i, v a i ^ 2 = (n : ℝ) := by
    intro a
    have hs : ∀ i, v a i ^ 2 = (1 : ℝ) := by
      intro i
      rcases hsign a i with h | h <;> rw [h] <;> norm_num
    simp_rw [hs]
    simp
  apply collision_bound_of_moment n hn w (inner v) hw hmass
  · intro a
    simpa [inner, pow_two] using hnorm a
  · intro a
    rw [moment_of_coordinate_isotropy v w hiso a, hnorm a]

/-- Equality under an atom cap forces every atom to have weight zero or the cap. -/
theorem equality_forces_capped_weights {α : Type*} [Fintype α]
    (w : α → ℝ) (c : ℝ) (hw : ∀ a, 0 ≤ w a)
    (hmass : ∑ a, w a = 1) (hbound : ∀ a, w a ≤ c)
    (heq : collision w = c) :
    ∀ a, w a = 0 ∨ w a = c := by
  have hsum : ∑ a, w a * (c - w a) = 0 := by
    simp_rw [mul_sub, ← sq]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
    exact sub_eq_zero.mpr heq.symm
  have hz : ∀ a, w a * (c - w a) = 0 := by
    have hnonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ w a * (c - w a) :=
      fun a _ => mul_nonneg (hw a) (sub_nonneg.mpr (hbound a))
    exact fun a => (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum a (Finset.mem_univ a)
  intro a
  rcases mul_eq_zero.mp (hz a) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

end EntropyDesigns
