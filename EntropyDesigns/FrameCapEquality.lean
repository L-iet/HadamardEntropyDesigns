module

public import EntropyDesigns.UniformEquality

/-! # Atom caps and orthogonal support at equality for arbitrary finite frames -/

@[expose] public section
namespace EntropyDesigns

theorem finite_frame_atom_cap {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : α → ι → ℝ) (w : α → ℝ)
    (hsign : ∀ a i, v a i = 1 ∨ v a i = -1) (hw : ∀ a, 0 ≤ w a)
    (hiso : ∀ i j, ∑ a, w a * v a i * v a j = if i = j then 1 else 0) :
    ∀ a, w a ≤ 1 / (Fintype.card ι : ℝ) := by
  have hn : ∀ a, ∑ i, v a i ^ 2 = (Fintype.card ι : ℝ) := by
    intro a
    have hs : ∀ i, v a i ^ 2 = (1 : ℝ) := by
      intro i; rcases hsign a i with h | h <;> simp [h]
    simp_rw [hs]
    simp
  apply atom_bound_of_moment (Fintype.card ι) Fintype.card_pos w (inner v) hw
  · intro a
    simpa only [inner, pow_two] using hn a
  · intro a
    rw [moment_of_coordinate_isotropy v w hiso a, hn a]

theorem finite_frame_equality_uniform {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : α → ι → ℝ) (w : α → ℝ)
    (hsign : ∀ a i, v a i = 1 ∨ v a i = -1) (hw : ∀ a, 0 ≤ w a)
    (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * v a i * v a j = if i = j then 1 else 0)
    (heq : collision w = 1 / (Fintype.card ι : ℝ)) :
    ∀ a, w a = 0 ∨ w a = 1 / (Fintype.card ι : ℝ) :=
  equality_forces_capped_weights w _ hw hmass (finite_frame_atom_cap v w hsign hw hiso) heq

theorem finite_frame_equality_orthogonal {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : α → ι → ℝ) (w : α → ℝ)
    (hsign : ∀ a i, v a i = 1 ∨ v a i = -1) (hw : ∀ a, 0 ≤ w a)
    (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * v a i * v a j = if i = j then 1 else 0)
    (heq : collision w = 1 / (Fintype.card ι : ℝ))
    (a b : α) (ha : w a ≠ 0) (hb : w b ≠ 0) (hab : a ≠ b) : inner v a b = 0 := by
  have hcap := finite_frame_equality_uniform v w hsign hw hmass hiso heq
  have hva := (hcap a).resolve_left ha
  have hn : ∀ x, ∑ i, v x i ^ 2 = (Fintype.card ι : ℝ) := by
    intro x
    have hs : ∀ i, v x i ^ 2 = (1 : ℝ) := by
      intro i; rcases hsign x i with h | h <;> simp [h]
    simp_rw [hs]
    simp
  have hdiag : inner v a a = (Fintype.card ι : ℝ) := by
    simpa only [inner, pow_two] using hn a
  have hm := moment_of_coordinate_isotropy v w hiso a
  rw [hn a] at hm
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset α)
    (fun x => w x * (inner v a x) ^ 2) (Finset.mem_univ a)
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hterm : w a * (inner v a a) ^ 2 = (Fintype.card ι : ℝ) := by
    rw [hva, hdiag]
    field_simp
  have hz : (∑ x ∈ Finset.univ.erase a, w x * (inner v a x) ^ 2) = 0 := by
    rw [hterm, hm] at hsplit
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x (_ : x ∈ Finset.univ.erase a) => mul_nonneg (hw x) (sq_nonneg _))).mp hz b
      (by simp [Ne.symm hab])
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hzero).resolve_left hb)

end EntropyDesigns
