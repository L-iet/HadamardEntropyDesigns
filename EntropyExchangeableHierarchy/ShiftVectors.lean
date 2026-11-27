/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyExchangeableHierarchy.PureTensors
public import EntropyExchangeableHierarchy.SignedShifts
public import Mathlib.Algebra.BigOperators.Field
@[expose] public section
namespace EntropyDesigns.ExchangeableHierarchy
noncomputable section
open scoped BigOperators ComplexOrder

def shiftVector {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) (a : G×G) : ℂ :=
  ((signedShift t ε a.1 a.2 / Real.sqrt (Fintype.card G:ℝ) : ℝ):ℂ)

theorem shiftVector_pair {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) (a b : G×G) :
    shiftVector t ε a*star (shiftVector t ε b)=
      ((signedShift t ε a.1 a.2*signedShift t ε b.1 b.2/(Fintype.card G:ℝ):ℝ):ℂ) := by
  have hr (x : ℝ) : star (x:ℂ)=(x:ℂ) := by simp
  simp only [shiftVector,hr,← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [div_mul_div_comm,← pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]

theorem shiftVector_normalized {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) : (∑ a : G×G,shiftVector t ε a*star (shiftVector t ε a))=1 := by
  have hn : (0:ℝ)<Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  simp_rw [shiftVector_pair]
  have hh : (∑ a : G×G,signedShift t ε a.1 a.2*signedShift t ε a.1 a.2/(Fintype.card G:ℝ))=1 := by
    rw [← Finset.sum_div]
    simp only [← pow_two]
    rw [signedShift_squared_norm,div_self hn.ne']
  exact_mod_cast hh

/-- Each displayed factor has maximally mixed first subsystem, hence is
maximally entangled; its purity comes from the explicit unit-vector form. -/
theorem shiftVector_reduced_state {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) (i a : G) :
    (∑ j,shiftVector t ε (i,j)*star (shiftVector t ε (a,j)))=
      ((if i=a then 1/(Fintype.card G:ℝ) else 0:ℝ):ℂ) := by
  simp_rw [shiftVector_pair]
  have hh : (∑ j,signedShift t ε i j*signedShift t ε a j/(Fintype.card G:ℝ))=
      if i=a then 1/(Fintype.card G:ℝ) else 0 := by
    rw [← Finset.sum_div,signedShift_row_moment]
    split_ifs <;> simp
  exact_mod_cast hh

theorem signedShift_not_flat {G : Type*} [AddGroup G] [Fintype G] [Nontrivial G] [DecidableEq G]
    (t : G) (ε : G → Bool) :
    ¬∀ i j : G,(signedShift t ε i j)^2=1/(Fintype.card G:ℝ) := by
  obtain ⟨i,j,hzero⟩ := signedShift_has_zero t ε
  intro hh
  have hn : (0:ℝ)<Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have heq := hh i j
  rw [hzero,zero_pow (by decide : (2:ℕ)≠0)] at heq
  linarith [one_div_pos.mpr hn]

end
end EntropyDesigns.ExchangeableHierarchy
