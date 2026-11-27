/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.RotationDensity
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace EntropyDesigns.RelativeSequence

/-- Arbitrarily late rotation visits yield a signed integer logarithm error
in any prescribed nonempty real interval. -/
theorem logarithm_error_in_interval (N : ℕ) (u v : ℝ) (huv : u < v) :
    ∃ a : ℕ, N ≤ a ∧ ∃ z : ℤ,
      u < (a : ℝ) * Real.log 12 - (z : ℝ) * Real.log 2 ∧
      (a : ℝ) * Real.log 12 - (z : ℝ) * Real.log 2 < v := by
  let q : ℝ → AddCircle (Real.log 2) := fun x => x
  have hopen : IsOpen (q '' Set.Ioo u v) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hne : (q '' Set.Ioo u v).Nonempty :=
    (Set.nonempty_Ioo.mpr huv).image q
  obtain ⟨n, x, hx, heq⟩ := (dense_twelve_log_rotation_tail N).exists_mem_open hopen hne
  have hq : (q (((n + N : ℕ) : ℝ) * Real.log 12 - x)) = 0 := by
    change (((((n + N : ℕ) : ℝ) * Real.log 12 : ℝ) : AddCircle (Real.log 2)) - q x) = 0
    rw [sub_eq_zero]
    simpa only [← nsmul_eq_mul, AddCircle.coe_nsmul] using heq.symm
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (Real.log 2)).mp hq
  simp only [zsmul_eq_mul] at hz
  exact ⟨n + N, Nat.le_add_left N n, z, by linarith [hx.1], by linarith [hx.2]⟩

end EntropyDesigns.RelativeSequence
