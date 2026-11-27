/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
Modified for this finite-radix project: Retained only the length-two seed needed by radix scaling; unused larger seed data and certificates are omitted.
-/
module

public import HadamardMultibase.Golay

@[expose] public section

namespace HadamardMultibase

/-- Finite formulation suitable for kernel-checked evaluation of explicit pairs. -/
theorem isGolayPair_iff_fin {n : ℕ} (A B : Fin n → ℤ) :
    IsGolayPair A B ↔ IsBinary A ∧ IsBinary B ∧
      ∀ s : Fin n, 0 < s.val → autocorrelation A s.val + autocorrelation B s.val = 0 := by
  constructor
  · rintro ⟨hA, hB, h⟩
    exact ⟨hA, hB, fun s hs => h s.val hs s.isLt⟩
  · rintro ⟨hA, hB, h⟩
    exact ⟨hA, hB, fun s hs hn => h ⟨s, hn⟩ hs⟩

def seed₂A : Fin 2 → ℤ := ![1, 1]
def seed₂B : Fin 2 → ℤ := ![1, -1]

theorem seed₂_isGolayPair : IsGolayPair seed₂A seed₂B := by
  rw [isGolayPair_iff_fin]
  unfold IsBinary
  decide

theorem golayLength_two : GolayLength 2 :=
  ⟨by omega, seed₂A, seed₂B, seed₂_isGolayPair⟩

end HadamardMultibase
