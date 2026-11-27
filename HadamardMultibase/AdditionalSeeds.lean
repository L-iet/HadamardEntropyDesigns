/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Length-ten seed declarations from the licensed first project; no proof changes. -/
module
public import HadamardMultibase.GolaySeeds
@[expose] public section
namespace HadamardMultibase
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
def seed₁₀A : Fin 10 → ℤ := ![1, 1, -1, 1, -1, 1, -1, -1, 1, 1]

def seed₁₀B : Fin 10 → ℤ := ![1, 1, -1, 1, 1, 1, 1, 1, -1, -1]

-- Livinskyi, thesis pp. 30–31. Entries are checked against the actual
-- aperiodic-autocorrelation definition, rather than trusting the transcription.

theorem seed₁₀_isGolayPair : IsGolayPair seed₁₀A seed₁₀B := by
  rw [isGolayPair_iff_fin]
  unfold IsBinary
  decide

theorem golayLength_ten : GolayLength 10 :=
  ⟨by omega, seed₁₀A, seed₁₀B, seed₁₀_isGolayPair⟩
end HadamardMultibase
