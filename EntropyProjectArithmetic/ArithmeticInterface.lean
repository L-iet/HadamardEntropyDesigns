/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
import EntropyProjectArithmetic.ProjectInput
public import HadamardMultibase.Basic
@[expose] public section
namespace EntropyDesigns.ArithmeticInterface
/-- The exact proved uniform multiplier endpoint, with the proof-only
arithmetic machinery behind a private import boundary. -/
theorem uniform_exponent :
    ∃ C : ℝ,0<C ∧ ∃ N : ℕ,∀ x : ℕ,N≤x →
      ∃ T : ℕ,(T:ℝ)≤C*HadamardMultibase.logScale x ∧
        ∀ q : ℕ,Odd q → q≤x → HadamardMultibase.HadamardOrder (2^T*q) :=
  ProjectInput.unconditional_uniform_exponent
end EntropyDesigns.ArithmeticInterface
