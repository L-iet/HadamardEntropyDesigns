/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantum.UniformCriteria
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem exact_ordered_commutator_energy (w : α → ℝ) (v : α → ι → ℝ)
    (N : ℝ) (hnorm : ∀ a,inner (v a) (v a)=N) :
    (commutatorEnergy w v=2*∑ a,∑ b,(w a)^2*(w b)^2*(inner (v a) (v b))^2*
      (N^2-(inner (v a) (v b))^2)) ∧
    (commutatorEnergy w v=2*(
      Matrix.trace ((∑ a,effect (w a) (v a)*effect (w a) (v a))*
        (∑ a,effect (w a) (v a)*effect (w a) (v a)))-
      ∑ a,∑ b,(Matrix.trace (effect (w a) (v a)*effect (w b) (v b)))^2)) :=
  ⟨exact_commutator_energy w v N hnorm,commutator_trace_energy w v N hnorm⟩
end
end EntropyDesigns.Quantum
