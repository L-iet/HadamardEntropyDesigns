/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import HadamardMultibase.LogarithmSeparation
public import HadamardMultibase.Results
@[expose] public section
namespace EntropyDesigns.ProjectInput
open HadamardMultibase
theorem unconditional_sparse_bound : SparseRepresentationBound :=
  sparseRepresentationBound_of_not_liouville
    (not_liouville_log_ratio (by norm_num : 2≤(2:ℕ)) (by norm_num : 2≤(10:ℕ))
      irrational_log_ten_div_log_two)
theorem unconditional_uniform_exponent :
    ∃ C : ℝ,0<C ∧ ∃ N : ℕ,∀ x : ℕ,N≤x →
      ∃ T : ℕ,(T:ℝ)≤C*logScale x ∧
        ∀ q : ℕ,Odd q → q≤x → HadamardOrder (2^T*q) :=
  uniform_exponent_bound_of_inputs golayFamily craigenTransfer unconditional_sparse_bound
end EntropyDesigns.ProjectInput
