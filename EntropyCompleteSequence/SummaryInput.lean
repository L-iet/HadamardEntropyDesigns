/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCompleteSequence.CompleteLawData
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section

/-- The paper's summary input, with all existence and entropy conclusions
in the concrete law-data record. No lower bound on k or nonzero dimension
is assumed separately: both follow from the stated budget. -/
theorem spanning_summary_input {k s : ℕ}
    (hsu : s≤2^s-k) (hsmall : 2^s-k<2^s/2)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    Nonempty (CompleteLawData k s) := by
  have hs : s≠0 := by
    intro hzero
    rw [hzero] at hsmall
    norm_num at hsmall
  have hk : 2≤k := order_at_least_two hs hsmall
  let e : Finset (Fin s) := {⟨0,Nat.pos_of_ne_zero hs⟩}
  let i0 : Fin k := ⟨0,lt_of_lt_of_le (by decide : 0<2) hk⟩
  exact complete_law_data_exists hk hsu hsmall e (Finset.singleton_nonempty _) i0 K hK

end
end EntropyDesigns.RelativeSequence
