/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Disjoint block complements clear all chosen anchor coordinates. -/
module
public import EntropyQuadraticClassification.NormalizeBlocks
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
variable {ι : Type*} [DecidableEq ι]

theorem normalizeBlocks_anchors (blocks : List (Finset ι × ι)) (s : Finset ι)
    (ha : ∀ p∈blocks,p.2∈p.1)
    (hd : blocks.Pairwise (fun p q => Disjoint p.1 q.1)) :
    ∀ p∈blocks,p.2∉normalizeBlocks blocks s := by
  induction blocks generalizing s with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hd
    intro q hq
    rcases List.mem_cons.mp hq with hq|hq
    · subst q
      have hoff : ∀ r∈ps,p.2∉r.1 := by
        intro r hr hm
        exact Finset.disjoint_left.mp (hhead r hr) (ha p (by simp)) hm
      change p.2∉normalizeBlocks ps (blockNormalize p.1 p.2 s)
      rw [normalizeBlocks_membership_off ps _ p.2 hoff]
      exact blockNormalize_first p.1 s p.2 (ha p (by simp))
    · exact ih (blockNormalize p.1 p.2 s)
        (fun r hr => ha r (by simp [hr])) htail q hq

end EntropyDesigns.QuadraticRefinement
