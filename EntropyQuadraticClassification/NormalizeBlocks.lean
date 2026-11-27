/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Compose block complements while retaining the parity graph invariants. -/
module
public import EntropyQuadraticClassification.BlockNormalization
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
variable {ι : Type*} [DecidableEq ι]

def normalizeBlocks : List (Finset ι × ι) → Finset ι → Finset ι
  | [],s => s
  | p::ps,s => normalizeBlocks ps (blockNormalize p.1 p.2 s)

theorem normalizeBlocks_checks (blocks : List (Finset ι × ι))
    (checks : Finset (Finset ι)) (s : Finset ι)
    (hs : SatisfiesChecks checks s)
    (hu : ∀ p∈blocks,SatisfiesChecks checks p.1) :
    SatisfiesChecks checks (normalizeBlocks blocks s) := by
  induction blocks generalizing s with
  | nil => exact hs
  | cons p ps ih =>
    apply ih
    · exact blockNormalize_checks p.2 hs (hu p (by simp))
    · intro q hq
      exact hu q (by simp [hq])

theorem normalizeBlocks_card (blocks : List (Finset ι × ι))
    (checks : Finset (Finset ι)) (s : Finset ι)
    (hs : SatisfiesChecks checks s)
    (hu : ∀ p∈blocks,p.1.card%4=0 ∧ SatisfiesChecks checks p.1 ∧ p.1∈checks) :
    (normalizeBlocks blocks s).card%4=s.card%4 := by
  induction blocks generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have hp := hu p (by simp)
    have hcheck := blockNormalize_checks p.2 hs hp.2.1
    have htail : ∀ q∈ps,q.1.card%4=0 ∧ SatisfiesChecks checks q.1 ∧ q.1∈checks :=
      fun q hq => hu q (by simp [hq])
    change (normalizeBlocks ps (blockNormalize p.1 p.2 s)).card%4=s.card%4
    rw [ih _ hcheck htail]
    exact blockNormalize_card p.1 s p.2 hp.1 (hs p.1 hp.2.2)

theorem normalizeBlocks_dot (blocks : List (Finset ι × ι))
    (checks : Finset (Finset ι)) (s t : Finset ι)
    (hs : SatisfiesChecks checks s) (ht : SatisfiesChecks checks t)
    (hu : ∀ p∈blocks,p.1.card%4=0 ∧ SatisfiesChecks checks p.1 ∧ p.1∈checks) :
    dotParity (normalizeBlocks blocks s) (normalizeBlocks blocks t)=dotParity s t := by
  induction blocks generalizing s t with
  | nil => rfl
  | cons p ps ih =>
    have hp := hu p (by simp)
    have hchecks := blockNormalize_checks p.2 hs hp.2.1
    have hcheckt := blockNormalize_checks p.2 ht hp.2.1
    have htail : ∀ q∈ps,q.1.card%4=0 ∧ SatisfiesChecks checks q.1 ∧ q.1∈checks :=
      fun q hq => hu q (by simp [hq])
    change dotParity (normalizeBlocks ps (blockNormalize p.1 p.2 s))
      (normalizeBlocks ps (blockNormalize p.1 p.2 t))=dotParity s t
    rw [ih _ _ hchecks hcheckt htail]
    apply blockNormalize_dot p.1 s t p.2
    · omega
    · exact hs p.1 hp.2.2
    · exact ht p.1 hp.2.2

theorem normalizeBlocks_membership_off (blocks : List (Finset ι × ι))
    (s : Finset ι) (a : ι) (ha : ∀ p∈blocks,a∉p.1) :
    a∈normalizeBlocks blocks s ↔ a∈s := by
  induction blocks generalizing s with
  | nil => rfl
  | cons p ps ih =>
    change a∈normalizeBlocks ps (blockNormalize p.1 p.2 s) ↔ a∈s
    rw [ih _ (fun q hq => ha q (by simp [hq]))]
    exact blockNormalize_membership_off p.1 s p.2 a (ha p (by simp))

end EntropyDesigns.QuadraticRefinement
