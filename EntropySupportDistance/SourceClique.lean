/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SourceGram
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem orthogonal_source_projection_injective {k s : ℕ} (e : Finset (Fin s))
    (i0 : Fin k) (hsize : 2*(k-1)<2^s) (T : Finset (BlockSeeds k s))
    (horth : ∀ x ∈ T, ∀ y ∈ T, x≠y → fullSourceInner e i0 x y=0) (j : Fin k) :
    Function.Injective (fun x : {x // x∈T} => x.val j) := by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  have hp := shared_block_inner_positive e i0 hsize x.val y.val j hxy
  rw [horth x.val x.property y.val y.property hne] at hp
  exact (lt_irrefl 0) hp

theorem orthogonal_source_card_le {k s : ℕ} (e : Finset (Fin s))
    (i0 : Fin k) (hsize : 2*(k-1)<2^s) (T : Finset (BlockSeeds k s))
    (horth : ∀ x ∈ T, ∀ y ∈ T, x≠y → fullSourceInner e i0 x y=0) :
    T.card≤2^s := by
  classical
  have h := Fintype.card_le_of_injective _
    (orthogonal_source_projection_injective e i0 hsize T horth i0)
  simpa using h

end
end EntropyDesigns.SupportFace
