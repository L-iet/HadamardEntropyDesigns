/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SourceRowBridge
public import EntropyWitness.SupportWitness
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def observedOrthogonal {k s : ℕ} {i0 : Fin k} (x y : SourceOutcome k s i0) : Prop :=
  1+(∑ c : SourceCoordinate k s i0,bitSign (x c)*bitSign (y c))=0

def observedSupport {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) :
    Finset (SourceOutcome k s i0) := Finset.univ.image (sourceCode e i0)

theorem observed_orthogonal_iff {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (x y : BlockSeeds k s) :
    observedOrthogonal (sourceCode e i0 x) (sourceCode e i0 y) ↔ fullSourceInner e i0 x y=0 := by
  rw [fullSourceInner_observed]
  rfl

theorem observed_clique_card_le {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (hsize : 2*(k-1)<2^s) (T : Finset (SourceOutcome k s i0))
    (hsub : T⊆observedSupport e i0) (horth : SupportWitness.IsClique observedOrthogonal T) :
    T.card≤2^s := by
  classical
  let U : Finset (BlockSeeds k s) := Finset.univ.filter (fun x => sourceCode e i0 x∈T)
  have himage : U.image (sourceCode e i0)=T := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2
    · intro hy
      obtain ⟨x,_,hx⟩ := Finset.mem_image.mp (hsub hy)
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ x,by rw [hx];exact hy⟩,hx⟩
  have hUorth : ∀ x∈U,∀ y∈U,x≠y → fullSourceInner e i0 x y=0 := by
    intro x hx y hy hne
    apply (observed_orthogonal_iff e i0 x y).mp
    apply horth _ (Finset.mem_filter.mp hx).2 _ (Finset.mem_filter.mp hy).2
    exact fun heq => hne (sourceCode_injective e i0 heq)
  have hc : U.card=T.card := by
    rw [←himage,Finset.card_image_of_injective _ (sourceCode_injective e i0)]
  rw [←hc]
  exact orthogonal_source_card_le e i0 hsize U hUorth

theorem observed_orthogonality_number {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (hsize : 2*(k-1)<2^s) :
    SupportWitness.orthogonalityNumber observedOrthogonal (observedSupport e i0)=2^s := by
  classical
  apply le_antisymm
  · unfold SupportWitness.orthogonalityNumber
    apply Finset.sup_le
    intro T hT
    split_ifs with horth
    · exact observed_clique_card_le e i0 hsize T (Finset.mem_powerset.mp hT) horth
    · exact Nat.zero_le _
  · let c : BlockSeeds k s := fun _ _ => false
    let T := (offsetClique c).image (sourceCode e i0)
    have hsub : T⊆observedSupport e i0 := by
      intro y hy
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩
    have horth : SupportWitness.IsClique observedOrthogonal T := by
      intro x hx y hy hne
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      apply (observed_orthogonal_iff e i0 a b).mpr
      exact offsetClique_orthogonal e i0 c a ha b hb (fun hab => hne (congrArg (sourceCode e i0) hab))
    have hc : T.card=2^s := by
      rw [Finset.card_image_of_injective _ (sourceCode_injective e i0)]
      exact offsetClique_card i0 c
    rw [←hc]
    exact SupportWitness.clique_card_le observedOrthogonal (observedSupport e i0) T hsub horth

end
end EntropyDesigns.SupportFace
