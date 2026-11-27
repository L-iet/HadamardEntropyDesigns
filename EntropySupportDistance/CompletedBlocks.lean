/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.CompletedCode
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def completedBlock {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (c : OffsetParameters k s i0) :
    Finset (SourceOutcome k s i0) := Finset.univ.image
      (fun r : Fin k × (Fin s → Bool) => completedCode e i0 (extendOffsets i0 c) K r.1 r.2)

theorem completedBlock_card {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hcol : ∀ t,K t i0=1) (c : OffsetParameters k s i0) :
    (completedBlock e i0 K c).card=k*2^s := by
  classical
  have hf : Function.Injective
      (fun r : Fin k × (Fin s → Bool) => completedCode e i0 (extendOffsets i0 c) K r.1 r.2) := by
    intro r v h
    have hp := normalized_completed_codes_injective hs e i0 K hK hcol
      (a₁:=(c,r)) (a₂:=(c,v)) h
    exact congrArg Prod.snd hp
  rw [completedBlock,Finset.card_image_of_injective _ hf]
  simp

theorem completedBlock_clique {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hcol : ∀ t,K t i0=1) (c : OffsetParameters k s i0) :
    SupportWitness.IsClique observedOrthogonal (completedBlock e i0 K c) := by
  classical
  intro x hx y hy hne
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hy
  apply completedCodes_orthogonal e i0 (extendOffsets i0 c) K hK hcol r v
  exact fun h => hne (congrArg
    (fun z : Fin k × (Fin s → Bool) => completedCode e i0 (extendOffsets i0 c) K z.1 z.2) h)

theorem completedBlockLaw_mem {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hcol : ∀ t,K t i0=1) (c : OffsetParameters k s i0) :
    uniformFiniteLaw (completedBlock e i0 K c)∈SupportWitness.blockLaws observedOrthogonal (k*2^s) := by
  exact ⟨completedBlock e i0 K c,completedBlock_card hs e i0 K hK hcol c,
    completedBlock_clique e i0 K hK hcol c,rfl⟩

theorem source_in_completedBlock_iff {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s))
    (i0 : Fin k) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (c d : OffsetParameters k s i0) (a : Fin s → Bool) :
    sourceCode e i0 (offsetSeed (extendOffsets i0 d) a)∈completedBlock e i0 K c ↔ c=d := by
  classical
  constructor
  · intro hx
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hx
    rw [←completedCode_first_row e i0 (extendOffsets i0 d) K hfirst] at hr
    have hp := normalized_completed_codes_injective hs e i0 K hK hcol
      (a₁:=(c,r)) (a₂:=(d,(i0,a))) hr
    exact congrArg Prod.fst hp
  · intro h
    subst d
    apply Finset.mem_image.mpr
    exact ⟨(i0,a),Finset.mem_univ _,completedCode_first_row e i0 (extendOffsets i0 c) K hfirst a⟩

theorem completedBlockLaw_source_value {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s))
    (i0 : Fin k) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (c d : OffsetParameters k s i0) (a : Fin s → Bool) :
    uniformFiniteLaw (completedBlock e i0 K c)
      (sourceCode e i0 (offsetSeed (extendOffsets i0 d) a))=
      if c=d then 1/((k*2^s:ℕ):ℝ) else 0 := by
  classical
  unfold uniformFiniteLaw
  simp only [source_in_completedBlock_iff hs e i0 K hK hfirst hcol,
    completedBlock_card hs e i0 K hK hcol]

end
end EntropyDesigns.SupportFace
