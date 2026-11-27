/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.CompletedBlocks
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def selectedEndpoint {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (F : Finset (OffsetParameters k s i0)) :
    Finset (SourceOutcome k s i0) := Finset.univ.image
      (fun p : {c // c∈F} × (Fin k × (Fin s → Bool)) =>
        completedCode e i0 (extendOffsets i0 p.1.val) K p.2.1 p.2.2)

def selectedOriginal {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (F : Finset (OffsetParameters k s i0)) : Finset (SourceOutcome k s i0) := Finset.univ.image
      (fun p : {c // c∈F} × (Fin s → Bool) => sourceCode e i0 (offsetSeed (extendOffsets i0 p.1.val) p.2))

theorem selectedEndpoint_card {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) (hcol : ∀ t,K t i0=1)
    (F : Finset (OffsetParameters k s i0)) :
    (selectedEndpoint e i0 K F).card=F.card*(k*2^s) := by
  classical
  have hf : Function.Injective
      (fun p : {c // c∈F} × (Fin k × (Fin s → Bool)) =>
        completedCode e i0 (extendOffsets i0 p.1.val) K p.2.1 p.2.2) := by
    intro p q heq
    have h := normalized_completed_codes_injective hs e i0 K hK hcol
      (a₁:=(p.1.val,p.2)) (a₂:=(q.1.val,q.2)) heq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (congrArg (fun z : OffsetParameters k s i0 × (Fin k × (Fin s → Bool)) => z.2) h)
  rw [selectedEndpoint,Finset.card_image_of_injective _ hf]
  simp

theorem selectedOriginal_card {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (F : Finset (OffsetParameters k s i0)) : (selectedOriginal e i0 F).card=F.card*2^s := by
  classical
  have hf : Function.Injective
      (fun p : {c // c∈F} × (Fin s → Bool) => sourceCode e i0 (offsetSeed (extendOffsets i0 p.1.val) p.2)) := by
    intro p q heq
    have hseed := sourceCode_injective e i0 heq
    have h := (offsetPartitionEquiv i0).injective
      (a₁:=(p.1.val,p.2)) (a₂:=(q.1.val,q.2)) hseed
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (congrArg (fun z : OffsetParameters k s i0 × (Fin s → Bool) => z.2) h)
  rw [selectedOriginal,Finset.card_image_of_injective _ hf]
  simp

theorem selectedEndpoint_source_intersection {k s : ℕ} (hs : 2≤s) (e : Finset (Fin s))
    (i0 : Fin k) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (hcol : ∀ t,K t i0=1)
    (F : Finset (OffsetParameters k s i0)) :
    observedSupport e i0∩selectedEndpoint e i0 K F=selectedOriginal e i0 F := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨hx,hr⟩ := Finset.mem_inter.mp hy
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hx
    obtain ⟨p,_,hr⟩ := Finset.mem_image.mp hr
    let d := (offsetPartitionEquiv (s:=s) i0).symm x
    have hd : offsetSeed (extendOffsets i0 d.1) d.2=x :=
      (offsetPartitionEquiv (s:=s) i0).apply_symm_apply x
    have heq : completedCode e i0 (extendOffsets i0 p.1.val) K p.2.1 p.2.2=
        completedCode e i0 (extendOffsets i0 d.1) K i0 d.2 := by
      calc
        _ = y := hr
        _ = sourceCode e i0 x := hx.symm
        _ = _ := by rw [←hd,completedCode_first_row e i0 (extendOffsets i0 d.1) K hfirst]
    have hpar := normalized_completed_codes_injective hs e i0 K hK hcol
      (a₁:=(p.1.val,p.2)) (a₂:=(d.1,(i0,d.2))) heq
    have ht : p.2.1=i0 := congrArg (fun z : OffsetParameters k s i0 × (Fin k × (Fin s → Bool)) => z.2.1) hpar
    apply Finset.mem_image.mpr
    refine ⟨(p.1,p.2.2),Finset.mem_univ _,?_⟩
    rw [←completedCode_first_row e i0 (extendOffsets i0 p.1.val) K hfirst]
    simpa only [ht] using hr
  · intro hy
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨offsetSeed (extendOffsets i0 p.1.val) p.2,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨(p.1,(i0,p.2)),Finset.mem_univ _,
        completedCode_first_row e i0 (extendOffsets i0 p.1.val) K hfirst p.2⟩

end
end EntropyDesigns.SupportFace
