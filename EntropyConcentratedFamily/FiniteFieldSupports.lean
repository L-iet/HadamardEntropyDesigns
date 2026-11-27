/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentratedFamily.FieldOffsets
public import EntropySupportDistance.SelectedEndpoint
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace

def fieldOffsetImage {k s : ℕ} (hs : s≠0) (i0 : Fin k) (t : Fin k → GaloisField 2 s) :
    Finset (OffsetParameters k s i0) := by
  classical
  exact Finset.univ.filter (fun c => ∃ B,fieldOffsetParameters hs i0 t B=c)

def planeSupport {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) : Finset (SourceOutcome k s i0) := by
  classical
  exact Finset.univ.filter (fun y => ∃ p : GaloisField 2 s × GaloisField 2 s,
    sourceCode e i0 (fieldSlopeSeeds hs t p)=y)

theorem mem_fieldOffsetImage {k s : ℕ} (hs : s≠0) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (c : OffsetParameters k s i0) :
    c∈fieldOffsetImage hs i0 t ↔ ∃ B,fieldOffsetParameters hs i0 t B=c := by
  classical
  simp [fieldOffsetImage]

theorem mem_planeSupport {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (y : SourceOutcome k s i0) :
    y∈planeSupport hs e i0 t ↔ ∃ z : GaloisField 2 s × GaloisField 2 s,
      sourceCode e i0 (fieldSlopeSeeds hs t z)=y := by
  classical
  simp [planeSupport]

theorem planeSupport_offset_partition {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) :
    planeSupport hs e i0 t=selectedOriginal e i0 (fieldOffsetImage hs i0 t) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hy).2
    let c := fieldOffsetParameters hs i0 t z.2
    have hc : c∈fieldOffsetImage hs i0 t :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨z.2,rfl⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨(⟨c,hc⟩,fieldSeedEquiv s hs (z.1+t i0*z.2)),Finset.mem_univ _,?_⟩
    change sourceCode e i0 (offsetSeed (extendOffsets i0 (fieldOffsetParameters hs i0 t z.2))
      (fieldSeedEquiv s hs (z.1+t i0*z.2)))=y
    rw [fieldSlopeSeeds_offset_identity]
    exact hz
  · intro hy
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨B,hB⟩ := (Finset.mem_filter.mp z.1.property).2
    let A : GaloisField 2 s := (fieldSeedEquiv s hs).symm z.2-t i0*B
    have hbase : fieldSeedEquiv s hs (A+t i0*B)=z.2 := by
      dsimp only [A]
      rw [sub_add_cancel,Equiv.apply_symm_apply]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,⟨(A,B),?_⟩⟩
    rw [←fieldSlopeSeeds_offset_identity hs i0 t A B,hbase,hB]

theorem fieldOffsetImage_card {k s : ℕ} (hk : 2≤k) (hs : s≠0) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    (fieldOffsetImage hs i0 t).card=2^s := by
  classical
  let F := GaloisField 2 s
  letI : Fintype F := Fintype.ofFinite F
  have himage : fieldOffsetImage hs i0 t=Finset.univ.image (fieldOffsetParameters hs i0 t) := by
    ext c
    simp [fieldOffsetImage]
  rw [himage,Finset.card_image_of_injective _ (fieldOffsetParameters_injective hk hs i0 t ht),Finset.card_univ]
  simpa only [Nat.card_eq_fintype_card] using (GaloisField.card (p:=2) (n:=s) hs)

theorem planeSupport_card {k s : ℕ} (hk : 2≤k) (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    (planeSupport hs e i0 t).card=(2^s)^2 := by
  rw [planeSupport_offset_partition,selectedOriginal_card,fieldOffsetImage_card hk hs i0 t ht]
  ring

end
end EntropyDesigns.ConcentratedFamily
