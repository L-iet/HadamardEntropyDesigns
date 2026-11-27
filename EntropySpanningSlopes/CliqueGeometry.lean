/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.SlopeWindow
public import EntropyConcentratedFamily.PlaneLaw
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace

theorem spanning_plane_code_injective {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    Function.Injective (fun p : GaloisField 2 s × GaloisField 2 s =>
      sourceCode e i0 (fieldSlopeSeeds hs t p)) := by
  exact (sourceCode_injective e i0).comp (fieldSlopeSeeds_injective hk hs t ht)

theorem spanning_plane_clique_card_le {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2) (T : Finset (SourceOutcome k s i0))
    (hsub : T⊆ConcentratedFamily.planeSupport hs e i0 t)
    (horth : SupportWitness.IsClique observedOrthogonal T) : T.card≤2^s := by
  classical
  let K := GaloisField 2 s
  letI : Fintype K := Fintype.ofFinite K
  let f : K × K → SourceOutcome k s i0 := fun p => sourceCode e i0 (fieldSlopeSeeds hs t p)
  have hf : Function.Injective f := spanning_plane_code_injective hk hs e i0 t ht
  let V : Finset (K × K) := Finset.univ.filter (fun p => f p∈T)
  have himage : V.image f=T := by
    ext y
    constructor
    · intro hy
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hp).2
    · intro hy
      obtain ⟨p,hp⟩ := (ConcentratedFamily.mem_planeSupport hs e i0 t y).mp (hsub hy)
      have hfp : f p=y := hp
      exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hfp];exact hy⟩,hfp⟩
  have hcard : V.card=T.card := by
    rw [←himage,Finset.card_image_of_injective _ hf]
  by_cases hV : V.Nonempty
  · let p0 := hV.choose
    have hp0 : p0∈V := hV.choose_spec
    have hB (p : K × K) (hp : p∈V) : p.2=p0.2 := by
      by_cases hpp : p=p0
      · rw [hpp]
      · have ho := horth (f p) (Finset.mem_filter.mp hp).2
          (f p0) (Finset.mem_filter.mp hp0).2 (fun h => hpp (hf h))
        exact (spanning_slopes_orthogonal_iff hs e he i0 t ht hzero R hspan hcomp hsmall p p0 hpp).mp ho
    have hAinj : Set.InjOn (fun p : K × K => p.1) (V:Set (K × K)) := by
      intro p hp q hq hfirst
      exact Prod.ext hfirst ((hB p hp).trans (hB q hq).symm)
    have hcardA : (V.image (fun p : K × K => p.1)).card=V.card := Finset.card_image_of_injOn hAinj
    have hKcard : Fintype.card K=2^s := by
      simpa only [Nat.card_eq_fintype_card] using GaloisField.card (p:=2) (n:=s) hs
    calc
      T.card=V.card := hcard.symm
      _=(V.image (fun p : K × K => p.1)).card := hcardA.symm
      _≤Fintype.card K := Finset.card_le_univ _
      _=2^s := hKcard
  · have hz : V=∅ := Finset.not_nonempty_iff_eq_empty.mp hV
    rw [←hcard,hz]
    simp

theorem spanning_plane_orthogonality_number {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2) :
    SupportWitness.orthogonalityNumber observedOrthogonal (ConcentratedFamily.planeSupport hs e i0 t)=2^s := by
  classical
  apply le_antisymm
  · unfold SupportWitness.orthogonalityNumber
    apply Finset.sup_le
    intro T hT
    split_ifs with horth
    · exact spanning_plane_clique_card_le hk hs e he i0 t ht hzero R hspan hcomp hsmall T
        (Finset.mem_powerset.mp hT) horth
    · exact Nat.zero_le _
  · let K := GaloisField 2 s
    letI : Fintype K := Fintype.ofFinite K
    let f : K × K → SourceOutcome k s i0 := fun p => sourceCode e i0 (fieldSlopeSeeds hs t p)
    let T : Finset (SourceOutcome k s i0) := Finset.univ.image (fun a : K => f (a,0))
    have hf : Function.Injective f := spanning_plane_code_injective hk hs e i0 t ht
    have hfa : Function.Injective (fun a : K => f (a,0)) := by
      intro a b hab
      exact congrArg Prod.fst (hf hab)
    have hsub : T⊆ConcentratedFamily.planeSupport hs e i0 t := by
      intro y hy
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hy
      exact (ConcentratedFamily.mem_planeSupport hs e i0 t _).mpr ⟨(a,0),rfl⟩
    have horth : SupportWitness.IsClique observedOrthogonal T := by
      intro y hy z hz hne
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hz
      exact same_second_field_pair_orthogonal hs e i0 t (a,0) (b,0) rfl
        (fun hab => hne (congrArg f hab))
    have hKcard : Fintype.card K=2^s := by
      simpa only [Nat.card_eq_fintype_card] using GaloisField.card (p:=2) (n:=s) hs
    have hTcard : T.card=2^s := by
      rw [Finset.card_image_of_injective _ hfa,Finset.card_univ,hKcard]
    have h := SupportWitness.clique_card_le observedOrthogonal
      (ConcentratedFamily.planeSupport hs e i0 t) T hsub horth
    rw [hTcard] at h
    exact h

end
end EntropyDesigns.SpanningSlopes
