/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.FieldKernel
public import EntropySpanningSlopes.BinaryCounts
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace

theorem negative_indices_count_window {k s : ℕ} (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2)
    (p q : GaloisField 2 s × GaloisField 2 s) (hb : p.2-q.2≠0) :
    0<(negativeSlopeIndices hs e i0 t p q).card ∧
      2*(negativeSlopeIndices hs e i0 t p q).card<2^s := by
  classical
  let K := GaloisField 2 s
  letI : Fintype K := Fintype.ofFinite K
  let f := maskFieldFunctional hs e
  have hf : f≠0 := maskFieldFunctional_nonzero hs e he
  have hcard : Fintype.card K=2^s := by
    simpa only [Nat.card_eq_fintype_card] using GaloisField.card (p:=2) (n:=s) hs
  have hsmallGF : R.card<Fintype.card K/2 := by rw [hcard];exact hsmall
  have hw := omitted_spanning_count_window R hspan hsmallGF f hf (p.2-q.2) hb
  have himage : (negativeSlopeIndices hs e i0 t p q).image t=
      (Finset.univ\R).filter (fun a : K => f (a*(p.2-q.2))=1) := by
    ext a
    constructor
    · intro ha
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · intro hR
        exact ((hcomp (t j)).mp hR) ⟨j,rfl⟩
      · have hv := (Finset.mem_filter.mp hj).2
        simpa only [hzero,sub_zero] using hv
    · intro ha
      obtain ⟨hP,hval⟩ := Finset.mem_filter.mp ha
      have hnR := (Finset.mem_sdiff.mp hP).2
      have hex : ∃ j : Fin k,t j=a := by
        by_contra hn
        exact hnR ((hcomp a).mpr hn)
      obtain ⟨j,hj⟩ := hex
      apply Finset.mem_image.mpr
      refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hj⟩
      simpa only [hzero,sub_zero,hj] using hval
  have hcount : (negativeSlopeIndices hs e i0 t p q).card=
      ((Finset.univ\R).filter (fun a : K => f (a*(p.2-q.2))=1)).card := by
    rw [←himage,Finset.card_image_of_injective _ ht]
  rw [←hcount,hcard] at hw
  exact ⟨hw.1,by omega⟩

theorem spanning_slopes_orthogonal_iff {k s : ℕ} (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2)
    (p q : GaloisField 2 s × GaloisField 2 s) (hpq : p≠q) :
    observedOrthogonal (sourceCode e i0 (fieldSlopeSeeds hs t p))
      (sourceCode e i0 (fieldSlopeSeeds hs t q)) ↔ p.2=q.2 := by
  constructor
  · intro horth
    by_contra hb'
    have hb : p.2-q.2≠0 := sub_ne_zero.mpr hb'
    have hw := negative_indices_count_window hs e he i0 t ht hzero R hspan hcomp hsmall p q hb
    exact field_pair_nonorthogonal_of_negative_window hs e i0 t ht p q hb hw.1 hw.2 horth
  · intro hb
    exact same_second_field_pair_orthogonal hs e i0 t p q hb hpq

end
end EntropyDesigns.SpanningSlopes
