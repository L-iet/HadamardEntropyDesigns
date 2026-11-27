/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.FieldObservables
public import EntropySupportFace.SourceConsequences
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem attaining_law_of_slopes {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    ∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ sourceSupported e i0 q ∧
      collision q=1/((2:ℝ)^s)^2 := by
  classical
  let F := GaloisField 2 s
  letI : Fintype F := Fintype.ofFinite F
  let f : F × F → SourceOutcome k s i0 := fun p => sourceCode e i0 (fieldSlopeSeeds hs t p)
  let w : F × F → ℝ := fun _ => 1/(Fintype.card (F × F):ℝ)
  let q := pushLaw f w
  have hm := uniform_binary_character_moments (fieldObservable hs e i0 t)
    (fieldObservable_nonzero hs e he i0 t ht) (fieldObservable_injective hs e he i0 t ht)
  have hsign (p : F × F) (c : SourceCoordinate k s i0) :
      (bitSign (f p c):ℝ)=binarySign (fieldObservable hs e i0 t c p) := by
    change (bitSign (sourceCode e i0 (fieldSlopeSeeds hs t p) c):ℝ)=_
    rw [sourceCode_sign]
    exact fieldObservable_character hs e i0 t p c
  have hf : Function.Injective f := (sourceCode_injective e i0).comp (fieldSlopeSeeds_injective hk hs t ht)
  refine ⟨q,?_,?_,?_⟩
  · refine ⟨pushLaw_nonneg f w hm.1,(pushLaw_mass f w).trans hm.2.1,?_,?_⟩
    · intro c
      have hp := pushLaw_moment (α:=F × F) (β:=SourceOutcome k s i0) f w (fun y => (bitSign (y c):ℝ))
      change (∑ y,pushLaw f w y*(bitSign (y c):ℝ))=0
      rw [hp]
      simpa only [hsign,w] using hm.2.2.1 c
    · intro c d hcd
      have hp := pushLaw_moment (α:=F × F) (β:=SourceOutcome k s i0) f w
        (fun y => (bitSign (y c):ℝ)*(bitSign (y d):ℝ))
      change (∑ y,pushLaw f w y*(bitSign (y c):ℝ)*(bitSign (y d):ℝ))=0
      simp only [mul_assoc]
      rw [hp]
      simpa only [hsign,w,mul_assoc] using hm.2.2.2 c d hcd
  · intro y hy
    change pushLaw f w y=0
    unfold pushLaw
    apply Finset.sum_eq_zero
    intro p _
    have hn : f p≠y := fun h => hy ⟨fieldSlopeSeeds hs t p,h⟩
    simp only [hn,ite_false]
  · have hFcard : Fintype.card F=2^s := by
      simpa only [Nat.card_eq_fintype_card] using (GaloisField.card (p:=2) (n:=s) hs)
    have hPcard : Fintype.card (F × F)=(2^s)^2 := by simp [hFcard,pow_two]
    have hn : (Fintype.card (F × F):ℝ)≠0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (F × F)≠0)
    calc
      collision q=collision w := pushLaw_injective_collision f hf w
      _=1/(Fintype.card (F × F):ℝ) := by
        simp only [collision,w,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        field_simp [hn]
      _=1/((2:ℝ)^s)^2 := by rw [hPcard];simp

theorem source_attaining_law {k s : ℕ} (hk : 2≤k) (hkh : k≤2^s)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    ∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ sourceSupported e i0 q ∧
      collision q=1/((2:ℝ)^s)^2 ∧
      (∀ y,q y=0 ∨ q y=1/((2:ℝ)^s)^2) ∧
      Nat.card {y : SourceOutcome k s i0 // q y≠0}=(2^s)^2 := by
  classical
  have hs : s≠0 := by intro h;subst s;norm_num at hkh;omega
  let F := GaloisField 2 s
  letI : Fintype F := Fintype.ofFinite F
  have hFcard : Fintype.card F=2^s := by
    simpa only [Nat.card_eq_fintype_card] using (GaloisField.card (p:=2) (n:=s) hs)
  let ef : F ≃ Fin (2^s) := Fintype.equivFinOfCardEq hFcard
  let t : Fin k ↪ F :=
    { toFun := fun j => ef.symm ⟨j.val,lt_of_lt_of_le j.isLt hkh⟩
      inj' := by
        intro a b h
        apply Fin.ext
        have hv := congrArg (fun x : F => (ef x).val) h
        simpa only [Equiv.apply_symm_apply] using hv }
  obtain ⟨q,hq,hsupport,hcollision⟩ := attaining_law_of_slopes hk hs e he i0 t t.injective
  obtain ⟨hweights,hcard,_⟩ := source_collision_equality_oa hk e i0 q hq hsupport hcollision
  exact ⟨q,hq,hsupport,hcollision,hweights,hcard⟩
end
end EntropyDesigns.SupportFace
