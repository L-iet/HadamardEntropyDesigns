/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.IndependentObservables
public import EntropySupportDistance.SourceOrthogonality
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem uniform_source_of_slopes {k s : ℕ} (hs : s≠0) (e : Finset (Fin s))
    (he : e.Nonempty) (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    ∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ sourceSupported e i0 q ∧
      collision q=1/((2:ℝ)^s)^k ∧
      (∀ x : BlockSeeds k s,q (sourceCode e i0 x)=1/((2:ℝ)^s)^k) ∧
      (observedSupport e i0).card=(2^s)^k := by
  classical
  let F := GaloisField 2 s
  letI : Fintype F := Fintype.ofFinite F
  let U := Fin k → F
  let f : U → SourceOutcome k s i0 := fun x => sourceCode e i0 (independentSeeds hs x)
  let w : U → ℝ := fun _ => 1/(Fintype.card U:ℝ)
  let q := pushLaw f w
  have hm := uniform_binary_character_moments (independentObservable hs e i0)
    (independentObservable_nonzero hs e he i0 t ht) (independentObservable_injective hs e he i0 t ht)
  have hsign (x : U) (c : SourceCoordinate k s i0) :
      (bitSign (f x c):ℝ)=binarySign (independentObservable hs e i0 c x) := by
    change (bitSign (sourceCode e i0 (independentSeeds hs x) c):ℝ)=_
    rw [sourceCode_sign]
    exact independentObservable_character hs e i0 x c
  have hf : Function.Injective f :=
    (sourceCode_injective e i0).comp (independentSeeds_bijective hs).1
  have hFcard : Fintype.card F=2^s := by
    simpa only [Nat.card_eq_fintype_card] using (GaloisField.card (p:=2) (n:=s) hs)
  have hUcard : Fintype.card U=(2^s)^k := by simp [U,hFcard]
  have hden : (Fintype.card U:ℝ)≠0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card U≠0)
  have hdeneq : (Fintype.card U:ℝ)=((2:ℝ)^s)^k := by rw [hUcard];simp
  refine ⟨q,?_,?_,?_,?_,?_⟩
  · refine ⟨pushLaw_nonneg f w hm.1,(pushLaw_mass f w).trans hm.2.1,?_,?_⟩
    · intro c
      have hp := pushLaw_moment (α:=U) (β:=SourceOutcome k s i0) f w (fun y => (bitSign (y c):ℝ))
      change (∑ y,pushLaw f w y*(bitSign (y c):ℝ))=0
      rw [hp]
      simpa only [hsign,w] using hm.2.2.1 c
    · intro c d hcd
      have hp := pushLaw_moment (α:=U) (β:=SourceOutcome k s i0) f w
        (fun y => (bitSign (y c):ℝ)*(bitSign (y d):ℝ))
      change (∑ y,pushLaw f w y*(bitSign (y c):ℝ)*(bitSign (y d):ℝ))=0
      simp only [mul_assoc]
      rw [hp]
      simpa only [hsign,w,mul_assoc] using hm.2.2.2 c d hcd
  · intro y hy
    change pushLaw f w y=0
    unfold pushLaw
    apply Finset.sum_eq_zero
    intro x _
    have hn : f x≠y := fun h => hy ⟨independentSeeds hs x,h⟩
    simp only [hn,ite_false]
  · calc
      collision q=collision w := pushLaw_injective_collision f hf w
      _=1/(Fintype.card U:ℝ) := by
        simp only [collision,w,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        field_simp [hden]
      _=1/((2:ℝ)^s)^k := by rw [hdeneq]
  · intro x
    obtain ⟨u,hu⟩ := (independentSeeds_bijective hs).2 x
    change q (sourceCode e i0 x)=_
    rw [←hu]
    change pushLaw f w (f u)=_
    rw [pushLaw_injective_value f hf w]
    exact congrArg (fun z : ℝ => 1/z) hdeneq
  · rw [observedSupport,Finset.card_image_of_injective _ (sourceCode_injective e i0)]
    simp [BlockSeeds]

end
end EntropyDesigns.SupportFace
