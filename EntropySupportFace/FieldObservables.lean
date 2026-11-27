/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.FieldMasks
public import EntropySupportFace.FieldSlopes
public import EntropySupportFace.SourceCode
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section

def fieldSlopeSeeds {k s : ℕ} (hs : s≠0) (t : Fin k → GaloisField 2 s)
    (p : GaloisField 2 s × GaloisField 2 s) : BlockSeeds k s :=
  fun i => fieldSeedEquiv s hs (slopeMap (t i) p)

def fieldObservable {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) : SourceCoordinate k s i0 →
      (GaloisField 2 s × GaloisField 2 s) →ₗ[ZMod 2] ZMod 2 :=
  Sum.elim (fun a => (maskFieldFunctional hs a.2.val).comp (slopeMap (t a.1)))
    (fun j => (maskFieldFunctional hs e).comp (scaledSndMap (t i0-t j.val)))

theorem fieldObservable_nonzero {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (he : e.Nonempty)
    (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    ∀ c,fieldObservable hs e i0 t c≠0 := by
  intro c
  rcases c with ⟨i,S⟩|j
  · exact nonzero_functional_comp_surjective _
      (maskFieldFunctional_nonzero hs S.val (Finset.nonempty_iff_ne_empty.mpr S.property)) _
      (slopeMap_surjective (t i))
  · have hne : t i0-t j.val≠0 := sub_ne_zero.mpr (fun h => j.property (ht h).symm)
    exact nonzero_functional_comp_surjective _ (maskFieldFunctional_nonzero hs e he) _
      (scaledSndMap_surjective _ hne)

theorem fieldObservable_injective {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (he : e.Nonempty)
    (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    Function.Injective (fieldObservable hs e i0 t) := by
  intro c d h
  rcases c with ⟨i,S⟩|j <;> rcases d with ⟨i',T⟩|j'
  · have hh := (slope_functional_eq_iff (t i) (t i') (maskFieldFunctional hs S.val)
      (maskFieldFunctional hs T.val) (maskFieldFunctional_nonzero hs S.val
        (Finset.nonempty_iff_ne_empty.mpr S.property))).mp h
    apply congrArg Sum.inl
    exact Prod.ext (ht hh.1) (Subtype.ext (maskFieldFunctional_injective hs hh.2))
  · exact False.elim (slope_functional_ne_scaled (t i) (t i0-t j'.val)
      (maskFieldFunctional hs S.val) (maskFieldFunctional hs e)
      (maskFieldFunctional_nonzero hs S.val (Finset.nonempty_iff_ne_empty.mpr S.property)) h)
  · exact False.elim (slope_functional_ne_scaled (t i') (t i0-t j.val)
      (maskFieldFunctional hs T.val) (maskFieldFunctional hs e)
      (maskFieldFunctional_nonzero hs T.val (Finset.nonempty_iff_ne_empty.mpr T.property)) h.symm)
  · have hc := scaled_functional_injective (maskFieldFunctional hs e)
      (maskFieldFunctional_nonzero hs e he) h
    have heq : t j.val=t j'.val := sub_right_inj.mp hc
    exact congrArg Sum.inr (Subtype.ext (ht heq))

theorem fieldObservable_character {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (p : GaloisField 2 s × GaloisField 2 s)
    (c : SourceCoordinate k s i0) :
    (sourceSign e i0 (fieldSlopeSeeds hs t p) c:ℝ)=binarySign (fieldObservable hs e i0 t c p) := by
  rcases c with ⟨i,S⟩|j
  · change (walshChar S.val (fieldSeedEquiv s hs (slopeMap (t i) p)):ℝ)=_
    rw [field_seed_walsh_character]
    rfl
  · change (((walshChar e (fieldSeedEquiv s hs (slopeMap (t i0) p))*
        walshChar e (fieldSeedEquiv s hs (slopeMap (t j.val) p))):ℤ):ℝ)=_
    rw [Int.cast_mul,field_seed_walsh_character,field_seed_walsh_character,← binarySign_sub,← map_sub]
    have hdiff : slopeMap (t i0) p-slopeMap (t j.val) p=scaledSndMap (t i0-t j.val) p := by
      change (p.1+t i0*p.2)-(p.1+t j.val*p.2)=(t i0-t j.val)*p.2
      ring
    rw [hdiff]
    rfl

theorem fieldSlopeSeeds_injective {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    Function.Injective (fieldSlopeSeeds hs t) := by
  intro p q h
  let i : Fin k := ⟨0,by omega⟩
  let j : Fin k := ⟨1,by omega⟩
  have hij : i≠j := by intro he;have hv := congrArg Fin.val he;dsimp [i,j] at hv;omega
  have hne : t i-t j≠0 := sub_ne_zero.mpr (fun he => hij (ht he))
  have he (a : Fin k) : p.1+t a*p.2=q.1+t a*q.2 :=
    (fieldSeedEquiv s hs).injective (congrFun h a)
  have hc : (t i-t j)*(p.2-q.2)=0 := by
    calc
      _=((p.1+t i*p.2)-(q.1+t i*q.2))-((p.1+t j*p.2)-(q.1+t j*q.2)) := by ring
      _=0 := by rw [he i,he j];ring
  have hB : p.2=q.2 := sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hne)
  apply Prod.ext
  · have hA := he i
    rw [hB] at hA
    exact add_right_cancel hA
  · exact hB
end
end EntropyDesigns.SupportFace
