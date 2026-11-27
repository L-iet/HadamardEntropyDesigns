/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.FieldAttainment
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section

def blockProjection {k : ℕ} {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (j : Fin k) : (Fin k → F) →ₗ[ZMod 2] F where
  toFun x := x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def independentObservable {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k) :
    SourceCoordinate k s i0 → (Fin k → GaloisField 2 s) →ₗ[ZMod 2] ZMod 2 :=
  Sum.elim (fun a => (maskFieldFunctional hs a.2.val).comp (blockProjection a.1))
    (fun j => (maskFieldFunctional hs e).comp (blockProjection i0-blockProjection j.val))

def independentSeeds {k s : ℕ} (hs : s≠0) (x : Fin k → GaloisField 2 s) : BlockSeeds k s :=
  fun j => fieldSeedEquiv s hs (x j)

def fullSlopeMap {k : ℕ} {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (t : Fin k → F) : (F × F) →ₗ[ZMod 2] (Fin k → F) where
  toFun p j := p.1+t j*p.2
  map_add' p q := by funext j;simp [mul_add];ring
  map_smul' a p := by funext j;simp [Algebra.smul_def];ring

theorem independentObservable_restrict {k s : ℕ} (hs : s≠0) (e : Finset (Fin s))
    (i0 : Fin k) (t : Fin k → GaloisField 2 s) (c : SourceCoordinate k s i0) :
    (independentObservable hs e i0 c).comp (fullSlopeMap t)=fieldObservable hs e i0 t c := by
  apply LinearMap.ext
  intro p
  rcases c with ⟨j,S⟩|j
  · rfl
  · change maskFieldFunctional hs e ((p.1+t i0*p.2)-(p.1+t j.val*p.2))=
      maskFieldFunctional hs e ((t i0-t j.val)*p.2)
    congr 1
    ring

theorem independentObservable_nonzero {k s : ℕ} (hs : s≠0) (e : Finset (Fin s))
    (he : e.Nonempty) (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    ∀ c,independentObservable hs e i0 c≠0 := by
  intro c hc
  apply fieldObservable_nonzero hs e he i0 t ht c
  rw [←independentObservable_restrict hs e i0 t c,hc]
  rfl

theorem independentObservable_injective {k s : ℕ} (hs : s≠0) (e : Finset (Fin s))
    (he : e.Nonempty) (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    Function.Injective (independentObservable hs e i0) := by
  intro c d hcd
  apply fieldObservable_injective hs e he i0 t ht
  rw [←independentObservable_restrict hs e i0 t c,
    ←independentObservable_restrict hs e i0 t d,hcd]

theorem independentObservable_character {k s : ℕ} (hs : s≠0) (e : Finset (Fin s))
    (i0 : Fin k) (x : Fin k → GaloisField 2 s) (c : SourceCoordinate k s i0) :
    (sourceSign e i0 (independentSeeds hs x) c:ℝ)=binarySign (independentObservable hs e i0 c x) := by
  rcases c with ⟨j,S⟩|j
  · exact field_seed_walsh_character hs S.val (x j)
  · change ((walshChar e (fieldSeedEquiv s hs (x i0))*
      walshChar e (fieldSeedEquiv s hs (x j.val)):ℤ):ℝ)=
        binarySign (maskFieldFunctional hs e (x i0-x j.val))
    rw [Int.cast_mul,field_seed_walsh_character,field_seed_walsh_character,
      map_sub,binarySign_sub]

theorem independentSeeds_bijective {k s : ℕ} (hs : s≠0) :
    Function.Bijective (independentSeeds (k:=k) hs) := by
  constructor
  · intro x y h
    funext j
    exact (fieldSeedEquiv s hs).injective (congrFun h j)
  · intro x
    refine ⟨fun j => (fieldSeedEquiv s hs).symm (x j),?_⟩
    funext j
    exact (fieldSeedEquiv s hs).apply_symm_apply (x j)

end
end EntropyDesigns.SupportFace
