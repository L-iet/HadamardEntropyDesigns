/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean.Restriction
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
@[expose] public section
namespace EntropyDesigns
noncomputable section

def booleanSupportVector {r : ℕ} (z : Finset (Fin r)) : Fin r → ZMod 2 :=
  fun i => if i∈z then 1 else 0

def booleanAffineEvaluation (r : ℕ) :
    ((Fin r → ZMod 2) →ᵃ[ZMod 2] ZMod 2) →ₗ[ZMod 2] (Finset (Fin r) → ZMod 2) where
  toFun F := fun z => F (booleanSupportVector z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lowDegreeBooleanCode_one_affine (r : ℕ) :
    lowDegreeBooleanCode r 1 ≤ LinearMap.range (booleanAffineEvaluation r) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s,rfl⟩
  by_cases hs : s.val=∅
  · refine LinearMap.mem_range.mpr ⟨AffineMap.const (ZMod 2) (Fin r → ZMod 2) 1,?_⟩
    funext z
    simp [booleanAffineEvaluation,squarefreeBooleanMonomial,hs]
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hsingle : s.val={i} := by
      ext j
      simp only [Finset.mem_singleton]
      constructor
      · intro hj
        exact Finset.card_le_one.mp s.property j hj i hi
      · intro hji; subst j; exact hi
    refine LinearMap.mem_range.mpr ⟨(LinearMap.proj i : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2).toAffineMap,?_⟩
    funext z
    simp [booleanAffineEvaluation,booleanSupportVector,squarefreeBooleanMonomial,hsingle]

theorem affineSpanningComplement_degree_sub_two_extension {r : ℕ} (hr : 2≤r)
    (S : Finset (Finset (Fin r)))
    (hspan : affineSpan (ZMod 2) (Set.range (fun z : {z : Finset (Fin r) // z∉S} =>
      booleanSupportVector z.val))=⊤) :
    ∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode r (r-2), binaryFunctionRestriction S g=f := by
  apply (lowDegreeBooleanCode_extension_criterion (r:=r) (d:=r-2) (by omega) S).mpr
  intro g hg hs
  have hd : r-(r-2)-1=1 := by omega
  rw [hd] at hg
  obtain ⟨F,hF⟩ := LinearMap.mem_range.mp (lowDegreeBooleanCode_one_affine r hg)
  have heq : F=0 := by
    apply AffineMap.ext_on hspan
    rintro _ ⟨z,rfl⟩
    have hz := congrFun hF z.val
    change F (booleanSupportVector z.val)=g z.val at hz
    simpa using hz.trans (hs z.val z.property)
  funext z
  have hz := congrFun hF z
  rw [heq] at hz
  simpa [booleanAffineEvaluation] using hz.symm

theorem five_bit_affine_complement_cubic_extension
    (S : Finset (Finset (Fin 5)))
    (hspan : affineSpan (ZMod 2) (Set.range (fun z : {z : Finset (Fin 5) // z∉S} =>
      booleanSupportVector z.val))=⊤) :
    ∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode 5 3, binaryFunctionRestriction S g=f :=
  affineSpanningComplement_degree_sub_two_extension (by omega) S hspan

end
end EntropyDesigns
