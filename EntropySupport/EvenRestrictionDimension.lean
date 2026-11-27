/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.RestrictionDimension
public import EntropyAffine.Indicator
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def binaryParityLinear (ι : Type*) [Fintype ι] : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun f := ∑ i,f i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

def evenBinaryCode {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  C ⊓ LinearMap.ker (binaryParityLinear ι)

theorem evenBinaryCode_finrank {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2))
    (hn : (fun _ : ι => (1 : ZMod 2))∉(binaryFunctionDotForm ι).orthogonal C) :
    Module.finrank (ZMod 2) (evenBinaryCode C)=Module.finrank (ZMod 2) C-1 := by
  classical
  let P := (binaryParityLinear ι).comp C.subtype
  have hex : ∃ g : C,P g≠0 := by
    by_contra! h
    apply hn
    intro g hg
    have hh := h ⟨g,hg⟩
    simpa [P,binaryParityLinear,binaryFunctionDotForm,dotProduct] using hh
  obtain ⟨g,hg⟩ := hex
  have hsur : Function.Surjective P := by
    intro a
    refine ⟨(a/(P g)) • g,?_⟩
    rw [map_smul]
    change (a/P g)*P g=a
    exact div_mul_cancel₀ a hg
  have hr : LinearMap.range P=⊤ := LinearMap.range_eq_top.mpr hsur
  have hd := P.finrank_range_add_finrank_ker
  rw [hr] at hd
  simp only [finrank_top,Module.finrank_self] at hd
  have he : (LinearMap.ker P).map C.subtype=evenBinaryCode C := by
    ext v
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨g.property,hg⟩
    · rintro ⟨hv,hp⟩
      exact ⟨⟨v,hv⟩,hp,rfl⟩
  have hm := Submodule.finrank_map_subtype_eq C (LinearMap.ker P)
  rw [he] at hm
  omega

theorem restriction_code_one_not_orthogonal {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hres : S.card%8=4) :
    (fun _ : S => (1 : ZMod 2))∉(binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S)) := by
  intro hh
  have hz := (binaryFunctionRestriction_orthogonal S (lowDegreeBooleanCode r (r-2)) _).mp hh
  have he : binaryFunctionZeroExtend S (fun _ : S => (1 : ZMod 2))=booleanSupportIndicator S := by
    funext z
    by_cases h : z∈S <;> simp [binaryFunctionZeroExtend,booleanSupportIndicator,h]
  rw [he] at hz
  change booleanSupportIndicator S∈(booleanCubeDotForm r).orthogonal (lowDegreeBooleanCode r (r-2)) at hz
  rw [lowDegreeBooleanCode_duality (by omega : r-2<r)] at hz
  have hd : r-(r-2)-1=1 := by omega
  rw [hd] at hz
  exact residue_four_support_indicator_not_affine hr S hres hz

theorem degree_sub_two_even_restriction_dimension {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ) (hres : S.card%8=4) :
    Module.finrank (ZMod 2) (evenBinaryCode
      ((lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S)))=
      S.card-(r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S)))-1 := by
  rw [evenBinaryCode_finrank _ (restriction_code_one_not_orthogonal hr S hres),
    degree_sub_two_restriction_dimension (by omega) S hproper]

end
end EntropyDesigns
