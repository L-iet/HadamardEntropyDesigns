/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean.Restriction
@[expose] public section
namespace EntropyDesigns
noncomputable section

def supportedBinaryFunctions {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {f | ∀ z,z∉S → f z=0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg z hz; simp [hf z hz,hg z hz]
  smul_mem' := by intro c f hf z hz; simp [hf z hz]

def binaryFunctionZeroExtendLinear {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (S → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun := binaryFunctionZeroExtend S
  map_add' f g := by
    funext z
    by_cases hz : z∈S <;> simp [binaryFunctionZeroExtend,hz]
  map_smul' c f := by
    funext z
    by_cases hz : z∈S <;> simp [binaryFunctionZeroExtend,hz]

noncomputable def restrictionOrthogonal_supportedEquiv {ι : Type*}
    [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    (binaryFunctionDotForm S).orthogonal (C.map (binaryFunctionRestriction S)) ≃ₗ[ZMod 2]
      ↥((binaryFunctionDotForm ι).orthogonal C ⊓ supportedBinaryFunctions S) where
  toFun f := ⟨binaryFunctionZeroExtend S f.val,
    ⟨(binaryFunctionRestriction_orthogonal S C f.val).mp f.property,
      by intro z hz; simp [binaryFunctionZeroExtend,hz]⟩⟩
  invFun f := ⟨binaryFunctionRestriction S f.val,by
    apply (binaryFunctionRestriction_orthogonal S C _).mpr
    have he : binaryFunctionZeroExtend S (binaryFunctionRestriction S f.val)=f.val := by
      funext z
      by_cases hz : z∈S
      · simp [binaryFunctionZeroExtend,binaryFunctionRestriction,hz]
      · simp [binaryFunctionZeroExtend,hz,f.property.2 z hz]
    rw [he]
    exact f.property.1⟩
  left_inv f := by
    apply Subtype.ext
    funext z
    exact binaryFunctionZeroExtend_on S f.val z
  right_inv f := by
    apply Subtype.ext
    funext z
    by_cases hz : z∈S
    · simp [binaryFunctionZeroExtend,binaryFunctionRestriction,hz]
    · simp [binaryFunctionZeroExtend,hz,f.property.2 z hz]
  map_add' f g := by
    apply Subtype.ext
    exact (binaryFunctionZeroExtendLinear S).map_add f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact (binaryFunctionZeroExtendLinear S).map_smul c f.val

theorem restrictionOrthogonal_finrank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    Module.finrank (ZMod 2) (C.map (binaryFunctionRestriction S))+
      Module.finrank (ZMod 2) ↥((binaryFunctionDotForm ι).orthogonal C ⊓ supportedBinaryFunctions S)=S.card := by
  have he := (restrictionOrthogonal_supportedEquiv S C).finrank_eq
  have hd := (binaryFunctionDotForm S).finrank_orthogonal (binaryFunctionDotForm_nondegenerate S)
    (C.map (binaryFunctionRestriction S))
  have hb := Submodule.finrank_le (C.map (binaryFunctionRestriction S))
  have hN : Module.finrank (ZMod 2) (S → ZMod 2)=S.card := by simp
  rw [hN] at hd hb
  omega

end
end EntropyDesigns
