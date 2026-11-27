/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.AffineVanishing
public import EntropySupport.SupportedDual
@[expose] public section
namespace EntropyDesigns
noncomputable section

noncomputable def booleanAffineEvaluationCodeEquiv (r : ℕ) :
    ((Fin r → ZMod 2) →ᵃ[ZMod 2] ZMod 2) ≃ₗ[ZMod 2] lowDegreeBooleanCode r 1 :=
  LinearEquiv.ofBijective
    ((booleanAffineEvaluation r).codRestrict (lowDegreeBooleanCode r 1)
      (fun F => by rw [← booleanAffineEvaluation_range]; exact LinearMap.mem_range.mpr ⟨F,rfl⟩))
    ⟨by intro F G h; apply booleanAffineEvaluation_injective r; exact congrArg Subtype.val h,
      by intro g; obtain ⟨F,hF⟩ := LinearMap.mem_range.mp (by rw [booleanAffineEvaluation_range]; exact g.property)
         exact ⟨F,Subtype.ext hF⟩⟩

theorem affineCodeEquiv_inverse_value {r : ℕ} (g : lowDegreeBooleanCode r 1)
    (z : Finset (Fin r)) :
    (booleanAffineEvaluationCodeEquiv r).symm g (booleanSupportVector z)=g.val z := by
  have h := congrArg (fun h : lowDegreeBooleanCode r 1 => h.val z)
    ((booleanAffineEvaluationCodeEquiv r).apply_symm_apply g)
  exact h

def omittedBooleanVectors {r : ℕ} (S : Finset (Finset (Fin r))) : Set (Fin r → ZMod 2) :=
  booleanSupportVector '' (Sᶜ : Set (Finset (Fin r)))

noncomputable def affineCodeSupported_equiv_vanishing {r : ℕ}
    (S : Finset (Finset (Fin r))) :
    ↥(lowDegreeBooleanCode r 1 ⊓ supportedBinaryFunctions S) ≃ₗ[ZMod 2]
      affineVanishingOn (omittedBooleanVectors S) where
  toFun g := ⟨(booleanAffineEvaluationCodeEquiv r).symm ⟨g.val,g.property.1⟩,by
    rintro x ⟨z,hz,rfl⟩
    rw [affineCodeEquiv_inverse_value]
    exact g.property.2 z (by simpa using hz)⟩
  invFun F := ⟨booleanAffineEvaluation r F.val,⟨by
    rw [← booleanAffineEvaluation_range]; exact LinearMap.mem_range.mpr ⟨F.val,rfl⟩,
    by intro z hz; exact F.property _ ⟨z,by simpa using hz,rfl⟩⟩⟩
  left_inv g := by
    apply Subtype.ext
    funext z
    exact affineCodeEquiv_inverse_value ⟨g.val,g.property.1⟩ z
  right_inv F := by
    apply Subtype.ext
    apply (booleanAffineEvaluationCodeEquiv r).injective
    exact (booleanAffineEvaluationCodeEquiv r).apply_symm_apply _
  map_add' f g := by
    apply Subtype.ext
    exact (booleanAffineEvaluationCodeEquiv r).symm.map_add ⟨f.val,f.property.1⟩ ⟨g.val,g.property.1⟩
  map_smul' c f := by
    apply Subtype.ext
    exact (booleanAffineEvaluationCodeEquiv r).symm.map_smul c ⟨f.val,f.property.1⟩

theorem degree_sub_two_restriction_dimension {r : ℕ} (hr : 2≤r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ) :
    Module.finrank (ZMod 2) ((lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S))=
      S.card-(r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))) := by
  have hne : (omittedBooleanVectors S).Nonempty := by
    have hex : ∃ z,z∉S := by
      by_contra! h
      exact hproper (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨z,hz⟩ := hex
    exact ⟨booleanSupportVector z,⟨z,by simpa using hz,rfl⟩⟩
  have he := (affineCodeSupported_equiv_vanishing S).finrank_eq
  rw [affineVanishing_dimension _ hne] at he
  have hd := restrictionOrthogonal_finrank S (lowDegreeBooleanCode r (r-2))
  change _+Module.finrank (ZMod 2) ↥((booleanCubeDotForm r).orthogonal (lowDegreeBooleanCode r (r-2)) ⊓ supportedBinaryFunctions S)=_ at hd
  rw [lowDegreeBooleanCode_duality (by omega : r-2<r)] at hd
  have hdeg : r-(r-2)-1=1 := by omega
  rw [hdeg,he] at hd
  omega

end
end EntropyDesigns
