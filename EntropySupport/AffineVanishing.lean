/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.AffineSeparation
@[expose] public section
namespace EntropyDesigns
noncomputable section

def affineVanishingOn {r : ℕ} (T : Set (Fin r → ZMod 2)) :
    Submodule (ZMod 2) ((Fin r → ZMod 2) →ᵃ[ZMod 2] ZMod 2) where
  carrier := {F | ∀ x∈T,F x=0}
  zero_mem' := by simp
  add_mem' := by intro F G hF hG x hx; simp [hF x hx,hG x hx]
  smul_mem' := by intro c F hF x hx; simp [hF x hx]

theorem affineVanishing_linear_annihilates {r : ℕ}
    (T : Set (Fin r → ZMod 2)) (F : affineVanishingOn T) :
    F.val.linear∈(vectorSpan (ZMod 2) T).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro v hv
  have he : ∀ v∈vectorSpan (ZMod 2) T,F.val.linear v=0 := by
    apply Submodule.span_induction
    · rintro v ⟨x,hx,y,hy,rfl⟩
      simpa only [AffineMap.linear_apply_vsub,F.property x hx,F.property y hy,vsub_self] 
    · simp
    · intro x y hx hy ihx ihy; simp [map_add,ihx,ihy]
    · intro c x hx ih; simp [map_smul,ih]
  exact he v hv

noncomputable def affineVanishing_equiv_annihilator {r : ℕ}
    (T : Set (Fin r → ZMod 2)) (p : Fin r → ZMod 2) (hp : p∈T) :
    affineVanishingOn T ≃ₗ[ZMod 2] (vectorSpan (ZMod 2) T).dualAnnihilator where
  toFun F := ⟨F.val.linear,affineVanishing_linear_annihilates T F⟩
  invFun f := ⟨f.val.toAffineMap - AffineMap.const (ZMod 2) (Fin r → ZMod 2) (f.val p),by
    intro x hx
    have hxp : x-p∈vectorSpan (ZMod 2) T := vsub_mem_vectorSpan (ZMod 2) hx hp
    have hh := (Submodule.mem_dualAnnihilator _).mp f.property (x-p) hxp
    simpa [map_sub] using hh⟩
  left_inv F := by
    apply Subtype.ext
    ext x
    have hh := F.val.linear_apply_vsub x p
    have hz := F.property p hp
    simpa [hz] using hh
  right_inv f := by
    apply Subtype.ext
    simp [AffineMap.sub_linear,AffineMap.const_linear]
  map_add' F G := by apply Subtype.ext; exact AffineMap.add_linear _ _
  map_smul' c F := by apply Subtype.ext; exact AffineMap.smul_linear _ _

theorem affineVanishing_dimension {r : ℕ} (T : Set (Fin r → ZMod 2))
    (hne : T.Nonempty) :
    Module.finrank (ZMod 2) (affineVanishingOn T)=
      r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) T) := by
  obtain ⟨p,hp⟩ := hne
  have he := (affineVanishing_equiv_annihilator T p hp).finrank_eq
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq (vectorSpan (ZMod 2) T)
  have hv : Module.finrank (ZMod 2) (Fin r → ZMod 2)=r := by simp
  rw [hv] at hd
  omega

end
end EntropyDesigns
