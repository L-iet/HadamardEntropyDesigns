/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.BinaryCharacters
public import Mathlib.Algebra.Algebra.Basic
@[expose] public section
namespace EntropyDesigns.SupportFace
noncomputable section
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

def slopeMap (t : F) : (F × F) →ₗ[ZMod 2] F where
  toFun p := p.1+t*p.2
  map_add' p q := by simp [mul_add];ring
  map_smul' c p := by simp [Algebra.smul_def];ring

def scaledSndMap (t : F) : (F × F) →ₗ[ZMod 2] F where
  toFun p := t*p.2
  map_add' p q := by simp [mul_add]
  map_smul' c p := by simp [Algebra.smul_def];ring

theorem slopeMap_surjective (t : F) : Function.Surjective (slopeMap t) := by
  intro y
  exact ⟨(y,0),by simp [slopeMap]⟩

theorem scaledSndMap_surjective (t : F) (ht : t≠0) : Function.Surjective (scaledSndMap t) := by
  intro y
  exact ⟨(0,t⁻¹*y),by simp [scaledSndMap,ht,mul_assoc]⟩

theorem nonzero_functional_comp_surjective (f : F →ₗ[ZMod 2] ZMod 2) (hf : f≠0)
    (T : (F × F) →ₗ[ZMod 2] F) (hT : Function.Surjective T) : f.comp T≠0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro y
  obtain ⟨p,hp⟩ := hT y
  have hv := LinearMap.congr_fun h p
  change f (T p)=0 at hv
  rw [hp] at hv
  exact hv

theorem slope_functional_eq_iff (a b : F) (f g : F →ₗ[ZMod 2] ZMod 2) (hf : f≠0) :
    f.comp (slopeMap a)=g.comp (slopeMap b) ↔ a=b ∧ f=g := by
  constructor
  · intro h
    have hfg : f=g := by
      apply LinearMap.ext
      intro y
      have hv := LinearMap.congr_fun h (y,0)
      simpa [slopeMap] using hv
    subst g
    by_cases hab : a=b
    · exact ⟨hab,rfl⟩
    · exfalso
      apply nonzero_functional_comp_surjective f hf (scaledSndMap (a-b))
        (scaledSndMap_surjective (a-b) (sub_ne_zero.mpr hab))
      apply LinearMap.ext
      intro p
      have hv := LinearMap.congr_fun h p
      change f (p.1+a*p.2)=f (p.1+b*p.2) at hv
      change f ((a-b)*p.2)=0
      have he : (a-b)*p.2=(p.1+a*p.2)-(p.1+b*p.2) := by ring
      rw [he,map_sub]
      exact sub_eq_zero.mpr hv
  · rintro ⟨rfl,rfl⟩
    rfl

theorem slope_functional_ne_scaled (a c : F) (f g : F →ₗ[ZMod 2] ZMod 2) (hf : f≠0) :
    f.comp (slopeMap a)≠g.comp (scaledSndMap c) := by
  intro h
  apply hf
  apply LinearMap.ext
  intro y
  have hv := LinearMap.congr_fun h (y,0)
  simpa [slopeMap,scaledSndMap] using hv

theorem scaled_functional_injective (f : F →ₗ[ZMod 2] ZMod 2) (hf : f≠0) :
    Function.Injective (fun a : F => f.comp (scaledSndMap a)) := by
  intro a b h
  have hfull : f.comp (slopeMap a)=f.comp (slopeMap b) := by
    apply LinearMap.ext
    intro p
    have hv := LinearMap.congr_fun h p
    change f (a*p.2)=f (b*p.2) at hv
    change f (p.1+a*p.2)=f (p.1+b*p.2)
    simp only [map_add]
    rw [hv]
  exact ((slope_functional_eq_iff a b f f hf).mp hfull).1
end
end EntropyDesigns.SupportFace
