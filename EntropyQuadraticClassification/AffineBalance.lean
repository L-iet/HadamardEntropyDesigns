/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Balanced fibers of a nonzero binary affine map with a zero. -/
module
public import EntropyQuadraticClassification.GaussOrthogonality
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped BigOperators

def gf2Sign (a : ZMod 2) : ℤ := if a=1 then -1 else 1

theorem gf2_two_cases : ∀ a : ZMod 2,a=0 ∨ a=1 := by decide

theorem gf2Sign_add_one : ∀ a : ZMod 2,gf2Sign (a+1)= -gf2Sign a := by decide

theorem gf2Sign_indicator (a : ZMod 2) :
    gf2Sign a=1-2*(if a=1 then (1 : ℤ) else 0) := by
  by_cases h : a=1 <;> simp [gf2Sign,h]

theorem gf2Sign_sum {A : Type*} [Fintype A] (f : A → ZMod 2) :
    (∑ a,gf2Sign (f a))=(Fintype.card A : ℤ)-
      2*((Finset.univ.filter (fun a => f a=1)).card : ℤ) := by
  classical
  simp_rw [gf2Sign_indicator]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [← Finset.mul_sum]
  have h : (∑ a : A,if f a=1 then (1 : ℤ) else 0)=
      ((Finset.univ.filter (fun a => f a=1)).card : ℤ) := by
    simp
  rw [h]

theorem affine_gf2_sign_sum_zero {r : ℕ}
    (F : (Fin r → ZMod 2) →ᵃ[ZMod 2] ZMod 2)
    (p : Fin r → ZMod 2) (hp : F p=0) (hF : F≠0) :
    (∑ y,gf2Sign (F y))=0 := by
  classical
  have hex : ∃ x,F x≠0 := by
    by_contra h
    have hz : ∀ x,F x=0 := by
      intro x
      by_contra hx
      exact h ⟨x,hx⟩
    apply hF
    ext x
    exact hz x
  obtain ⟨x,hx⟩ := hex
  have hFx : F x=1 := (gf2_two_cases (F x)).resolve_left hx
  let v := x-p
  have hv : F.linear v=1 := by
    simpa [v,hFx,hp] using F.linear_apply_vsub x p
  have hshift : ∀ y,F (y+v)=F y+1 := by
    intro y
    have hh := F.linear_apply_vsub (y+v) y
    change F.linear ((y+v)-y)=F (y+v)-F y at hh
    rw [add_sub_cancel_left,hv] at hh
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh.symm)
  apply sum_zero_of_negating_equiv (Equiv.addRight v) (fun y => gf2Sign (F y))
  intro y
  change gf2Sign (F (y+v))= -gf2Sign (F y)
  rw [hshift]
  exact gf2Sign_add_one (F y)

theorem affine_gf2_one_count {r : ℕ}
    (F : (Fin r → ZMod 2) →ᵃ[ZMod 2] ZMod 2)
    (p : Fin r → ZMod 2) (hp : F p=0) (hF : F≠0) :
    2*(Finset.univ.filter (fun y => F y=1)).card=2^r := by
  classical
  have h := affine_gf2_sign_sum_zero F p hp hF
  rw [gf2Sign_sum] at h
  have hc : Fintype.card (Fin r → ZMod 2)=2^r := by simp
  rw [hc] at h
  omega

theorem affine_four_one_count
    (F : (Fin 4 → ZMod 2) →ᵃ[ZMod 2] ZMod 2)
    (p : Fin 4 → ZMod 2) (hp : F p=0) (hF : F≠0) :
    (Finset.univ.filter (fun y => F y=1)).card=8 := by
  have h := affine_gf2_one_count F p hp hF
  norm_num at h
  omega

end EntropyDesigns.QuadraticRefinement
