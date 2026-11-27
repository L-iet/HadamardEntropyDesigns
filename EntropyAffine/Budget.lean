/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyAffine.Complement
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

theorem affine_polynomial_complement_budget {r : ℕ} {ι : Type*} [Fintype ι]
    (S : Finset (Fin r → Bool)) (hS : S.Nonempty) (hproper : S≠Finset.univ)
    (g : ι → (Finset (Fin r) → ZMod 2)) (hg : ∀ i,g i∈lowDegreeBooleanCode r 1)
    (hortho : ∀ i j,i≠j → ∑ x∈S,
      (booleanValueSign (g i (boolCoordinateSupport x)) : ℝ)*
        (booleanValueSign (g j (boolCoordinateSupport x)) : ℝ)=0) :
    Fintype.card ι≤2^r-S.card := by
  classical
  choose ε T hε hrep using (fun i => degree_one_boolean_sign_character (g i) (hg i))
  have heq (i : ι) (x : Fin r → Bool) :
      realSignedCubeCharacter (ε i) (T i) x=
        (booleanValueSign (g i (boolCoordinateSupport x)) : ℝ) := by
    change ((ε i*walshChar (T i) x : ℤ) : ℝ)=_
    exact_mod_cast (hrep i x).symm
  apply signed_cube_character_complement_budget S hS hproper ε T hε
  intro i j hij
  simp_rw [heq]
  exact hortho i j hij

theorem affine_unbiased_output_complement_budget {r k : ℕ}
    (S : Finset (Fin r → Bool)) (hS : S.Nonempty) (hproper : S≠Finset.univ)
    (g : Fin k → (Finset (Fin r) → ZMod 2)) (hg : ∀ i,g i∈lowDegreeBooleanCode r 1)
    (hmean : ∀ i,∑ x∈S,(booleanValueSign (g i (boolCoordinateSupport x)) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x∈S,
      (booleanValueSign (g i (boolCoordinateSupport x)) : ℝ)*
        (booleanValueSign (g j (boolCoordinateSupport x)) : ℝ)=0) :
    k+1≤2^r-S.card := by
  let F : Option (Fin k) → (Finset (Fin r) → ZMod 2) := fun i => Option.elim i 0 g
  have hFC : ∀ i,F i∈lowDegreeBooleanCode r 1 := by
    intro i
    cases i with
    | none => exact Submodule.zero_mem _
    | some i => exact hg i
  have horth : ∀ i j : Option (Fin k),i≠j → ∑ x∈S,
      (booleanValueSign (F i (boolCoordinateSupport x)) : ℝ)*
        (booleanValueSign (F j (boolCoordinateSupport x)) : ℝ)=0 := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        change (∑ x∈S,(booleanValueSign 0 : ℝ)*(booleanValueSign (g j (boolCoordinateSupport x)) : ℝ))=0
        simpa only [show booleanValueSign 0=1 by rfl,Int.cast_one,one_mul] using hmean j
    | some i =>
      cases j with
      | none =>
        change (∑ x∈S,(booleanValueSign (g i (boolCoordinateSupport x)) : ℝ)*(booleanValueSign 0 : ℝ))=0
        simpa only [show booleanValueSign 0=1 by rfl,Int.cast_one,mul_one] using hmean i
      | some j =>
        have hne : i≠j := by intro h; apply hij; exact congrArg some h
        simpa [F] using hpair i j hne
  have hh := affine_polynomial_complement_budget S hS hproper F hFC horth
  simpa only [Fintype.card_option,Fintype.card_fin] using hh

theorem twelve_label_affine_output_bound {k : ℕ}
    (S : Finset (Fin 4 → Bool)) (hS : S.card=12)
    (g : Fin k → (Finset (Fin 4) → ZMod 2)) (hg : ∀ i,g i∈lowDegreeBooleanCode 4 1)
    (hmean : ∀ i,∑ x∈S,(booleanValueSign (g i (boolCoordinateSupport x)) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x∈S,
      (booleanValueSign (g i (boolCoordinateSupport x)) : ℝ)*
        (booleanValueSign (g j (boolCoordinateSupport x)) : ℝ)=0) : k≤3 := by
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  have hproper : S≠Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    simp only [hS,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hc
    norm_num at hc
  have hh := affine_unbiased_output_complement_budget S hnonempty hproper g hg hmean hpair
  rw [hS] at hh
  norm_num at hh
  omega

end
end EntropyDesigns
