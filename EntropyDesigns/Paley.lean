/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.ModularSeed
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns
open scoped Matrix

theorem mobius_forward_ne_one {F : Type*} [Field F] {a b x : F} (hab : a≠b) (hxb : x≠b) :
    (x-a)/(x-b) ≠ 1 := by
  intro h
  have hh := (div_eq_iff (sub_ne_zero.mpr hxb)).mp h
  apply hab
  linear_combination -hh

theorem mobius_backward_ne_base {F : Type*} [Field F] {a b y : F} (hab : a≠b) (hy : y≠1) :
    (b*y-a)/(y-1) ≠ b := by
  intro h
  have hh := (div_eq_iff (sub_ne_zero.mpr hy)).mp h
  apply hab
  linear_combination -hh

def completedMobius {F : Type*} [Field F] [DecidableEq F] (a b : F) (hab : a≠b) : F ≃ F where
  toFun x := if x=b then 1 else (x-a)/(x-b)
  invFun y := if y=1 then b else (b*y-a)/(y-1)
  left_inv x := by
    by_cases hx : x=b
    · simp [hx]
    · have hy := mobius_forward_ne_one hab hx
      simp only [if_neg hx,if_neg hy]
      apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
      field_simp [sub_ne_zero.mpr hx] <;> ring
  right_inv y := by
    by_cases hy : y=1
    · simp [hy]
    · have hx := mobius_backward_ne_base hab hy
      simp only [if_neg hy,if_neg hx]
      apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
      field_simp [sub_ne_zero.mpr hy] <;> ring

theorem quadratic_char_ratio {F : Type*} [Field F] [Fintype F] [DecidableEq F] (u v : F) (hv : v≠0) :
    quadraticChar F u*quadraticChar F v=quadraticChar F (u/v) := by
  have hh : quadraticChar F (u/v)*quadraticChar F v=quadraticChar F u := by
    rw [← map_mul,div_mul_cancel₀ u hv]
  calc
    _ = (quadraticChar F (u/v)*quadraticChar F v)*quadraticChar F v := by rw [hh]
    _ = quadraticChar F (u/v)*(quadraticChar F v)^2 := by ring
    _ = _ := by rw [quadraticChar_sq_one hv,mul_one]

theorem quadratic_char_correlation {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F≠2) (a b : F) (hab : a≠b) :
    (∑ x : F,quadraticChar F (x-a)*quadraticChar F (x-b))= -1 := by
  let e := completedMobius a b hab
  have ht (x : F) : quadraticChar F (x-a)*quadraticChar F (x-b)=
      quadraticChar F (e x)-(if x=b then (1 : ℤ) else 0) := by
    by_cases hx : x=b
    · subst x
      simp [e,completedMobius,quadraticChar_zero]
    · simp only [e,completedMobius,Equiv.coe_fn_mk,if_neg hx,sub_zero]
      exact quadratic_char_ratio _ _ (sub_ne_zero.mpr hx)
  simp_rw [ht]
  rw [Finset.sum_sub_distrib,Equiv.sum_comp e (quadraticChar F),quadraticChar_sum_zero hchar]
  simp

theorem odd_paley_char_ne_two {F : Type*} [Field F] [Fintype F]
    (hres : Fintype.card F%4=3) : ringChar F≠2 := by
  intro h
  have hh := FiniteField.even_card_of_char_two h
  omega

def paleyOnesMatrix (F : Type*) : Matrix F F ℤ := fun _ _ => 1

def paleyCharacterMatrix (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Matrix F F ℤ :=
  fun x y => quadraticChar F (y-x)

theorem paley_character_neg {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=3) (x : F) : quadraticChar F (-x)= -quadraticChar F x := by
  have hs : ¬IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    exact not_ne_iff.mpr hres
  have hn : quadraticChar F (-1)= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hs
  calc
    _ = quadraticChar F ((-1)*x) := by rw [neg_one_mul]
    _ = quadraticChar F (-1)*quadraticChar F x := map_mul _ _ _
    _ = _ := by rw [hn,neg_one_mul]

theorem paley_character_transpose {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=3) :
    (paleyCharacterMatrix F)ᵀ= -paleyCharacterMatrix F := by
  ext x y
  change quadraticChar F (x-y)= -quadraticChar F (y-x)
  rw [show x-y= -(y-x) by ring]
  exact paley_character_neg hres _

theorem paley_character_row_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=3) (x : F) : (∑ y,paleyCharacterMatrix F x y)=0 := by
  have he : (∑ y : F,quadraticChar F (y+ -x))=∑ y : F,quadraticChar F y :=
    Equiv.sum_comp (Equiv.addRight (-x)) (quadraticChar F)
  calc
    _ = ∑ y : F,quadraticChar F y := by simpa only [paleyCharacterMatrix,sub_eq_add_neg] using he
    _ = 0 := quadraticChar_sum_zero (odd_paley_char_ne_two hres)

theorem paley_character_gram {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=3) :
    paleyCharacterMatrix F*(paleyCharacterMatrix F)ᵀ=(Fintype.card F : ℤ) • 1-paleyOnesMatrix F := by
  ext x z
  change (∑ y : F,quadraticChar F (y-x)*quadraticChar F (y-z))=
    (((Fintype.card F : ℤ) • (1 : Matrix F F ℤ)) x z)-1
  by_cases hxz : x=z
  · subst z
    have ht (y : F) : quadraticChar F (y-x)*quadraticChar F (y-x)=
        1-(if y=x then (1 : ℤ) else 0) := by
      by_cases hy : y=x
      · subst y
        simp [quadraticChar_zero]
      · have hh := quadraticChar_sq_one (sub_ne_zero.mpr hy)
        simpa only [pow_two,if_neg hy,sub_zero] using hh
    simp_rw [ht]
    simp [Finset.sum_sub_distrib,Matrix.smul_apply,Matrix.one_apply,Matrix.natCast_apply]
  · have hh := quadratic_char_correlation (odd_paley_char_ne_two hres) x z hxz
    simpa [Matrix.smul_apply,Matrix.one_apply,Matrix.natCast_apply,hxz] using hh

def paleyLowerMatrix (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Matrix F F ℤ :=
  paleyCharacterMatrix F-1

theorem paley_lower_gram {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=3) :
    paleyLowerMatrix F*(paleyLowerMatrix F)ᵀ=
      ((Fintype.card F : ℤ)+1) • 1-paleyOnesMatrix F := by
  calc
    _ = paleyCharacterMatrix F*(paleyCharacterMatrix F)ᵀ-paleyCharacterMatrix F-
        (paleyCharacterMatrix F)ᵀ+1 := by
      simp only [paleyLowerMatrix,Matrix.transpose_sub,Matrix.transpose_one,Matrix.sub_mul,
        Matrix.mul_sub,Matrix.mul_one,Matrix.one_mul]
      abel
    _ = _ := by
      rw [paley_character_gram hres,paley_character_transpose hres]
      ext x y
      simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul]
      ring

theorem paley_lower_row_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=3) (x : F) : (∑ y,paleyLowerMatrix F x y)= -1 := by
  simp only [paleyLowerMatrix,Matrix.sub_apply,Finset.sum_sub_distrib]
  rw [paley_character_row_sum hres]
  simp [Matrix.one_apply]

theorem paley_lower_sign {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (x y : F) : paleyLowerMatrix F x y=1 ∨ paleyLowerMatrix F x y= -1 := by
  by_cases h : x=y
  · subst y
    simp [paleyLowerMatrix,paleyCharacterMatrix,Matrix.one_apply]
  · have hh := quadraticChar_dichotomy (sub_ne_zero.mpr (Ne.symm h))
    simpa [paleyLowerMatrix,paleyCharacterMatrix,Matrix.one_apply,h] using hh

def paleyHadamardMatrix (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Option F) (Option F) ℤ
  | none, _ => 1
  | some _, none => 1
  | some x, some y => paleyLowerMatrix F x y

theorem paley_hadamard_sign {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (x y : Option F) : paleyHadamardMatrix F x y=1 ∨ paleyHadamardMatrix F x y= -1 := by
  cases x with
  | none => exact Or.inl rfl
  | some x =>
    cases y with
    | none => exact Or.inl rfl
    | some y => exact paley_lower_sign x y

theorem paley_hadamard_gram {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=3) :
    paleyHadamardMatrix F*(paleyHadamardMatrix F)ᵀ=((Fintype.card F : ℤ)+1) • 1 := by
  ext x z
  cases x with
  | none =>
    cases z with
    | none => simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_option,paleyHadamardMatrix,Matrix.smul_apply,Matrix.one_apply]
    | some z => simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_option,paleyHadamardMatrix,Matrix.smul_apply,Matrix.one_apply,paley_lower_row_sum hres]
  | some x =>
    cases z with
    | none => simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_option,paleyHadamardMatrix,Matrix.smul_apply,Matrix.one_apply,paley_lower_row_sum hres]
    | some z =>
      have hh := congrArg (fun M : Matrix F F ℤ => M x z) (paley_lower_gram hres)
      have hs : (∑ y : F,paleyLowerMatrix F x y*paleyLowerMatrix F z y)=
          ((Fintype.card F : ℤ)+1)*(if x=z then 1 else 0)-1 := by
        by_cases hxz : x=z <;>
          simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.sub_apply,Matrix.smul_apply,
            paleyOnesMatrix,Matrix.one_apply,Matrix.natCast_apply,smul_eq_mul,hxz] using hh
      simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_option,paleyHadamardMatrix,
        one_mul,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Option.some.injEq]
      rw [hs]
      ring

theorem paley_integer_hadamard {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=3) : Matrix.IsHadamard (paleyHadamardMatrix F) := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro x y
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (paley_hadamard_sign x y)
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Fintype.card_option,Nat.cast_add,Nat.cast_one] using paley_hadamard_gram hres
  · apply isRegular_iff_ne_zero.mpr
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Option F) ≠ 0)

def realMatrixOfInteger {ι : Type*} (H : Matrix ι ι ℤ) : Matrix ι ι ℝ := fun i j => (H i j : ℝ)

theorem integer_hadamard_real {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℤ) (hH : Matrix.IsHadamard H) : Matrix.IsHadamard (realMatrixOfInteger H) := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j) with h|h <;>
      simp [realMatrixOfInteger,h]
  · ext i j
    have hh := congrArg (fun M : Matrix ι ι ℤ => M i j) hH.mul_conjTranspose
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hh
    simpa [realMatrixOfInteger,Matrix.mul_apply,Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,Matrix.natCast_apply,smul_eq_mul] using hr
  · apply isRegular_iff_ne_zero.mpr
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)

theorem paley_finite_field_exists (F : Type*) [Field F] [Fintype F]
    (hres : Fintype.card F%4=3) :
    ∃ H : Matrix (Fin (Fintype.card F+1)) (Fin (Fintype.card F+1)) ℝ,Matrix.IsHadamard H := by
  classical
  let e : Option F ≃ Fin (Fintype.card F+1) := (Fintype.equivFin _).trans (finCongr (by simp))
  have hH := integer_hadamard_real (paleyHadamardMatrix F) (paley_integer_hadamard hres)
  exact ⟨_,hH.reindex e e⟩

theorem paley_three_power_exists (t : ℕ) :
    ∃ H : Matrix (Fin (3^(2*t+1)+1)) (Fin (3^(2*t+1)+1)) ℝ,Matrix.IsHadamard H := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let F := GaloisField 3 (2*t+1)
  letI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F=3^(2*t+1) := by
    simpa only [Nat.card_eq_fintype_card] using GaloisField.card (p := 3) (n := 2*t+1) (by omega)
  have hmod : 3^(2*t+1)%4=3 := by
    rw [pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  have hh := paley_finite_field_exists F (by simpa only [hc] using hmod)
  rw [hc] at hh
  exact hh

theorem paley_three_power_order_residue (t : ℕ) : (3^(2*t+1)+1)%8=4 := by
  rw [pow_add,pow_mul]
  norm_num [Nat.add_mod,Nat.mul_mod,Nat.pow_mod]
end EntropyDesigns
