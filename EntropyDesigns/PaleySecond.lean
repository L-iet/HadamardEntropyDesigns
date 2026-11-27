/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.Paley
public import Mathlib.Data.Matrix.Block
public import Mathlib.Tactic.NoncommRing

/-! Original formalization of the classical second Paley construction.
Mathematical source: R. E. A. C. Paley, On Orthogonal Matrices (1933),
https://doi.org/10.1002/sapm1933121311 . No external implementation copied. -/
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns
open scoped Matrix

def conferenceDouble {ι : Type*} [DecidableEq ι] (C : Matrix ι ι ℤ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ :=
  Matrix.fromBlocks (C+1) (C-1) (C-1) (-C-1)

theorem conferenceDouble_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (q : ℤ) (hs : Cᵀ=C) (hg : C*C=q • 1) :
    conferenceDouble C*(conferenceDouble C)ᵀ=(2*(q+1)) • 1 := by
  have h₁ : (C+1)*(C+1)+(C-1)*(C-1)=(2*(q+1)) • 1 := by
    calc
      _ = 2 • (C*C+1) := by noncomm_ring
      _ = _ := by rw [hg]; simp [smul_add, add_smul, mul_add, mul_smul]
  have h₂ : (C+1)*(C-1)+(C-1)*(-C-1)=0 := by noncomm_ring
  have h₃ : (C-1)*(C+1)+(-C-1)*(C-1)=0 := by noncomm_ring
  have h₄ : (C-1)*(C-1)+(-C-1)*(-C-1)=(2*(q+1)) • 1 := by
    calc
      _ = (C+1)*(C+1)+(C-1)*(C-1) := by noncomm_ring
      _ = _ := h₁
  simp only [conferenceDouble, Matrix.fromBlocks_transpose,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_neg,
    Matrix.transpose_one, hs, Matrix.fromBlocks_multiply, h₁, h₂, h₃, h₄]
  simpa only [smul_zero,Matrix.fromBlocks_one] using
    (Matrix.fromBlocks_smul (2*(q+1)) (1 : Matrix ι ι ℤ) (0 : Matrix ι ι ℤ) (0 : Matrix ι ι ℤ) (1 : Matrix ι ι ℤ)).symm

theorem conferenceDouble_sign {ι : Type*} [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hd : ∀ i,C i i=0)
    (ho : ∀ i j,i≠j → C i j=1 ∨ C i j= -1)
    (i j : ι ⊕ ι) : conferenceDouble C i j=1 ∨ conferenceDouble C i j= -1 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases h : i=j
      · subst j; simp [conferenceDouble, hd, Matrix.one_apply]
      · rcases ho i j h with hc|hc <;> simp [conferenceDouble, Matrix.one_apply,h,hc]
    | inr j =>
      by_cases h : i=j
      · subst j; simp [conferenceDouble, hd, Matrix.one_apply]
      · rcases ho i j h with hc|hc <;> simp [conferenceDouble, Matrix.one_apply,h,hc]
  | inr i =>
    cases j with
    | inl j =>
      by_cases h : i=j
      · subst j; simp [conferenceDouble, hd, Matrix.one_apply]
      · rcases ho i j h with hc|hc <;> simp [conferenceDouble, Matrix.one_apply,h,hc]
    | inr j =>
      by_cases h : i=j
      · subst j; simp [conferenceDouble, hd, Matrix.one_apply]
      · rcases ho i j h with hc|hc <;> simp [conferenceDouble, Matrix.one_apply,h,hc]

theorem odd_character_row_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F≠2) (x : F) : (∑ y,paleyCharacterMatrix F x y)=0 := by
  have he : (∑ y : F,quadraticChar F (y+ -x))=∑ y : F,quadraticChar F y :=
    Equiv.sum_comp (Equiv.addRight (-x)) (quadraticChar F)
  calc
    _ = ∑ y : F,quadraticChar F y := by simpa only [paleyCharacterMatrix,sub_eq_add_neg] using he
    _ = 0 := quadraticChar_sum_zero hchar

theorem odd_character_gram {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F≠2) :
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
  · have hh := quadratic_char_correlation hchar x z hxz
    simpa [Matrix.smul_apply,Matrix.one_apply,Matrix.natCast_apply,hxz] using hh

theorem square_character_neg {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=1) (x : F) : quadraticChar F (-x)=quadraticChar F x := by
  have hs : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  have hn : quadraticChar F (-1)=1 := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr hs
  rw [show -x=(-1)*x by ring, map_mul, hn, one_mul]

def paleyConference (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Option F) (Option F) ℤ
  | none,none => 0
  | none,some _ => 1
  | some _,none => 1
  | some x,some y => paleyCharacterMatrix F x y

theorem paleyConference_transpose {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=1) : (paleyConference F)ᵀ=paleyConference F := by
  ext i j
  cases i with
  | none => cases j <;> rfl
  | some x =>
    cases j with
    | none => rfl
    | some y =>
      change quadraticChar F (x-y)=quadraticChar F (y-x)
      rw [show x-y= -(y-x) by ring,square_character_neg hres]

theorem paleyConference_diagonal {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (i : Option F) : paleyConference F i i=0 := by
  cases i <;> simp [paleyConference,paleyCharacterMatrix,quadraticChar_zero]

theorem paleyConference_off_diagonal {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (i j : Option F) (h : i≠j) : paleyConference F i j=1 ∨ paleyConference F i j= -1 := by
  cases i with
  | none => cases j <;> simp_all [paleyConference]
  | some x =>
    cases j with
    | none => simp [paleyConference]
    | some y =>
      have hn : y-x≠0 := sub_ne_zero.mpr (by intro he; subst y; exact h rfl)
      change quadraticChar F (y-x)=1 ∨ quadraticChar F (y-x)= -1
      exact sq_eq_one_iff.mp (quadraticChar_sq_one hn)

theorem paleyConference_gram {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=1) :
    paleyConference F*paleyConference F=(Fintype.card F : ℤ) • 1 := by
  have hchar : ringChar F≠2 := by
    intro h
    have hh := FiniteField.even_card_of_char_two h
    omega
  conv_lhs => rhs; rw [← paleyConference_transpose hres]
  ext i j
  cases i with
  | none =>
    cases j with
    | none =>
      simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_option,
        paleyConference,Matrix.smul_apply,Matrix.one_apply]
    | some y =>
      simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_option,
        paleyConference,Matrix.smul_apply,Matrix.one_apply,odd_character_row_sum hchar]
  | some x =>
    cases j with
    | none =>
      simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_option,
        paleyConference,Matrix.smul_apply,Matrix.one_apply,odd_character_row_sum hchar]
    | some y =>
      have hh := congrArg (fun M : Matrix F F ℤ => M x y) (odd_character_gram hchar)
      simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.sub_apply,
        Matrix.smul_apply,paleyOnesMatrix,smul_eq_mul,Matrix.one_apply] at hh
      simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_option,
        paleyConference,one_mul,Matrix.smul_apply,smul_eq_mul,
        Matrix.one_apply,Option.some.injEq]
      linarith

theorem paley_second_integer_hadamard {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hres : Fintype.card F%4=1) : Matrix.IsHadamard (conferenceDouble (paleyConference F)) := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    exact conferenceDouble_sign _ paleyConference_diagonal paleyConference_off_diagonal i j
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Fintype.card_sum,
      Fintype.card_option,Nat.cast_add,Nat.cast_one, two_mul] using
      conferenceDouble_gram _ _ (paleyConference_transpose hres) (paleyConference_gram hres)
  · apply isRegular_iff_ne_zero.mpr
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Option F ⊕ Option F)≠0)

theorem paley_second_finite_field_exists (F : Type*) [Field F] [Fintype F]
    (hres : Fintype.card F%4=1) :
    ∃ H : Matrix (Fin (2*(Fintype.card F+1))) (Fin (2*(Fintype.card F+1))) ℝ,
      Matrix.IsHadamard H := by
  classical
  let e : (Option F ⊕ Option F) ≃ Fin (2*(Fintype.card F+1)) :=
    (Fintype.equivFin _).trans (finCongr (by simp; omega))
  have hH := integer_hadamard_real (conferenceDouble (paleyConference F))
    (paley_second_integer_hadamard hres)
  exact ⟨_,hH.reindex e e⟩

def orderTwoSign : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]

theorem orderTwoSign_hadamard : Matrix.IsHadamard orderTwoSign := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    fin_cases i <;> fin_cases j <;> norm_num [orderTwoSign]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [orderTwoSign,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]
  · norm_num [isRegular_iff_ne_zero]

theorem odd_prime_twice_successor_hadamard {p : ℕ} (hp : p.Prime) (hodd : p≠2) :
    ∃ H : Matrix (Fin (2*(p+1))) (Fin (2*(p+1))) ℝ,Matrix.IsHadamard H := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hmod : p%4=1 ∨ p%4=3 := by
    have hh := hp.eq_two_or_odd
    omega
  rcases hmod with hmod|hmod
  · have hc : Fintype.card (ZMod p)=p := ZMod.card p
    obtain ⟨H,hH⟩ := paley_second_finite_field_exists (ZMod p) (by rw [hc]; exact hmod)
    let e : Fin (2*(Fintype.card (ZMod p)+1)) ≃ Fin (2*(p+1)) := finCongr (by rw [hc])
    exact ⟨_,hH.reindex e e⟩
  · obtain ⟨H,hH⟩ := paley_finite_field_exists (ZMod p) (by simpa using hmod)
    have hh := orderTwoSign_hadamard.kronecker hH
    let e : (Fin 2 × Fin (Fintype.card (ZMod p)+1)) ≃ Fin (2*(p+1)) :=
      (Fintype.equivFin _).trans (finCongr (by simp))
    exact ⟨_,hh.reindex e e⟩

end EntropyDesigns
