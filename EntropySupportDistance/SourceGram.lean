/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.SourceCode
public import EntropyDesigns.WalshInversion
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def fullSourceRow {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) :
    Fin k × Finset (Fin s) → ℤ := fun a =>
  if a.2=∅ then walshChar e (x i0)*walshChar e (x a.1) else walshChar a.2 (x a.1)
def fullSourceInner {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x y : BlockSeeds k s) : ℤ :=
  ∑ j : Fin k,∑ S : Finset (Fin s),fullSourceRow e i0 x (j,S)*fullSourceRow e i0 y (j,S)
def relativeChar {k s : ℕ} (e : Finset (Fin s)) (x y : BlockSeeds k s) (j : Fin k) : ℤ :=
  walshChar e (x j)*walshChar e (y j)

theorem relativeChar_sign {k s : ℕ} (e : Finset (Fin s)) (x y : BlockSeeds k s) (j : Fin k) :
    relativeChar e x y j=1 ∨ relativeChar e x y j= -1 := by
  rcases walshChar_sign e (x j) with h|h <;> rcases walshChar_sign e (y j) with h'|h' <;>
    simp [relativeChar,h,h']

theorem fullSourceInner_formula {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x y : BlockSeeds k s) :
    fullSourceInner e i0 x y=(2:ℤ)^s*(∑ j : Fin k,if x j=y j then (1:ℤ) else 0)-(k:ℤ)+
      ∑ j : Fin k,relativeChar e x y i0*relativeChar e x y j := by
  classical
  have hblock (j : Fin k) :
      (∑ S : Finset (Fin s),fullSourceRow e i0 x (j,S)*fullSourceRow e i0 y (j,S))=
        (2:ℤ)^s*(if x j=y j then 1 else 0)+relativeChar e x y i0*relativeChar e x y j-1 := by
    have hp (S : Finset (Fin s)) : fullSourceRow e i0 x (j,S)*fullSourceRow e i0 y (j,S)=
        walshChar S (x j)*walshChar S (y j)+
          if S=∅ then relativeChar e x y i0*relativeChar e x y j-1 else 0 := by
      by_cases hS : S=∅
      · subst S;simp [fullSourceRow,relativeChar,walshChar];ring
      · simp [fullSourceRow,hS]
    simp only [hp,Finset.sum_add_distrib,walshChar_dual_orthogonality]
    by_cases hxy : x j=y j <;> simp [hxy] <;> ring
  unfold fullSourceInner
  simp_rw [hblock]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  ring

theorem relative_sum_lower {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x y : BlockSeeds k s) :
    2-(k:ℤ)≤∑ j : Fin k,relativeChar e x y i0*relativeChar e x y j := by
  classical
  let g (j : Fin k) := relativeChar e x y i0*relativeChar e x y j
  have hg (j : Fin k) : -1≤g j := by
    rcases relativeChar_sign e x y i0 with h|h <;> rcases relativeChar_sign e x y j with h'|h' <;>
      norm_num [g,h,h']
  have hself : g i0=1 := by rcases relativeChar_sign e x y i0 with h|h <;> norm_num [g,h]
  have hsum := Finset.sum_erase_add Finset.univ g (Finset.mem_univ i0)
  have hlower := Finset.sum_le_sum (s:=Finset.univ.erase i0) (fun j _ => hg j)
  have hc : (Finset.univ.erase i0).card=k-1 := by simp
  have hk : 1≤k := by have h := i0.isLt;omega
  simp only [Finset.sum_const,nsmul_eq_mul,hc,Int.ofNat_sub hk] at hlower
  rw [hself] at hsum
  change 2-(k:ℤ)≤∑ j,g j
  omega

theorem shared_block_inner_positive {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (hsize : 2*(k-1)<2^s) (x y : BlockSeeds k s) (j : Fin k) (hshared : x j=y j) :
    0<fullSourceInner e i0 x y := by
  classical
  have hcount : (1:ℤ)≤∑ a : Fin k,if x a=y a then (1:ℤ) else 0 := by
    have h := Finset.single_le_sum (fun a (_ : a∈Finset.univ) =>
      show (0:ℤ) ≤ (if x a=y a then (1:ℤ) else 0) by split <;> norm_num) (Finset.mem_univ j)
    simpa [hshared] using h
  have hp : (0:ℤ)<(2:ℤ)^s := pow_pos (by decide) s
  have hmul := mul_le_mul_of_nonneg_left hcount hp.le
  have hmix := relative_sum_lower e i0 x y
  have hk : 1≤k := by have h := i0.isLt;omega
  have hlarge : (2:ℤ)*((k:ℤ)-1)<(2:ℤ)^s := by
    have h : (2:ℤ)*((k-1:ℕ):ℤ)<(2:ℤ)^s := by exact_mod_cast hsize
    simpa only [Int.ofNat_sub hk, Int.natCast_one] using h
  rw [fullSourceInner_formula]
  nlinarith
end
end EntropyDesigns.SupportFace
