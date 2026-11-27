/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns
open scoped Matrix

def allOnesMatrix (n : ℕ) (R : Type*) [One R] : Matrix (Fin n) (Fin n) R := fun _ _ => 1

def modularCounterexampleSeed (n : ℕ) (R : Type*) [Ring R] : Matrix (Fin n) (Fin n) R :=
  allOnesMatrix n R-(2 : R) • 1

theorem allOnesMatrix_square (n : ℕ) (R : Type*) [CommRing R] :
    allOnesMatrix n R*allOnesMatrix n R=(n : R) • allOnesMatrix n R := by
  ext i j
  simp [allOnesMatrix,Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul]

theorem modularCounterexampleSeed_transpose (n : ℕ) (R : Type*) [CommRing R] :
    (modularCounterexampleSeed n R)ᵀ=modularCounterexampleSeed n R := by
  ext i j
  simp [modularCounterexampleSeed,allOnesMatrix,Matrix.one_apply,eq_comm]

theorem modularCounterexampleSeed_gram (n : ℕ) (R : Type*) [CommRing R] :
    modularCounterexampleSeed n R*(modularCounterexampleSeed n R)ᵀ=
      (4 : R) • 1+((n : R)-4) • allOnesMatrix n R := by
  rw [modularCounterexampleSeed_transpose]
  unfold modularCounterexampleSeed
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,allOnesMatrix_square]
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul,smul_smul]
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem modularCounterexampleSeed_sign (n : ℕ) (i j : Fin n) :
    modularCounterexampleSeed n ℤ i j=1 ∨ modularCounterexampleSeed n ℤ i j= -1 := by
  by_cases h : i=j <;> simp [modularCounterexampleSeed,allOnesMatrix,Matrix.one_apply,Matrix.ofNat_apply,h]

theorem modularCounterexampleSeed_modular_gram {n m : ℕ} (h : n % m=4 % m) :
    modularCounterexampleSeed n (ZMod m)*(modularCounterexampleSeed n (ZMod m))ᵀ=
      (n : ZMod m) • 1 := by
  have hn : (n : ZMod m)=4 := by
    exact (ZMod.natCast_eq_natCast_iff' n 4 m).mpr h
  rw [modularCounterexampleSeed_gram,hn]
  simp

theorem modularCounterexampleSeed_not_hadamard {n : ℕ} (hn : 4<n) :
    ¬ Matrix.IsHadamard (modularCounterexampleSeed n ℝ) := by
  intro h
  have hgram : modularCounterexampleSeed n ℝ*(modularCounterexampleSeed n ℝ)ᵀ=(n : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Fintype.card_fin] using h.mul_conjTranspose
  rw [modularCounterexampleSeed_gram] at hgram
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M ⟨0,by omega⟩ ⟨1,by omega⟩) hgram
  norm_num [Matrix.smul_apply,Matrix.one_apply,allOnesMatrix] at hh
  have hn' : (4 : ℝ)<n := by exact_mod_cast hn
  linarith

theorem modular_sign_cast_injective {m : ℕ} (hm : 3≤m) {x y : ℤ}
    (hx : x=1 ∨ x= -1) (hy : y=1 ∨ y= -1) (h : (x : ZMod m)=(y : ZMod m)) : x=y := by
  have hne : (-1 : ZMod m) ≠ 1 := by
    intro he
    rcases ZMod.neg_one_eq_one_iff.mp he with h|h <;> omega
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> norm_num at h ⊢
  · exact False.elim (hne h.symm)
  · exact False.elim (hne h)

theorem modularCounterexampleSeed_cast {n : ℕ} (R : Type*) [CommRing R] :
    (fun i j => (modularCounterexampleSeed n ℤ i j : R))=modularCounterexampleSeed n R := by
  ext i j
  by_cases h : i=j <;>
    simp [modularCounterexampleSeed,allOnesMatrix,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Matrix.ofNat_apply,h] <;> ring

theorem modularCounterexampleSeed_no_sign_lift {n m : ℕ} (hn : 4<n) (hm : 3≤m) :
    ¬ ∃ H : Matrix (Fin n) (Fin n) ℤ,
      (∀ i j,H i j=1 ∨ H i j= -1) ∧
      Matrix.IsHadamard (fun i j => (H i j : ℝ)) ∧
      ∀ i j,(H i j : ZMod m)=modularCounterexampleSeed n (ZMod m) i j := by
  rintro ⟨H,hH,hHad,hmod⟩
  have hEq : H=modularCounterexampleSeed n ℤ := by
    ext i j
    apply modular_sign_cast_injective hm (hH i j) (modularCounterexampleSeed_sign n i j)
    rw [hmod]
    exact (congrArg (fun M : Matrix (Fin n) (Fin n) (ZMod m) => M i j) (modularCounterexampleSeed_cast (n := n) (ZMod m))).symm
  apply modularCounterexampleSeed_not_hadamard hn
  rw [hEq] at hHad
  rwa [modularCounterexampleSeed_cast] at hHad

theorem modular_seed_without_sign_lift {n m : ℕ} (hn : 4<n) (hm : 3≤m) (hmod : n%m=4%m) :
    modularCounterexampleSeed n (ZMod m)*(modularCounterexampleSeed n (ZMod m))ᵀ=(n : ZMod m) • 1 ∧
      ¬ Matrix.IsHadamard (modularCounterexampleSeed n ℝ) ∧
      ¬ ∃ H : Matrix (Fin n) (Fin n) ℤ,
        (∀ i j,H i j=1 ∨ H i j= -1) ∧
        Matrix.IsHadamard (fun i j => (H i j : ℝ)) ∧
        ∀ i j,(H i j : ZMod m)=modularCounterexampleSeed n (ZMod m) i j :=
  ⟨modularCounterexampleSeed_modular_gram hmod,modularCounterexampleSeed_not_hadamard hn,
    modularCounterexampleSeed_no_sign_lift hn hm⟩

theorem modularCounterexampleSeed_isUnit {n p : ℕ} [Fact p.Prime]
    (hmod : n%p=4%p) (hfour : (4 : ZMod p) ≠ 0) :
    IsUnit (modularCounterexampleSeed n (ZMod p)) := by
  have hsq : modularCounterexampleSeed n (ZMod p)*modularCounterexampleSeed n (ZMod p)=(4 : ZMod p) • 1 := by
    have hg := modularCounterexampleSeed_modular_gram hmod
    rw [modularCounterexampleSeed_transpose] at hg
    have hn : (n : ZMod p)=4 := (ZMod.natCast_eq_natCast_iff' n 4 p).mpr hmod
    rwa [hn] at hg
  refine ⟨⟨modularCounterexampleSeed n (ZMod p),
    (4 : ZMod p)⁻¹ • modularCounterexampleSeed n (ZMod p),?_,?_⟩,rfl⟩
  · rw [Matrix.mul_smul,hsq,smul_smul,inv_mul_cancel₀ hfour,one_smul]
  · rw [Matrix.smul_mul,hsq,smul_smul,inv_mul_cancel₀ hfour,one_smul]

theorem odd_prime_four_ne_zero (p : ℕ) (hp : p.Prime) (hodd : Odd p) : (4 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h
  have hd' : p ∣ 2*2 := hd
  have htwo : p ∣ 2 := (hp.dvd_mul.mp hd').elim id id
  have heq : p=2 := (Nat.dvd_prime Nat.prime_two).mp htwo |>.resolve_left hp.ne_one
  subst p
  norm_num [Odd] at hodd

theorem infinite_prime_modular_counterexamples (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (t : ℕ) (ht : 1≤t) :
    let n := 4+4*p*t
    4 ∣ n ∧ 4<n ∧ IsUnit (modularCounterexampleSeed n (ZMod p)) ∧
      ¬ ∃ H : Matrix (Fin n) (Fin n) ℤ,
        (∀ i j,H i j=1 ∨ H i j= -1) ∧
        Matrix.IsHadamard (fun i j => (H i j : ℝ)) ∧
        ∀ i j,(H i j : ZMod p)=modularCounterexampleSeed n (ZMod p) i j := by
  dsimp only
  have hp3 : 3≤p := by
    have hp2 := hp.two_le
    have hne : p≠2 := by intro h; subst p; norm_num [Odd] at hodd
    omega
  have hn : 4<4+4*p*t := by nlinarith [hp.two_le]
  have hmod : (4+4*p*t)%p=4%p := by simp [Nat.add_mod,Nat.mul_mod]
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨⟨1+p*t,by ring⟩,hn,modularCounterexampleSeed_isUnit hmod (odd_prime_four_ne_zero p hp hodd),?_⟩
  exact modularCounterexampleSeed_no_sign_lift hn hp3

theorem infinitely_many_modular_seeds_without_lifts (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Set.Infinite {n : ℕ | 4 ∣ n ∧ 4<n ∧ IsUnit (modularCounterexampleSeed n (ZMod p)) ∧
      ¬ ∃ H : Matrix (Fin n) (Fin n) ℤ,
        (∀ i j,H i j=1 ∨ H i j= -1) ∧
        Matrix.IsHadamard (fun i j => (H i j : ℝ)) ∧
        ∀ i j,(H i j : ZMod p)=modularCounterexampleSeed n (ZMod p) i j} := by
  let f : ℕ → ℕ := fun t => 4+4*p*(t+1)
  have hf : Function.Injective f := by
    intro a b h
    have hh : 4*p*(a+1)=4*p*(b+1) := Nat.add_left_cancel h
    have hp0 : 0<4*p := Nat.mul_pos (by decide) hp.pos
    have hab := Nat.eq_of_mul_eq_mul_left hp0 hh
    omega
  apply (Set.infinite_range_of_injective hf).mono
  rintro n ⟨t,rfl⟩
  exact infinite_prime_modular_counterexamples p hp hodd (t+1) (by omega)
end EntropyDesigns
