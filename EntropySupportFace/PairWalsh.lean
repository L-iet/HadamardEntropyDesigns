/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.WalshInversion
public import EntropyDesigns.Pushforward
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators
abbrev PairSeed (s : ℕ) := (Fin s → Bool) × (Fin s → Bool)
abbrev PairMask (s : ℕ) := Finset (Fin s) × Finset (Fin s)
def pairChar {s : ℕ} (P : PairMask s) (x : PairSeed s) : ℝ :=
  (walshChar P.1 x.1:ℝ)*(walshChar P.2 x.2:ℝ)
def pairCoefficient {s : ℕ} (q : PairSeed s → ℝ) (P : PairMask s) : ℝ :=
  ∑ x,q x*pairChar P x

theorem pairChar_dual_orthogonality {s : ℕ} (x y : PairSeed s) :
    (∑ P : PairMask s,pairChar P x*pairChar P y)=
      if x=y then ((2:ℝ)^s)^2 else 0 := by
  unfold pairChar
  rw [Fintype.sum_prod_type]
  have hfactor : (∑ S : Finset (Fin s),∑ T : Finset (Fin s),
      ((walshChar S x.1:ℝ)*(walshChar T x.2:ℝ))*
        ((walshChar S y.1:ℝ)*(walshChar T y.2:ℝ)))=
      (∑ S : Finset (Fin s),(walshChar S x.1:ℝ)*(walshChar S y.1:ℝ))*
      (∑ T : Finset (Fin s),(walshChar T x.2:ℝ)*(walshChar T y.2:ℝ)) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [hfactor,walshChar_real_dual_orthogonality,walshChar_real_dual_orthogonality]
  by_cases h1 : x.1=y.1 <;> by_cases h2 : x.2=y.2 <;>
    simp [h1,h2,Prod.ext_iff,pow_two]

theorem pair_walsh_inversion {s : ℕ} (q : PairSeed s → ℝ) (x : PairSeed s) :
    (∑ P : PairMask s,pairCoefficient q P*pairChar P x)=((2:ℝ)^s)^2*q x := by
  classical
  simp only [pairCoefficient,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc,← Finset.mul_sum,pairChar_dual_orthogonality]
  simp [mul_comm]

theorem pair_uniform_of_coefficients {s : ℕ} (q : PairSeed s → ℝ)
    (hcoeff : ∀ P,pairCoefficient q P=if P=(∅,∅) then 1 else 0) :
    ∀ x,q x=1/((2:ℝ)^s)^2 := by
  intro x
  have h := pair_walsh_inversion q x
  simp only [hcoeff] at h
  simp [pairChar,walshChar] at h
  apply (eq_div_iff (pow_ne_zero 2 (pow_ne_zero s (by norm_num : (2:ℝ)≠0)))).mpr
  nlinarith
end
end EntropyDesigns.SupportFace
