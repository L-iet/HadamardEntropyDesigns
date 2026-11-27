/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPlotkinSupport.SharedSeed
public import EntropyPlotkinSupport.NegativeGram
public import EntropySupportFace.SourceConsequences
@[expose] public section
namespace EntropyDesigns.PlotkinSupport
noncomputable section
open SupportFace
open scoped BigOperators

def mixedRow {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) :
    MixedBlock k i0 → ℝ := fun j => (walshChar e (x i0)*walshChar e (x j.val):ℤ)

theorem mixedRow_self {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) :
    (∑ j : MixedBlock k i0,mixedRow e i0 x j*mixedRow e i0 x j)=(k-1:ℕ) := by
  have hval (j : MixedBlock k i0) : mixedRow e i0 x j*mixedRow e i0 x j=1 := by
    have h0 := walshChar_sq e (x i0)
    have hj := walshChar_sq e (x j.val)
    have h : (walshChar e (x i0)*walshChar e (x j.val))^2=(1:ℤ) := by
      rw [mul_pow,h0,hj];norm_num
    have hreal : ((walshChar e (x i0)*walshChar e (x j.val):ℤ):ℝ)^2=1 := by exact_mod_cast h
    simpa only [pow_two,mixedRow] using hreal
  simp only [hval,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [card_mixed_blocks]

theorem mixedRow_pair {k s : ℕ} (hk : k≤2^s)
    (e : Finset (Fin s)) (i0 : Fin k) (x y : BlockSeeds k s)
    (hshared : x i0=y i0) (horth : fullSourceInner e i0 x y=0) :
    (∑ j : MixedBlock k i0,mixedRow e i0 x j*mixedRow e i0 y j)=
      -((2:ℝ)^s-(k:ℝ)+1) := by
  classical
  let g (j : Fin k) : ℤ := relativeChar e x y i0*relativeChar e x y j
  have hsum : (∑ j : Fin k,g j)=(k:ℤ)-(2:ℤ)^s :=
    shared_seed_relative_sum hk e i0 x y hshared horth
  have hself : g i0=1 := by
    rcases relativeChar_sign e x y i0 with h|h <;> simp [g,h]
  letI : Unique {j : Fin k // ¬j≠i0} := {
    default := ⟨i0,by simp⟩
    uniq := fun j => Subtype.ext (not_not.mp j.property) }
  have hdefault : (default : {j : Fin k // ¬j≠i0}).val=i0 :=
    not_not.mp (default : {j : Fin k // ¬j≠i0}).property
  have hsplit : (∑ j : MixedBlock k i0,g j.val)+g i0=∑ j : Fin k,g j := by
    simpa [MixedBlock,hdefault] using Fintype.sum_subtype_add_sum_subtype (fun j : Fin k => j≠i0) g
  have hoff : (∑ j : MixedBlock k i0,g j.val)=(k:ℤ)-(2:ℤ)^s-1 := by omega
  have hreal : (∑ j : MixedBlock k i0,(g j.val:ℝ))=(k:ℝ)-(2:ℝ)^s-1 := by exact_mod_cast hoff
  calc
    _=(∑ j : MixedBlock k i0,(g j.val:ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [mixedRow,g,relativeChar,Int.cast_mul]
      ring
    _= -((2:ℝ)^s-(k:ℝ)+1) := by rw [hreal];ring

end
end EntropyDesigns.PlotkinSupport
