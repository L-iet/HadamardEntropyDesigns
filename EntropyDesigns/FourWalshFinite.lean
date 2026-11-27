/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.TrapRationalData
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace EntropyDesigns
def fourHighCharacter (i : Fin 5) (x : Fin 4 → Bool) : ℤ :=
  ∏ j : Fin 4, if j.val=i.val then 1 else bitSign (x j)
def fourLowKernel (x y : Fin 4 → Bool) : ℤ :=
  1+(∑ i : Fin 4, bitSign (x i)*bitSign (y i))+
    ∑ ij : Fin 4×Fin 4, if ij.1 < ij.2 then
      bitSign (x ij.1)*bitSign (x ij.2)*bitSign (y ij.1)*bitSign (y ij.2) else 0

theorem four_walsh_kernel_certificate :
    ∀ x y : Fin 4 → Bool,
      (16 : ℤ)*(if y=x then 1 else 0)=fourLowKernel x y+
        ∑ i : Fin 5, fourHighCharacter i x*fourHighCharacter i y := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool]
  repeat' apply And.intro
  all_goals decide +kernel

theorem four_high_character_certificate :
    (∀ i : Fin 5, ∑ x, fourHighCharacter i x=0) ∧
    (∀ i : Fin 5, ∀ j : Fin 4, ∑ x, fourHighCharacter i x*bitSign (x j)=0) ∧
    (∀ i : Fin 5, ∀ j k : Fin 4, j≠k →
      ∑ x, fourHighCharacter i x*bitSign (x j)*bitSign (x k)=0) ∧
    (∀ i j : Fin 5, ∑ x, fourHighCharacter i x*fourHighCharacter j x=if i=j then 16 else 0) ∧
    (∀ x : Fin 4 → Bool, (∏ i : Fin 5, fourHighCharacter i x)=1) ∧
    (∀ v : Fin 5 → Bool, (∏ i, bitSign (v i))=1 →
      ∃ x : Fin 4 → Bool, ∀ i, fourHighCharacter i x=bitSign (v i)) := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool]
  repeat' apply And.intro
  all_goals decide +kernel


end EntropyDesigns
