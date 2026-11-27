/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Data
public import EntropyCubic.Certificates
public import Mathlib.Data.Nat.Bitwise
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators symmDiff
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem naturalMaskSupport_injective_on_bits {r m n : ℕ} (hm : m<2^r) (hn : n<2^r)
    (heq : naturalMaskSupport r m=naturalMaskSupport r n) : m=n := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k<r
  · have hh := Finset.ext_iff.mp heq (⟨k,hk⟩ : Fin r)
    have hiff : m.testBit k=true ↔ n.testBit k=true := by
      simpa only [naturalMaskSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hh
    cases h1 : m.testBit k <;> cases h2 : n.testBit k <;> simp_all
  · have hpow : 2^r≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    have h1 : m.testBit k=false := Nat.testBit_eq_false_of_lt (hm.trans_le hpow)
    have h2 : n.testBit k=false := Nat.testBit_eq_false_of_lt (hn.trans_le hpow)
    rw [h1,h2]

def benchmarkLabelMask12 : Fin 12 → ℕ := ![0,5,3,6,13,11,7,14,4,8,1,2]

def benchmarkLabels12 (j : Fin 12) : Finset (Fin 4) := naturalMaskSupport 4 (benchmarkLabelMask12 j)

def benchmarkPolynomialMasks12 : Fin 11 → List ℕ := ![[1],[2],[4],[3,4,5,6,8,11],[1,3,4,8,9,11],[1,2,5,6,7,8,11],[1,2,4,5,9,10,11],[2,4,7,8,10,11],[1,6,8,10,11],[1,2,3,4,6,7,9,10,11],[2,3,5,7,8,9,11]]

def benchmarkPolynomial12 (i : Fin 11) : Finset (Fin 4) → ZMod 2 :=
 squarefreeBooleanPolynomial (polynomialMaskTerms 4 (benchmarkPolynomialMasks12 i))

theorem benchmarkLabelMask12_bound : ∀ j : Fin 12,benchmarkLabelMask12 j<2^4 := by decide

theorem benchmarkLabelMask12_injective : Function.Injective benchmarkLabelMask12 := by decide

theorem benchmarkLabels12_injective : Function.Injective benchmarkLabels12 := by
  intro i j h
  apply benchmarkLabelMask12_injective
  exact naturalMaskSupport_injective_on_bits (benchmarkLabelMask12_bound i) (benchmarkLabelMask12_bound j) h

def benchmarkLabelMask20 : Fin 20 → ℕ := ![0,13,27,22,12,25,19,7,15,30,29,26,21,10,20,8,16,1,3,6]

def benchmarkLabels20 (j : Fin 20) : Finset (Fin 5) := naturalMaskSupport 5 (benchmarkLabelMask20 j)

def benchmarkPolynomialMasks20 : Fin 19 → List ℕ := ![[1],[2],[4],[8],[16],[1,3,4,6,7,8,12,14,19,20],[3,5,7,9,10,12,13,16,17,18],[1,2,4,5,6,7,8,9,10,13,14,18],[3,4,5,6,7,8,16,19,20],[1,2,7,8,9,11,12,16,19],[1,4,6,7,8,9,10,11,13,16],[1,2,3,4,6,7,11,14,16],[1,4,10,11,12,14,19],[2,4,5,6,8,11,12,13,17,18],[2,3,7,8,10,11,12,13,16,17,20],[1,3,10,11,12,13,14,16],[1,2,3,5,6,8,13,14,17,20],[2,4,6,7,8,9,11,12,14,16,18],[1,3,4,5,7,9,13,14,16]]

def benchmarkPolynomial20 (i : Fin 19) : Finset (Fin 5) → ZMod 2 :=
 squarefreeBooleanPolynomial (polynomialMaskTerms 5 (benchmarkPolynomialMasks20 i))

theorem benchmarkLabelMask20_bound : ∀ j : Fin 20,benchmarkLabelMask20 j<2^5 := by decide

theorem benchmarkLabelMask20_injective : Function.Injective benchmarkLabelMask20 := by decide

theorem benchmarkLabels20_injective : Function.Injective benchmarkLabels20 := by
  intro i j h
  apply benchmarkLabelMask20_injective
  exact naturalMaskSupport_injective_on_bits (benchmarkLabelMask20_bound i) (benchmarkLabelMask20_bound j) h

end EntropyDesigns
