/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators Matrix

def bitHadamardSign {n : ℕ} (masks : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if Nat.testBit (masks i) j.val then -1 else 1

def benchmarkRowMask12 : Fin 12 → ℕ := ![0,2954,1814,3628,3162,2230,366,732,1464,2928,1762,3524]

def benchmarkHadamard12 : Matrix (Fin 12) (Fin 12) ℤ := bitHadamardSign benchmarkRowMask12

def benchmarkRowMask20 : Fin 20 → ℕ := ![0,649754,250934,501868,1003736,958898,869222,689870,331166,662332,276090,552180,55786,111572,223144,446288,892576,736578,424582,849164]

def benchmarkHadamard20 : Matrix (Fin 20) (Fin 20) ℤ := bitHadamardSign benchmarkRowMask20

end EntropyDesigns
