/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import EntropyDesigns.SignLaws
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Fin.Tuple.Basic
@[expose] public section
namespace EntropyDesigns
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
abbrev SmallTrapMomentIndex (d : Nat) := Unit ⊕ (Fin d ⊕ (Fin d×Fin d))

def rationalTrapMomentMatrix (d : Nat) : Matrix (SmallTrapMomentIndex d) (Fin d → Bool) ℚ :=
  Sum.elim (fun _ _ => 1) (Sum.elim (fun i x => (bitSign (x i) : ℚ))
    (fun ij x => (bitSign (x ij.1) : ℚ)*(bitSign (x ij.2) : ℚ)))

def rationalTrapMomentTarget (d : Nat) : SmallTrapMomentIndex d → ℚ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 0) (fun ij => if ij.1=ij.2 then 1 else 0))


def fourTrapNegativeCount (x : Fin 4 → Bool) : Nat := (Finset.univ.filter (fun i => x i=true)).card

def fourTrapRationalWeights (x : Fin 4 → Bool) : ℚ := if fourTrapNegativeCount x=0 then 1/6 else if fourTrapNegativeCount x=2 ∨ fourTrapNegativeCount x=3 then 1/12 else 0

theorem fourTrapSeedNumber_bound : ∀ x : Fin 4 → Bool,(∑ i : Fin 4,if x i then 2^i.val else 0)<16 := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

def fourTrapSeedNumber (x : Fin 4 → Bool) : Fin 16 := ⟨∑ i : Fin 4,if x i then 2^i.val else 0,fourTrapSeedNumber_bound x⟩

def fourTrapMomentNumber : SmallTrapMomentIndex 4 → Fin 21 := Sum.elim (fun _ => 0) (Sum.elim (fun i => ⟨1+i.val,by omega⟩) (fun ij => ⟨5+ij.1.val*4+ij.2.val,by omega⟩))

def fourTrapInterpolationTable : Matrix (Fin 16) (Fin 21) ℚ := !![(1/6),(1/12),(1/12),(1/12),(1/12),0,(1/12),(1/12),(1/12),0,0,(1/12),(1/12),0,0,0,(1/12),0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(-1/12),(-1/12),(1/6),(1/6),0,(-1/12),(-1/12),(-1/12),0,0,(-1/12),(-1/12),0,0,0,(1/6),0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(-1/12),(1/6),(-1/12),(1/6),0,(-1/12),(-1/12),(-1/12),0,0,(-1/12),(1/6),0,0,0,(-1/12),0,0,0,0;
  (1/12),(1/6),(-1/12),(-1/12),(1/6),0,(-1/12),(-1/12),(1/6),0,0,(-1/12),(-1/12),0,0,0,(-1/12),0,0,0,0;
  (1/12),(-1/12),(-1/12),(-1/12),(-1/12),0,(1/6),(1/6),(-1/12),0,0,(1/6),(-1/12),0,0,0,(-1/12),0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(-1/12),(1/6),(1/6),(-1/12),0,(-1/12),(-1/12),(-1/12),0,0,(1/6),(-1/12),0,0,0,(-1/12),0,0,0,0;
  (1/12),(1/6),(-1/12),(1/6),(-1/12),0,(-1/12),(1/6),(-1/12),0,0,(-1/12),(-1/12),0,0,0,(-1/12),0,0,0,0;
  (1/12),(-1/12),(-1/12),(-1/12),(-1/12),0,(1/6),(-1/12),(1/6),0,0,(-1/12),(1/6),0,0,0,(-1/12),0,0,0,0;
  (1/12),(1/6),(1/6),(-1/12),(-1/12),0,(1/6),(-1/12),(-1/12),0,0,(-1/12),(-1/12),0,0,0,(-1/12),0,0,0,0;
  (1/12),(-1/12),(-1/12),(-1/12),(-1/12),0,(-1/12),(1/6),(1/6),0,0,(-1/12),(-1/12),0,0,0,(1/6),0,0,0,0;
  (1/12),(-1/12),(-1/12),(-1/12),(-1/12),0,(-1/12),(-1/12),(-1/12),0,0,(1/6),(1/6),0,0,0,(1/6),0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

def fourTrapRationalInterpolation (x : Fin 4 → Bool) (r : SmallTrapMomentIndex 4) : ℚ := fourTrapInterpolationTable (fourTrapSeedNumber x) (fourTrapMomentNumber r)

def fourTrapRationalDual : SmallTrapMomentIndex 4 → ℚ := Sum.elim (fun _ => 7/72) (Sum.elim (fun _ => (1/144)) (fun ij => if ij.1.val < ij.2.val then (1/144) else 0))







def fiveTrapNegativeCount (x : Fin 5 → Bool) : Nat := (Finset.univ.filter (fun i => x i=true)).card

def fiveTrapRationalWeights (x : Fin 5 → Bool) : ℚ := if fiveTrapNegativeCount x=0 then 1/6 else if fiveTrapNegativeCount x=3 then 1/12 else 0

theorem fiveTrapSeedNumber_bound : ∀ x : Fin 5 → Bool,(∑ i : Fin 5,if x i then 2^i.val else 0)<32 := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

def fiveTrapSeedNumber (x : Fin 5 → Bool) : Fin 32 := ⟨∑ i : Fin 5,if x i then 2^i.val else 0,fiveTrapSeedNumber_bound x⟩

def fiveTrapMomentNumber : SmallTrapMomentIndex 5 → Fin 31 := Sum.elim (fun _ => 0) (Sum.elim (fun i => ⟨1+i.val,by omega⟩) (fun ij => ⟨6+ij.1.val*5+ij.2.val,by omega⟩))

def fiveTrapInterpolationTable : Matrix (Fin 32) (Fin 31) ℚ := !![(1/6),(1/6),(1/6),(1/6),(1/6),(1/6),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(-1/6),(-1/6),(-1/6),(-1/6),(-1/6),0,(1/4),(1/4),0,0,0,0,(1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(-1/6),(-1/6),(-1/6),(-1/6),(-1/6),0,(1/4),0,(1/4),0,0,0,0,(1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(1/12),(1/12),(1/12),(1/12),(1/3),0,(-1/4),0,0,0,0,0,(-1/4),(-1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(1/12),(1/12),(1/12),(1/12),(1/3),0,(-1/4),(-1/4),(-1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(1/12),(1/12),(1/3),(1/3),(1/3),0,(-1/4),(-1/4),(-1/4),0,0,0,(-1/4),(-1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(-1/6),(1/12),(-1/6),(1/12),(-1/6),0,0,0,0,0,0,0,0,(1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(1/12),(-1/6),(-1/6),(1/12),(-1/6),0,0,0,(1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(-1/6),(1/12),(1/12),(-1/6),(-1/6),0,0,0,0,0,0,0,(1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(1/12),(-1/6),(1/12),(-1/6),(-1/6),0,0,(1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  (1/12),(1/12),(1/12),(-1/6),(-1/6),(-1/6),0,(1/4),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

def fiveTrapRationalInterpolation (x : Fin 5 → Bool) (r : SmallTrapMomentIndex 5) : ℚ := fiveTrapInterpolationTable (fiveTrapSeedNumber x) (fiveTrapMomentNumber r)

def fiveTrapRationalDual : SmallTrapMomentIndex 5 → ℚ := Sum.elim (fun _ => 7/72) (Sum.elim (fun _ => (1/216)) (fun ij => if ij.1.val < ij.2.val then (1/216) else 0))








noncomputable section


end
end EntropyDesigns
