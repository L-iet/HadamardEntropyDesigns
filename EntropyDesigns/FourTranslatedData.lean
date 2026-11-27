/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourWalshFinite
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace EntropyDesigns
def fourTranslatedWeights (s x : Fin 4 → Bool) : ℚ :=
  fourTrapRationalWeights (fun i => xor (x i) (s i))

def fourUniformWeights (i : Fin 5) (b : Bool) (x : Fin 4 → Bool) : ℚ :=
  if fourHighCharacter i x=bitSign b then 1/8 else 0


end EntropyDesigns
