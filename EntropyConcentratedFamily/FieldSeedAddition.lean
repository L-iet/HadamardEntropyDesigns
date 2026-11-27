/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.FieldCoordinates
public import EntropySupportDistance.SourceOffsets
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace

theorem binarySeed_seedXor {s : ℕ} (a b : Fin s → Bool) :
    binarySeed (seedXor a b)=binarySeed a+binarySeed b := by
  have h11 : (1:ZMod 2)+1=0 := by decide
  funext t
  cases ha : a t <;> cases hb : b t <;> simp [binarySeed,seedXor,ha,hb,h11]

theorem fieldSeedEquiv_xor {s : ℕ} (hs : s≠0) (a b : GaloisField 2 s) :
    seedXor (fieldSeedEquiv s hs a) (fieldSeedEquiv s hs b)=fieldSeedEquiv s hs (a+b) := by
  apply binarySeed_bijective.1
  simp only [binarySeed_seedXor,binarySeed_fieldSeedEquiv,map_add]

theorem fieldSeedEquiv_zero {s : ℕ} (hs : s≠0) :
    fieldSeedEquiv s hs (0:GaloisField 2 s)=fun _ => false := by
  apply binarySeed_bijective.1
  rw [binarySeed_fieldSeedEquiv,map_zero]
  funext t
  simp [binarySeed]

end
end EntropyDesigns.ConcentratedFamily
