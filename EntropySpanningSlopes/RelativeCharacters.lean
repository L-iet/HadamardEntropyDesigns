/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.FieldObservables
public import EntropySupportDistance.SourceGram
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace

theorem binarySign_neg (z : ZMod 2) : binarySign (-z)=binarySign z := by
  have hzero : binarySign (0:ZMod 2)=1 := by norm_num [binarySign]
  simpa only [zero_sub,hzero,one_mul] using binarySign_sub 0 z

theorem field_mixed_relative_character {k s : ℕ} (hs : s≠0)
    (e : Finset (Fin s)) (i0 j : Fin k) (t : Fin k → GaloisField 2 s)
    (p q : GaloisField 2 s × GaloisField 2 s) :
    ((relativeChar e (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q) i0*
      relativeChar e (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q) j:ℤ):ℝ)=
      binarySign (maskFieldFunctional hs e ((t j-t i0)*(p.2-q.2))) := by
  let f := maskFieldFunctional hs e
  have hsign (i : Fin k) (v : GaloisField 2 s × GaloisField 2 s) :
      ((walshChar e (fieldSlopeSeeds hs t v i):ℤ):ℝ)=
        binarySign (f (v.1+t i*v.2)) := by
    exact field_seed_walsh_character hs e (v.1+t i*v.2)
  have hprod (i : Fin k) :
      ((relativeChar e (fieldSlopeSeeds hs t p) (fieldSlopeSeeds hs t q) i:ℤ):ℝ)=
        binarySign (f ((p.1+t i*p.2)-(q.1+t i*q.2))) := by
    simp only [relativeChar,Int.cast_mul]
    rw [hsign,hsign,←binarySign_sub,←map_sub]
  rw [Int.cast_mul,hprod,hprod,←binarySign_sub,←map_sub]
  have halg : ((p.1+t i0*p.2)-(q.1+t i0*q.2))-
      ((p.1+t j*p.2)-(q.1+t j*q.2))= -((t j-t i0)*(p.2-q.2)) := by ring
  rw [halg,map_neg,binarySign_neg]

end
end EntropyDesigns.SpanningSlopes
