/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentration.PairKernel
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.Concentration
noncomputable section
open SupportFace
open scoped BigOperators

theorem pairKernel_moment {k s : ℕ} (i0 : Fin k) (i j : Fin k) (hij : i≠j)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) (v : PairSeed s) :
    (∑ y,q y*pairKernel i j v y)=1/((2:ℝ)^s)^2 := by
  classical
  let c : ℝ := 1/((2:ℝ)^s)^2
  have hm (P : PairMask s) : (∑ y,q y*pairFeature i j P y)=
      if P=(∅,∅) then 1 else 0 := by
    simpa only [pairFeature,mul_assoc,Prod.ext_iff] using blockFeature_pair_moment i0 i j hij q hq P.1 P.2
  have hterm (y : SourceOutcome k s i0) :
      q y*pairKernel i j v y=c*(∑ P : PairMask s,pairChar P v*(q y*pairFeature i j P y)) := by
    calc
      _=c*(q y*(∑ P : PairMask s,pairChar P v*pairFeature i j P y)) := by
        dsimp only [pairKernel,c]
        ring
      _=c*(∑ P : PairMask s,q y*(pairChar P v*pairFeature i j P y)) := by rw [Finset.mul_sum]
      _=_ := by
        congr 1
        apply Finset.sum_congr rfl
        intro P _
        ring
  calc
    _=∑ y,c*(∑ P : PairMask s,pairChar P v*(q y*pairFeature i j P y)) :=
      Finset.sum_congr rfl (fun y _ => hterm y)
    _=c*(∑ y,∑ P : PairMask s,pairChar P v*(q y*pairFeature i j P y)) :=
      (Finset.mul_sum _ _ _).symm
    _=c*(∑ P : PairMask s,∑ y,pairChar P v*(q y*pairFeature i j P y)) := by rw [Finset.sum_comm]
    _=c*(∑ P : PairMask s,pairChar P v*(∑ y,q y*pairFeature i j P y)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro P _
      exact (Finset.mul_sum _ _ _).symm
    _=c := by simp [hm,mul_ite,pairChar,walshChar]
    _=_ := rfl

end
end EntropyDesigns.Concentration
