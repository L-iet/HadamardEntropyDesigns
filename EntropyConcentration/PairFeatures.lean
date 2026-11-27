/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.SourceCode
public import EntropySupportFace.PairWalsh
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.Concentration
noncomputable section
open SupportFace
open scoped BigOperators

def blockFeature {k s : ℕ} {i0 : Fin k} (i : Fin k) (S : Finset (Fin s))
    (y : SourceOutcome k s i0) : ℝ :=
  if h : S=∅ then 1 else (bitSign (y (Sum.inl (i,⟨S,h⟩))):ℝ)

theorem blockFeature_sign {k s : ℕ} {i0 : Fin k} (i : Fin k) (S : Finset (Fin s))
    (y : SourceOutcome k s i0) : blockFeature i S y=1 ∨ blockFeature i S y= -1 := by
  classical
  by_cases hS : S=∅
  · simp [blockFeature,hS]
  · unfold blockFeature
    rw [dif_neg hS]
    cases y (Sum.inl (i,⟨S,hS⟩)) <;> norm_num [bitSign]

theorem blockFeature_source {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (i : Fin k) (S : Finset (Fin s)) (x : BlockSeeds k s) :
    blockFeature i S (sourceCode e i0 x)=(walshChar S (x i):ℝ) := by
  classical
  by_cases hS : S=∅
  · subst S;simp [blockFeature,walshChar]
  · unfold blockFeature
    rw [dif_neg hS,sourceCode_sign]
    rfl

theorem blockFeature_pair_moment {k s : ℕ} (i0 : Fin k) (i j : Fin k) (hij : i≠j)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) (S T : Finset (Fin s)) :
    (∑ y,q y*blockFeature i S y*blockFeature j T y)=
      if S=∅ ∧ T=∅ then 1 else 0 := by
  classical
  by_cases hS : S=∅
  · by_cases hT : T=∅
    · simpa [blockFeature,hS,hT] using hq.2.1
    · simpa [blockFeature,hS,hT] using
        hq.2.2.1 (Sum.inl (j,⟨T,hT⟩))
  · by_cases hT : T=∅
    · simpa [blockFeature,hS,hT] using
        hq.2.2.1 (Sum.inl (i,⟨S,hS⟩))
    · let c : SourceCoordinate k s i0 := Sum.inl (i,⟨S,hS⟩)
      let d : SourceCoordinate k s i0 := Sum.inl (j,⟨T,hT⟩)
      have hcd : c≠d := by
        intro heq
        exact hij (congrArg (fun z : Fin k × NonzeroMask s => z.1) (Sum.inl.inj heq))
      simpa [blockFeature,hS,hT,c,d] using hq.2.2.2 c d hcd

end
end EntropyDesigns.Concentration
