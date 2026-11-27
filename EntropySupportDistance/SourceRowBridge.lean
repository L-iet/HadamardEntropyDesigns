/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SignedCharacters
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def fullColumnEquiv {k s : ℕ} (i0 : Fin k) :
    (Fin k × Finset (Fin s)) ≃ Option (SourceCoordinate k s i0) where
  toFun z := if hS : z.2=∅ then
    if hj : z.1=i0 then none else some (Sum.inr ⟨z.1,hj⟩)
    else some (Sum.inl (z.1,⟨z.2,hS⟩))
  invFun z := match z with
    | none => (i0,∅)
    | some (Sum.inl (j,S)) => (j,S.val)
    | some (Sum.inr j) => (j.val,∅)
  left_inv z := by
    rcases z with ⟨j,S⟩
    by_cases hS : S=∅
    · subst S
      by_cases hj : j=i0 <;> simp [hj]
    · simp [hS]
  right_inv z := by
    rcases z with _|z
    · simp
    · rcases z with ⟨j,S⟩|j
      · simp [S.property]
      · simp [j.property]

theorem fullSourceRow_column_bridge {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (x : BlockSeeds k s) (z : Option (SourceCoordinate k s i0)) :
    fullSourceRow e i0 x ((fullColumnEquiv i0).symm z)=
      Option.elim z 1 (fun c => bitSign (sourceCode e i0 x c)) := by
  classical
  rcases z with _|z
  · change walshChar e (x i0)*walshChar e (x i0)=1
    simpa only [pow_two] using walshChar_sq e (x i0)
  · rw [Option.elim_some,sourceCode_sign]
    rcases z with ⟨j,S⟩|j
    · simp [fullColumnEquiv,fullSourceRow,sourceSign,S.property]
    · simp [fullColumnEquiv,fullSourceRow,sourceSign]

theorem fullSourceInner_observed {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (x y : BlockSeeds k s) :
    fullSourceInner e i0 x y=1+
      ∑ c : SourceCoordinate k s i0,bitSign (sourceCode e i0 x c)*bitSign (sourceCode e i0 y c) := by
  classical
  have he := Equiv.sum_comp (fullColumnEquiv i0).symm
    (fun z : Fin k × Finset (Fin s) => fullSourceRow e i0 x z*fullSourceRow e i0 y z)
  rw [Fintype.sum_prod_type] at he
  change (∑ z : Option (SourceCoordinate k s i0),
    fullSourceRow e i0 x ((fullColumnEquiv i0).symm z)*
      fullSourceRow e i0 y ((fullColumnEquiv i0).symm z))=fullSourceInner e i0 x y at he
  rw [←he]
  simp only [fullSourceRow_column_bridge,Fintype.sum_option,Option.elim_none,
    Option.elim_some,one_mul]

end
end EntropyDesigns.SupportFace
