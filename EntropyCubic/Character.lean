/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators symmDiff

def booleanValueSign (a : ZMod 2) : ℤ := if a=0 then 1 else -1

def boolCoordinateSupport {r : ℕ} (x : Fin r → Bool) : Finset (Fin r) :=
  Finset.univ.filter (fun i => x i=true)

theorem booleanValueSign_add (a b : ZMod 2) :
    booleanValueSign (a+b)=booleanValueSign a*booleanValueSign b := by
  have h : ∀ a b : ZMod 2,booleanValueSign (a+b)=booleanValueSign a*booleanValueSign b := by decide
  exact h a b

theorem walshChar_mul_symmDiff {r : ℕ} (S T : Finset (Fin r)) (x : Fin r → Bool) :
    walshChar S x*walshChar T x=walshChar (S ∆ T) x := by
  classical
  have hprod (U : Finset (Fin r)) :
      (∏ i : Fin r,if i∈U then bitSign (x i) else 1)=walshChar U x := by
    simp [walshChar,Finset.prod_ite]
  rw [←hprod S,←hprod T,←hprod (S ∆ T),←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hs : i∈S <;> by_cases ht : i∈T <;>
    rcases bitSign_sign (x i) with hx|hx <;>
    simp [Finset.mem_symmDiff,hs,ht,hx]

theorem degree_one_boolean_sign_character {r : ℕ} (g : Finset (Fin r) → ZMod 2)
    (hg : g∈lowDegreeBooleanCode r 1) :
    ∃ ε : ℤ, ∃ S : Finset (Fin r), (ε=1 ∨ ε= -1) ∧
      ∀ x : Fin r → Bool, booleanValueSign (g (boolCoordinateSupport x))=ε*walshChar S x := by
  classical
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨s,rfl⟩ := hg
    by_cases hs : s.val=∅
    · refine ⟨-1,∅,Or.inr rfl,?_⟩
      intro x
      simp [hs,squarefreeBooleanMonomial,booleanValueSign,walshChar]
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have he : s.val={i} := by
        ext j
        simp only [Finset.mem_singleton]
        constructor
        · intro hj
          exact Finset.card_le_one.mp s.property j hj i hi
        · intro hj; subst j; exact hi
      refine ⟨1,{i},Or.inl rfl,?_⟩
      intro x
      cases hx : x i <;>
        simp [he,squarefreeBooleanMonomial,boolCoordinateSupport,hx,booleanValueSign,walshChar,bitSign]
  | zero =>
    refine ⟨1,∅,Or.inl rfl,?_⟩
    intro x
    simp [booleanValueSign,walshChar]
  | add f g hf hg ihf ihg =>
    obtain ⟨ε,S,hε,hf⟩ := ihf
    obtain ⟨δ,T,hδ,hg⟩ := ihg
    refine ⟨ε*δ,S ∆ T,?_,?_⟩
    · rcases hε with hε|hε <;> rcases hδ with hδ|hδ <;> simp [hε,hδ]
    · intro x
      change booleanValueSign (f (boolCoordinateSupport x)+g (boolCoordinateSupport x))=_
      rw [booleanValueSign_add,hf,hg,←walshChar_mul_symmDiff]
      ring
  | smul a f hf ih =>
    have htwo : ∀ a : ZMod 2,a=0 ∨ a=1 := by decide
    rcases htwo a with ha|ha
    · subst a
      refine ⟨1,∅,Or.inl rfl,?_⟩
      intro x
      simp [booleanValueSign,walshChar]
    · subst a
      simpa using ih

end
end EntropyDesigns
