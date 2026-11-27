/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.BlockMarginals
public import EntropyDesigns.BinaryObservables
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators
abbrev NonzeroMask (s : ℕ) := {S : Finset (Fin s) // S≠∅}
abbrev MixedBlock (k : ℕ) (i0 : Fin k) := {j : Fin k // j≠i0}
abbrev SourceCoordinate (k s : ℕ) (i0 : Fin k) := (Fin k × NonzeroMask s) ⊕ MixedBlock k i0
abbrev SourceOutcome (k s : ℕ) (i0 : Fin k) := SourceCoordinate k s i0 → Bool

def sourceSign {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) :
    SourceCoordinate k s i0 → ℤ :=
  Sum.elim (fun a => walshChar a.2.val (x a.1))
    (fun j => walshChar e (x i0)*walshChar e (x j.val))
def sourceCode {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) : SourceOutcome k s i0 :=
  fun c => decide (sourceSign e i0 x c= -1)

theorem sourceSign_sign {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s)
    (c : SourceCoordinate k s i0) : sourceSign e i0 x c=1 ∨ sourceSign e i0 x c= -1 := by
  rcases c with ⟨i,S⟩|j
  · exact walshChar_sign S.val (x i)
  · rcases walshChar_sign e (x i0) with h|h <;> rcases walshChar_sign e (x j.val) with h'|h' <;>
      simp [sourceSign,h,h']

theorem sourceCode_sign {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s)
    (c : SourceCoordinate k s i0) : bitSign (sourceCode e i0 x c)=sourceSign e i0 x c := by
  rcases sourceSign_sign e i0 x c with h|h <;> norm_num [sourceCode,bitSign,h]

theorem sourceCode_singleton {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s)
    (i : Fin k) (t : Fin s) : sourceCode e i0 x (Sum.inl (i,⟨{t},by simp⟩))=x i t := by
  cases h : x i t <;> simp [sourceCode,sourceSign,walshChar,bitSign,h]

theorem sourceCode_injective {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) :
    Function.Injective (sourceCode e i0) := by
  intro x y h
  funext i t
  have ht := congrFun h (Sum.inl (i,⟨{t},by simp⟩))
  simpa only [sourceCode_singleton] using ht

def sourceFeasible {k s : ℕ} (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ) : Prop :=
  (∀ y,0≤q y) ∧ (∑ y,q y=1) ∧
  (∀ c,(∑ y,q y*(bitSign (y c):ℝ))=0) ∧
  (∀ c d,c≠d → (∑ y,q y*(bitSign (y c):ℝ)*(bitSign (y d):ℝ))=0)
def sourceSupported {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ) : Prop :=
  ∀ y,(¬∃ x,sourceCode e i0 x=y) → q y=0
def sourcePullback {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ) :
    BlockSeeds k s → ℝ := fun x => q (sourceCode e i0 x)

theorem source_push_pullback {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (q : SourceOutcome k s i0 → ℝ) (hsupport : sourceSupported e i0 q) :
    pushLaw (sourceCode e i0) (sourcePullback e i0 q)=q := by
  classical
  funext y
  by_cases hy : ∃ x,sourceCode e i0 x=y
  · obtain ⟨x,rfl⟩ := hy
    simpa only [sourcePullback] using pushLaw_injective_value (sourceCode e i0)
      (sourceCode_injective e i0) (sourcePullback e i0 q) x
  · rw [hsupport y hy]
    unfold pushLaw
    apply Finset.sum_eq_zero
    intro x _
    have hxy : sourceCode e i0 x≠y := fun h => hy ⟨x,h⟩
    simp [hxy]

theorem source_pullback_moments {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) (hsupport : sourceSupported e i0 q) :
    (∀ x,0≤sourcePullback e i0 q x) ∧ (∑ x,sourcePullback e i0 q x=1) ∧
      blockCharacterMoments (sourcePullback e i0 q) := by
  classical
  let f : BlockSeeds k s → SourceOutcome k s i0 := sourceCode e i0
  let w : BlockSeeds k s → ℝ := sourcePullback e i0 q
  have hpush : pushLaw f w=q := source_push_pullback e i0 q hsupport
  refine ⟨fun x => hq.1 (sourceCode e i0 x),?_,?_,?_⟩
  · rw [← pushLaw_mass f w,hpush]
    exact hq.2.1
  · intro i S hS
    let c : SourceCoordinate k s i0 := Sum.inl (i,⟨S,hS⟩)
    have hp := pushLaw_moment (α:=BlockSeeds k s) (β:=SourceOutcome k s i0) f w
      (fun y => (bitSign (y c):ℝ))
    rw [hpush] at hp
    have h := hp.symm.trans (hq.2.2.1 c)
    simpa [f,w,c,sourceCode_sign,sourceSign] using h
  · intro i j hij S T hS hT
    let c : SourceCoordinate k s i0 := Sum.inl (i,⟨S,hS⟩)
    let d : SourceCoordinate k s i0 := Sum.inl (j,⟨T,hT⟩)
    have hcd : c≠d := by
      intro h
      have hp : ((i,⟨S,hS⟩) : Fin k × NonzeroMask s)=(j,⟨T,hT⟩) := Sum.inl.inj h
      exact hij (congrArg Prod.fst hp)
    have hp := pushLaw_moment (α:=BlockSeeds k s) (β:=SourceOutcome k s i0) f w
      (fun y => (bitSign (y c):ℝ)*(bitSign (y d):ℝ))
    rw [hpush] at hp
    have h : (∑ x,w x*((bitSign (f x c):ℝ)*(bitSign (f x d):ℝ)))=0 :=
      hp.symm.trans (by simpa only [mul_assoc] using hq.2.2.2 c d hcd)
    simpa [f,w,c,d,sourceCode_sign,sourceSign,mul_assoc] using h
end
end EntropyDesigns.SupportFace
