/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
The original quadratic-observable problem is equivalent to an exact support-code frame problem. -/
module
public import EntropyQuadraticClassification.SupportObservables
public import EntropyQuadraticClassification.QuadraticCheckTypes
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped BigOperators

def HasQuadraticObservableFrame (S : Finset (Finset (Fin 4))) (m : ℕ) : Prop :=
  ∃ rows : S → Fin m → Bool,IsUniformBinaryPairwiseIndependent rows ∧
    ∃ F : Fin m → (Finset (Fin 4) → ZMod 2),
      (∀ i,F i∈lowDegreeBooleanCode 4 2) ∧
      ∀ i (z : S),F i z.val=if rows z i then 1 else 0

theorem indicatorF2_oneSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ZMod 2) : indicatorF2 (oneSupport f)=f := by
  apply oneSupport_injective
  exact indicatorF2_support _

theorem quadratic_frame_of_supports (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    {m : ℕ} (supports : Fin m → Finset S)
    (hmem : ∀ i,indicatorF2 (supports i)∈
      (lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))
    (hcard : ∀ i,(supports i).card=6)
    (hinter : ∀ i j,i≠j → (supports i ∩ supports j).card=3) :
    HasQuadraticObservableFrame S m := by
  classical
  have hex : ∀ i,∃ F∈lowDegreeBooleanCode 4 2,
      binaryFunctionRestriction S F=indicatorF2 (supports i) :=
    fun i => Submodule.mem_map.mp (hmem i)
  choose F hF he using hex
  let rows : S → Fin m → Bool := fun z i => decide (z∈supports i)
  have hsize : Fintype.card S=12 := by simp [hS]
  refine ⟨rows,support_frame_uniform hsize supports hcard hinter,F,hF,?_⟩
  intro i z
  have hz := congrFun (he i) z
  change F i z.val=indicatorF2 (supports i) z at hz
  rw [hz]
  by_cases hm : z∈supports i <;> simp [indicatorF2,rows,hm]

theorem supports_of_quadratic_frame (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    {m : ℕ} (hframe : HasQuadraticObservableFrame S m) :
    ∃ supports : Fin m → Finset S,
      (∀ i,indicatorF2 (supports i)∈
        (lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)) ∧
      (∀ i,(supports i).card=6) ∧
      ∀ i j,i≠j → (supports i ∩ supports j).card=3 := by
  classical
  obtain ⟨rows,hrows,F,hF,hm⟩ := hframe
  let f : Fin m → (S → ZMod 2) := fun i => binaryFunctionRestriction S (F i)
  let supports : Fin m → Finset S := fun i => oneSupport (f i)
  have hsign : ∀ i z,gf2Sign (f i z)=bitSign (rows z i) := by
    intro i z
    change gf2Sign (F i z.val)=bitSign (rows z i)
    rw [hm]
    cases rows z i <;> rfl
  have hmean : ∀ i,(∑ z,gf2Sign (f i z))=0 := by
    intro i
    simp_rw [hsign]
    exact hrows.1 i
  have hpair : ∀ i j,i≠j → (∑ z,gf2Sign (f i z)*gf2Sign (f j z))=0 := by
    intro i j hij
    simp_rw [hsign]
    exact hrows.2 i j hij
  have hsize : Fintype.card S=12 := by simp [hS]
  refine ⟨supports,?_,?_,?_⟩
  · intro i
    change indicatorF2 (oneSupport (f i))∈_
    rw [indicatorF2_oneSupport]
    exact Submodule.mem_map.mpr ⟨F i,hF i,rfl⟩
  · intro i
    exact twelve_balanced_support_card hsize (f i) (hmean i)
  · intro i j hij
    exact twelve_orthogonal_intersection hsize (f i) (f j) (hmean i) (hmean j) (hpair i j hij)

end EntropyDesigns.QuadraticRefinement
