/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Coordinate equivalences respecting finite partitions preserve support parity. -/
module
public import EntropyQuadraticClassification.Transvections
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

theorem exists_fiber_respecting_equiv {A B J : Type*}
    [Fintype A] [Fintype B] [DecidableEq J]
    (c : A → J) (d : B → J)
    (hcard : ∀ j,Fintype.card {a // c a=j}=Fintype.card {b // d b=j}) :
    ∃ e : A ≃ B,∀ a,d (e a)=c a := by
  classical
  let fibers : ∀ j,{a // c a=j} ≃ {b // d b=j} :=
    fun j => Fintype.equivOfCardEq (hcard j)
  exact ⟨Equiv.ofFiberEquiv fibers,Equiv.ofFiberEquiv_map fibers⟩

theorem support_map_card {A B : Type*} (e : A ≃ B) (s : Finset A) :
    (s.map e.toEmbedding).card=s.card := Finset.card_map _

theorem support_map_dot {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (s t : Finset A) :
    dotParity (s.map e.toEmbedding) (t.map e.toEmbedding)=dotParity s t := by
  unfold dotParity
  rw [←Finset.map_inter,Finset.card_map]

theorem support_map_fiber {A B J : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq J]
    (e : A ≃ B) (c : A → J) (d : B → J) (he : ∀ a,d (e a)=c a) (j : J) :
    (Finset.univ.filter (fun a => c a=j)).map e.toEmbedding=
      Finset.univ.filter (fun b => d b=j) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,hxy⟩ := Finset.mem_map.mp hy
    change e x=y at hxy
    subst y
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,he x] using hx
  · intro hy
    apply Finset.mem_map.mpr
    refine ⟨e.symm y,?_,by simp⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hy ⊢
    rw [←he (e.symm y),e.apply_symm_apply]
    exact hy

end EntropyDesigns.QuadraticRefinement
