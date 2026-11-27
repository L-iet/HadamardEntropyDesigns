/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Pull finite sign supports back through a coordinate equivalence. -/
module
public import EntropyQuadraticClassification.FiberTransport
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

theorem support_map_symm {A B : Type*} (e : A ≃ B) (s : Finset B) :
    (s.map e.symm.toEmbedding).map e.toEmbedding=s := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hx
    simpa only [Equiv.toEmbedding_apply,e.apply_symm_apply] using hz
  · intro hy
    apply Finset.mem_map.mpr
    refine ⟨e.symm y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,?_⟩
    exact e.apply_symm_apply y

theorem support_dot_pullback {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (s : Finset A) (t : Finset B) :
    dotParity s (t.map e.symm.toEmbedding)=dotParity (s.map e.toEmbedding) t := by
  have h := support_map_dot e s (t.map e.symm.toEmbedding)
  rw [support_map_symm] at h
  exact h.symm

end EntropyDesigns.QuadraticRefinement
