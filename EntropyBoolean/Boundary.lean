/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean.Affine
@[expose] public section
namespace EntropyDesigns
noncomputable section

theorem lowDegreeBooleanCode_eq_top_of_ge {r d : ℕ} (hd : r≤d) :
    lowDegreeBooleanCode r d=⊤ := by
  classical
  have hspan : Submodule.span (ZMod 2) (Set.range
      (fun s : Finset (Fin r) => squarefreeBooleanMonomial s))=⊤ :=
    squarefreeBooleanMonomial_linearIndependent.span_eq_top_of_card_eq_finrank'
      (Module.finrank_fintype_fun_eq_card (ZMod 2)).symm
  have hle : Submodule.span (ZMod 2) (Set.range
      (fun s : Finset (Fin r) => squarefreeBooleanMonomial s))≤lowDegreeBooleanCode r d := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨s,?_⟩,rfl⟩
    calc
      s.card≤Fintype.card (Fin r) := Finset.card_le_univ s
      _=r := Fintype.card_fin r
      _≤d := hd
  rw [hspan] at hle
  exact top_unique hle

theorem booleanSupport_full_degree_extension {r d : ℕ} (hd : r≤d)
    (S : Finset (Finset (Fin r))) :
    ∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode r d, binaryFunctionRestriction S g=f := by
  intro f
  refine ⟨binaryFunctionZeroExtend S f,?_,?_⟩
  · rw [lowDegreeBooleanCode_eq_top_of_ge hd]
    trivial
  · funext z
    exact binaryFunctionZeroExtend_on S f z

/-- The negative-degree dual code is zero, including the full-degree boundary. -/
def booleanDegreeDualCode (r d : ℕ) : Submodule (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  if d<r then lowDegreeBooleanCode r (r-d-1) else ⊥

theorem booleanSupport_extension_criterion_all_degrees (r d : ℕ)
    (S : Finset (Finset (Fin r))) :
    (∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode r d, binaryFunctionRestriction S g=f) ↔
      (∀ g∈booleanDegreeDualCode r d, (∀ z,z∉S → g z=0) → g=0) := by
  by_cases hd : d<r
  · simpa only [booleanDegreeDualCode,if_pos hd] using lowDegreeBooleanCode_extension_criterion hd S
  · have hleft := booleanSupport_full_degree_extension (r:=r) (d:=d) (by omega) S
    have hright : ∀ g∈booleanDegreeDualCode r d, (∀ z,z∉S → g z=0) → g=0 := by
      intro g hg _
      simpa only [booleanDegreeDualCode,if_neg hd,Submodule.mem_bot] using hg
    exact iff_of_true hleft hright

end
end EntropyDesigns
