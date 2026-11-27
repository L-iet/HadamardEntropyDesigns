/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySeedRepair.BasisSubset
@[expose] public section
namespace EntropyDesigns.SupportRepair
noncomputable section

theorem booleanSupportVector_injective (r : ℕ) : Function.Injective (@booleanSupportVector r) := by
  intro A B h
  apply Finset.ext
  intro i
  have hi := congrFun h i
  by_cases ha : i∈A <;> by_cases hb : i∈B <;> simp [booleanSupportVector,ha,hb] at hi ⊢

def booleanLabelsEquiv (r : ℕ) : Finset (Fin r) ≃ (Fin r → ZMod 2) :=
  Equiv.ofBijective booleanSupportVector ⟨booleanSupportVector_injective r,booleanSupportVector_surjective r⟩

theorem booleanLabelsEquiv_apply (r : ℕ) (z : Finset (Fin r)) :
    booleanLabelsEquiv r z=booleanSupportVector z := rfl

theorem boolean_label_image_as_vectors {r : ℕ} (T : Finset (Finset (Fin r))) :
    ((T.map (booleanLabelsEquiv r).toEmbedding) : Set (Fin r → ZMod 2))=
      booleanSupportVector '' (T : Set (Finset (Fin r))) := by
  ext v
  constructor
  · intro hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hv
    exact ⟨z,hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact Finset.mem_map.mpr ⟨z,hz,rfl⟩

end
end EntropyDesigns.SupportRepair
