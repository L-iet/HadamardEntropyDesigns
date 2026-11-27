/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportFace.FieldCoordinates
@[expose] public section
namespace EntropyDesigns.SupportFace
noncomputable section

theorem maskFunctional_injective (s : ℕ) : Function.Injective (@maskFunctional s) := by
  classical
  intro S T h
  apply Finset.ext
  intro j
  have hv := LinearMap.congr_fun h (fun i => if i=j then 1 else 0)
  have he : (if j∈S then (1:ZMod 2) else 0)=(if j∈T then (1:ZMod 2) else 0) := by
    simpa [maskFunctional] using hv
  by_cases hS : j∈S <;> by_cases hT : j∈T <;> simp_all

theorem maskFieldFunctional_injective {s : ℕ} (hs : s≠0) :
    Function.Injective (maskFieldFunctional hs) := by
  intro S T h
  apply maskFunctional_injective s
  apply LinearMap.ext
  intro z
  obtain ⟨a,ha⟩ := (fieldCoordinates s hs).surjective z
  have hv := LinearMap.congr_fun h a
  change maskFunctional S (fieldCoordinates s hs a)=maskFunctional T (fieldCoordinates s hs a) at hv
  rw [ha] at hv
  exact hv
end
end EntropyDesigns.SupportFace
