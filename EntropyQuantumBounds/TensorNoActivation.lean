/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantumBounds.TensorDefect
public import EntropyQuantum.UniformCriteria
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem actual_tensor_povm_no_activation (o : ι) (w : α → ℝ) (v : α → ι → ℝ)
    (hw : ∀ a,0<w a) (hv : ∀ a,v a o=1) (hsign : ∀ a i,v a i=1 ∨ v a i= -1)
    (hinj : Function.Injective v)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) (r : ℕ) (hr : r≠0) :
    (∑ a,effect (tensorWeight w r a) (tensorVector v r a)=
      (1 : Matrix (Fin r → ι) (Fin r → ι) ℝ)) ∧
    (projectivityDefect (tensorWeight w r) (tensorVector v r)/(Fintype.card ι:ℝ)^r=
      1-((Fintype.card ι:ℝ)*(∑ a,(w a)^2))^r) ∧
    ((∀ a,effect (tensorWeight w r a) (tensorVector v r a)*effect (tensorWeight w r a) (tensorVector v r a)=
      effect (tensorWeight w r a) (tensorVector v r a)) ↔ UniformHadamardMeasurement w v) ∧
    ((∀ a b,effect (tensorWeight w r a) (tensorVector v r a)*effect (tensorWeight w r b) (tensorVector v r b)=
      effect (tensorWeight w r b) (tensorVector v r b)*effect (tensorWeight w r a) (tensorVector v r a)) ↔
      UniformHadamardMeasurement w v) := by
  have hN : (0:ℝ)<Fintype.card ι := by exact_mod_cast (Fintype.card_pos_iff.mpr ⟨o⟩)
  have hmass := tight_mass o w v hv htight
  have hnorm := fun a => sign_norm (v a) (hsign a)
  have hTightT := tensor_tight w v r htight
  have hBase := exact_projective_commuting_criteria o w v hw hv hsign hinj htight
  have hTensor := exact_projective_commuting_criteria (fun _ : Fin r => o)
    (tensorWeight w r) (tensorVector v r) (tensor_weight_positive w r hw)
    (tensor_normalized o v r hv) (tensor_sign v r hsign)
    (tensor_vector_injective o v r hv hinj) hTightT
  have hNoAct := tensor_projectivity_no_activation w v (Fintype.card ι:ℝ) hN hw hmass hnorm htight r hr
  have hProj := hNoAct.trans hBase.1.symm
  exact ⟨hTightT,tensor_normalized_projectivity_defect w v _ hN hmass hnorm r,
    hProj,hTensor.2.1.symm.trans (hTensor.1.trans hProj)⟩
end
end EntropyDesigns.Quantum
