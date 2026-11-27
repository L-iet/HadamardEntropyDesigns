/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Tactic.FieldSimp
public import EntropyQuantumBounds.WeightCaps
public import EntropyQuantumBounds.TensorTightness
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem tensor_normalized_projectivity_defect (w : α → ℝ) (v : α → ι → ℝ)
    (N : ℝ) (hN : 0<N) (hmass : ∑ a,w a=1)
    (hnorm : ∀ a,inner (v a) (v a)=N) (r : ℕ) :
    projectivityDefect (tensorWeight w r) (tensorVector v r)/(N^r)=
      1-(N*(∑ a,(w a)^2))^r := by
  have hmassT : ∑ a,tensorWeight w r a=1 := by rw [tensor_weight_mass,hmass,one_pow]
  rw [exact_projectivity_defect _ _ (N^r) hmassT (tensor_vector_norm v r N hnorm),tensor_weight_collision]
  rw [mul_pow]
  have hn : N^r≠0 := pow_ne_zero r (ne_of_gt hN)
  field_simp [hn] <;> ring

theorem projective_collision_one (w : α → ℝ) (v : α → ι → ℝ)
    (N : ℝ) (hN : 0<N) (hmass : ∑ a,w a=1)
    (hnorm : ∀ a,inner (v a) (v a)=N)
    (hp : ∀ a,effect (w a) (v a)*effect (w a) (v a)=effect (w a) (v a)) :
    N*(∑ a,(w a)^2)=1 := by
  have hz : projectivityDefect w v=0 := by simp [projectivityDefect,hp]
  rw [exact_projectivity_defect w v N hmass hnorm] at hz
  have hf : N*(1-N*(∑ a,(w a)^2))=0 := by nlinarith
  have h := (mul_eq_zero.mp hf).resolve_left (ne_of_gt hN)
  linarith

theorem tensor_projectivity_no_activation (w : α → ℝ) (v : α → ι → ℝ)
    (N : ℝ) (hN : 0<N) (hw : ∀ a,0<w a) (hmass : ∑ a,w a=1)
    (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) (r : ℕ) (hr : r≠0) :
    (∀ a,effect (tensorWeight w r a) (tensorVector v r a)*effect (tensorWeight w r a) (tensorVector v r a)=
      effect (tensorWeight w r a) (tensorVector v r a)) ↔
    (∀ a,effect (w a) (v a)*effect (w a) (v a)=effect (w a) (v a)) := by
  have hmassT : ∑ a,tensorWeight w r a=1 := by rw [tensor_weight_mass,hmass,one_pow]
  have hnormT := tensor_vector_norm v r N hnorm
  have hcollision := tensor_weight_collision w r
  have hpositive : 0≤N*(∑ a,(w a)^2) := mul_nonneg hN.le (Finset.sum_nonneg (fun a _ => sq_nonneg (w a)))
  constructor
  · intro hp
    have hpower := projective_collision_one _ _ (N^r) (pow_pos hN r) hmassT hnormT hp
    rw [hcollision,← mul_pow] at hpower
    have hmax := (pow_eq_one_iff_of_nonneg hpositive hr).mp hpower
    exact maximal_collision_projective w v N hN hw hmass hnorm htight hmax
  · intro hp
    have hmax := projective_collision_one w v N hN hmass hnorm hp
    have hmaxT : N^r*(∑ a,(tensorWeight w r a)^2)=1 := by
      rw [hcollision,← mul_pow,hmax,one_pow]
    exact maximal_collision_projective _ _ (N^r) (pow_pos hN r)
      (tensor_weight_positive w r hw) hmassT hnormT (tensor_tight w v r htight) hmaxT
end
end EntropyDesigns.Quantum
