/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantum.FrameRigidity
public import EntropyQuantum.ExactDefects
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem tight_weight_cap (w : α → ℝ) (v : α → ι → ℝ) (N : ℝ) (hN : 0<N)
    (hw : ∀ a,0≤w a) (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) (a : α) : w a*N≤1 := by
  have he := tight_inner_energy w v htight (v a)
  have hs := Finset.single_le_sum (fun b (_ : b∈Finset.univ) =>
    mul_nonneg (hw b) (sq_nonneg (inner (v a) (v b)))) (Finset.mem_univ a)
  rw [he,hnorm a] at hs
  apply (mul_le_mul_iff_left₀ hN).mp
  nlinarith

theorem normalized_collision_cap (w : α → ℝ) (v : α → ι → ℝ) (N : ℝ) (hN : 0<N)
    (hw : ∀ a,0≤w a) (hmass : ∑ a,w a=1) (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) :
    N*(∑ a,(w a)^2)≤1 := by
  calc
    N*(∑ a,(w a)^2)=∑ a,w a*(w a*N) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _≤∑ a,w a := Finset.sum_le_sum (fun a _ => by
      simpa using mul_le_mul_of_nonneg_left (tight_weight_cap w v N hN hw hnorm htight a) (hw a))
    _=1 := hmass

theorem maximal_collision_projective (w : α → ℝ) (v : α → ι → ℝ) (N : ℝ) (hN : 0<N)
    (hw : ∀ a,0<w a) (hmass : ∑ a,w a=1) (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ))
    (hmax : N*(∑ a,(w a)^2)=1) :
    ∀ a,effect (w a) (v a)*effect (w a) (v a)=effect (w a) (v a) := by
  have hdef : projectivityDefect w v=0 := by
    rw [exact_projectivity_defect w v N hmass hnorm]
    calc N-N^2*(∑ a,(w a)^2)=N*(1-N*(∑ a,(w a)^2)) := by ring
         _=0 := by rw [hmax,sub_self,mul_zero]
  have hterm (a : α) : Matrix.trace (effect (w a) (v a)-effect (w a) (v a)*effect (w a) (v a))=
      (w a*N)*(1-w a*N) := by
    rw [Matrix.trace_sub,effect_trace,effect_square_trace,hnorm a]
    ring
  have hnonneg (a : α) : 0≤(w a*N)*(1-w a*N) :=
    mul_nonneg (mul_nonneg (hw a).le hN.le)
      (sub_nonneg.mpr (tight_weight_cap w v N hN (fun a => (hw a).le) hnorm htight a))
  simp only [projectivityDefect,hterm] at hdef
  intro a
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg b)).mp hdef a (Finset.mem_univ a)
  have hprod : w a*N≠0 := ne_of_gt (mul_pos (hw a) hN)
  have hone := (mul_eq_zero.mp hz).resolve_left hprod
  apply projective_of_weight (w a) N (v a) (hnorm a)
  linarith
end
end EntropyDesigns.Quantum
