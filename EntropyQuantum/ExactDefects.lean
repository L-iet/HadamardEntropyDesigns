/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantum.FrameRigidity
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [Fintype α]

def projectivityDefect (w : α → ℝ) (v : α → ι → ℝ) : ℝ :=
  ∑ a,Matrix.trace (effect (w a) (v a)-effect (w a) (v a)*effect (w a) (v a))
def commutatorEnergy (w : α → ℝ) (v : α → ι → ℝ) : ℝ :=
  ∑ a,∑ b,frobeniusSq (commutator (effect (w a) (v a)) (effect (w b) (v b)))

theorem exact_projectivity_defect (w : α → ℝ) (v : α → ι → ℝ)
    (N : ℝ) (hmass : ∑ a,w a=1) (hnorm : ∀ a,inner (v a) (v a)=N) :
    projectivityDefect w v=N-N^2*(∑ a,(w a)^2) := by
  simp only [projectivityDefect,Matrix.trace_sub,effect_trace,effect_square_trace,hnorm,
    Finset.sum_sub_distrib,← Finset.sum_mul]
  rw [hmass]
  ring

theorem exact_commutator_energy (w : α → ℝ) (v : α → ι → ℝ)
    (N : ℝ) (hnorm : ∀ a,inner (v a) (v a)=N) :
    commutatorEnergy w v=2*∑ a,∑ b,(w a)^2*(w b)^2*(inner (v a) (v b))^2*
      (N^2-(inner (v a) (v b))^2) := by
  simp only [commutatorEnergy,commutator_frobenius,hnorm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frobeniusSq_nonneg (A : Matrix ι ι ℝ) : 0≤frobeniusSq A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem frobeniusSq_zero_iff (A : Matrix ι ι ℝ) : frobeniusSq A=0 ↔ A=0 := by
  constructor
  · intro h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))).mp h
    ext i j
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A i j))).mp
      (hi i (Finset.mem_univ i)) j (Finset.mem_univ j)
    have hz : A i j=0 := by nlinarith [sq_nonneg (A i j)]
    exact hz
  · rintro rfl
    simp [frobeniusSq]

theorem zero_energy_iff_commuting (w : α → ℝ) (v : α → ι → ℝ) :
    commutatorEnergy w v=0 ↔
      ∀ a b,effect (w a) (v a)*effect (w b) (v b)=effect (w b) (v b)*effect (w a) (v a) := by
  constructor
  · intro h a b
    have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => frobeniusSq_nonneg _))).mp h a (Finset.mem_univ a)
    have hab := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => frobeniusSq_nonneg _)).mp ha b (Finset.mem_univ b)
    exact sub_eq_zero.mp ((frobeniusSq_zero_iff _).mp hab)
  · intro h
    have hz (a b : α) : commutator (effect (w a) (v a)) (effect (w b) (v b))=0 := sub_eq_zero.mpr (h a b)
    simp [commutatorEnergy,hz,frobeniusSq]
theorem effect_product_trace (a b : ℝ) (v w : ι → ℝ) :
    Matrix.trace (effect a v*effect b w)=a*b*(inner v w)^2 := by
  classical
  rw [effect,Matrix.smul_mul,Matrix.trace_smul,outer_effect_trace]
  simp only [smul_eq_mul]
  ring

theorem squared_effect_product_trace (a b N : ℝ) (v w : ι → ℝ)
    (hv : inner v v=N) (hw : inner w w=N) :
    Matrix.trace ((effect a v*effect a v)*(effect b w*effect b w))=
      N^2*a^2*b^2*(inner v w)^2 := by
  rw [effect_square,effect_square,hv,hw]
  change Matrix.trace (effect (a^2*N) v*effect (b^2*N) w)=_
  rw [effect_product_trace]
  ring

theorem trace_squared_sum (w : α → ℝ) (v : α → ι → ℝ) (N : ℝ)
    (hnorm : ∀ a,inner (v a) (v a)=N) :
    Matrix.trace ((∑ a,effect (w a) (v a)*effect (w a) (v a))*
      (∑ a,effect (w a) (v a)*effect (w a) (v a)))=
      ∑ a,∑ b,N^2*(w a)^2*(w b)^2*(inner (v a) (v b))^2 := by
  simp only [Finset.sum_mul,Finset.mul_sum,Matrix.trace_sum,
    squared_effect_product_trace _ _ N _ _ (hnorm _) (hnorm _)]
  rw [Finset.sum_comm]

theorem commutator_trace_energy (w : α → ℝ) (v : α → ι → ℝ) (N : ℝ)
    (hnorm : ∀ a,inner (v a) (v a)=N) :
    commutatorEnergy w v=2*(
      Matrix.trace ((∑ a,effect (w a) (v a)*effect (w a) (v a))*
        (∑ a,effect (w a) (v a)*effect (w a) (v a)))-
      ∑ a,∑ b,(Matrix.trace (effect (w a) (v a)*effect (w b) (v b)))^2) := by
  rw [exact_commutator_energy w v N hnorm,trace_squared_sum w v N hnorm]
  simp only [effect_product_trace,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring
end
end EntropyDesigns.Quantum
