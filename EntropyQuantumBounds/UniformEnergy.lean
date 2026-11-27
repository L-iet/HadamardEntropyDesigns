/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantumBounds.EuclideanEffects
public import EntropyQuantumBounds.WeightCaps
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem uniform_inner_energy (M N : ℝ) (hM : 0<M) (v : α → ι → ℝ)
    (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (1/M) (v a)=(1 : Matrix ι ι ℝ)) (a : α) :
    (∑ b,(inner (v a) (v b))^2)=N*M := by
  have h := tight_inner_energy (fun _ : α => 1/M) v htight (v a)
  rw [hnorm a] at h
  have hd : (∑ b,(inner (v a) (v b))^2)/M=N := by
    simpa only [← Finset.mul_sum,div_eq_mul_inv,mul_comm,one_div,mul_one,one_mul] using h
  exact (div_eq_iff (ne_of_gt hM)).mp hd

theorem uniform_offdiag_inner_energy (M N : ℝ) (hM : 0<M) (v : α → ι → ℝ)
    (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (1/M) (v a)=(1 : Matrix ι ι ℝ)) (a : α) :
    (∑ b∈Finset.univ.erase a,(inner (v a) (v b))^2)=N*(M-N) := by
  have hs := Finset.sum_erase_add Finset.univ (fun b => (inner (v a) (v b))^2) (Finset.mem_univ a)
  rw [uniform_inner_energy M N hM v hnorm htight a,hnorm a] at hs
  nlinarith

theorem uniform_pair_inner_budget (M N : ℝ) (hM : 0<M) (v : α → ι → ℝ)
    (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (1/M) (v a)=(1 : Matrix ι ι ℝ)) (a b : α) (hab : a≠b) :
    (inner (v a) (v b))^2≤N*(M-N) := by
  have hs := Finset.single_le_sum (s:=Finset.univ.erase a)
    (fun c _ => sq_nonneg (inner (v a) (v c))) (Finset.mem_erase.mpr ⟨hab.symm,Finset.mem_univ b⟩)
  rw [uniform_offdiag_inner_energy M N hM v hnorm htight a] at hs
  exact hs

theorem uniform_row_commutator_budget (M N : ℝ) (hM : 0<M) (v : α → ι → ℝ)
    (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (1/M) (v a)=(1 : Matrix ι ι ℝ)) (a : α) :
    (∑ b,(inner (v a) (v b))^2*(N^2-(inner (v a) (v b))^2))≤N^3*(M-N) := by
  let f (b : α) := (inner (v a) (v b))^2*(N^2-(inner (v a) (v b))^2)
  have hself : f a=0 := by simp [f,hnorm a]
  have hs := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  rw [hself,add_zero] at hs
  change (∑ b,f b)≤_
  rw [← hs]
  calc
    _≤∑ b∈Finset.univ.erase a,N^2*(inner (v a) (v b))^2 := by
      apply Finset.sum_le_sum
      intro b _
      dsimp [f]
      nlinarith [sq_nonneg ((inner (v a) (v b))^2)]
    _=N^2*(N*(M-N)) := by
      rw [← Finset.mul_sum,uniform_offdiag_inner_energy M N hM v hnorm htight a]
    _=N^3*(M-N) := by ring

theorem uniform_normalized_energy_bound (M N : ℝ) (hM : 0<M) (hN : 0<N)
    (hcard : (Fintype.card α:ℝ)=M) (v : α → ι → ℝ)
    (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (1/M) (v a)=(1 : Matrix ι ι ℝ)) :
    commutatorEnergy (fun _ : α => 1/M) v/N≤2*(N/M)^2*(1-N/M) := by
  have hsum : (∑ a,∑ b,(inner (v a) (v b))^2*(N^2-(inner (v a) (v b))^2))≤M*(N^3*(M-N)) := by
    have h := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) => uniform_row_commutator_budget M N hM v hnorm htight a)
    simpa [hcard] using h
  have hfactor : commutatorEnergy (fun _ : α => 1/M) v=
      (2/M^4)*(∑ a,∑ b,(inner (v a) (v b))^2*(N^2-(inner (v a) (v b))^2)) := by
    rw [exact_commutator_energy (fun _ : α => 1/M) v N hnorm]
    simp only [Finset.mul_sum,div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  apply (div_le_iff₀ hN).mpr
  rw [hfactor]
  calc
    _≤(2/M^4)*(M*(N^3*(M-N))) := mul_le_mul_of_nonneg_left hsum (div_nonneg (by norm_num) (pow_nonneg hM.le _))
    _=(2*(N/M)^2*(1-N/M))*N := by field_simp [ne_of_gt hM] <;> ring
end
end EntropyDesigns.Quantum
