/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantumBounds.MatrixNormBounds
public import EntropyQuantumBounds.UniformEnergy
public import EntropyQuantum.UniformCriteria
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem uniform_tight_povm_operator_bounds (o : ι) (v : α → ι → ℝ)
    (hv : ∀ a,v a o=1) (hsign : ∀ a i,v a i=1 ∨ v a i= -1)
    (htight : ∑ a,effect (1/(Fintype.card α:ℝ)) (v a)=(1 : Matrix ι ι ℝ)) :
    let N := (Fintype.card ι:ℝ)
    let M := (Fintype.card α:ℝ)
    (∀ a,euclideanOperatorNorm (effect (1/M) (v a)-effect (1/M) (v a)*effect (1/M) (v a))=
      (N/M)*(1-N/M)) ∧
    (IsGreatest (Set.range (fun a => euclideanOperatorNorm
      (effect (1/M) (v a)-effect (1/M) (v a)*effect (1/M) (v a)))) ((N/M)*(1-N/M))) ∧
    (∀ a b,(euclideanOperatorNorm (commutator (effect (1/M) (v a)) (effect (1/M) (v b))))^2≤
      (N/M)^3*(1-N/M)) ∧
    (commutatorEnergy (fun _ : α => 1/M) v/N≤2*(N/M)^2*(1-N/M)) := by
  classical
  dsimp only
  let N : ℝ := Fintype.card ι
  let M : ℝ := Fintype.card α
  have hmass := tight_mass o (fun _ : α => 1/M) v hv htight
  have hα : Nonempty α := by
    by_contra h
    letI : IsEmpty α := not_nonempty_iff.mp h
    simp at hmass
  have hM : 0<M := by dsimp [M]; exact_mod_cast (Fintype.card_pos_iff.mpr hα)
  have hN : 0<N := by dsimp [N]; exact_mod_cast (Fintype.card_pos_iff.mpr ⟨o⟩)
  have hnorm (a : α) : inner (v a) (v a)=N := sign_norm (v a) (hsign a)
  have hscalar : (1/M)*N=N/M := by simp only [div_eq_mul_inv];ring
  have hcap : N/M≤1 := by
    have h := tight_weight_cap (fun _ : α => 1/M) v N hN (fun _ => (one_div_pos.mpr hM).le)
      hnorm htight (Classical.choice hα)
    simpa only [hscalar] using h
  have hlam : 0≤N/M := (div_pos hN hM).le
  have hDefect (a : α) : euclideanOperatorNorm
      (effect (1/M) (v a)-effect (1/M) (v a)*effect (1/M) (v a))=(N/M)*(1-N/M) := by
    have h := effect_matrix_defect_norm (1/M) N hN (by simpa only [hscalar] using hlam)
      (by simpa only [hscalar] using hcap) (v a) (hnorm a)
    simpa only [hscalar] using h
  have hGreat : IsGreatest (Set.range (fun a => euclideanOperatorNorm
      (effect (1/M) (v a)-effect (1/M) (v a)*effect (1/M) (v a)))) ((N/M)*(1-N/M)) := by
    refine ⟨⟨Classical.choice hα,hDefect _⟩,?_⟩
    intro z hz
    obtain ⟨a,rfl⟩ := hz
    exact (hDefect a).le
  refine ⟨hDefect,hGreat,?_,uniform_normalized_energy_bound M N hM hN rfl v hnorm htight⟩
  · intro a b
    by_cases hab : a=b
    · subst b
      have hz : commutator (effect (1/M) (v a)) (effect (1/M) (v a))=0 := by simp [commutator]
      rw [hz]
      simp only [euclideanOperatorNorm,map_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0)]
      exact mul_nonneg (pow_nonneg hlam _) (sub_nonneg.mpr hcap)
    · let s := inner (v a) (v b)
      have hbudget : s^2≤N*(M-N) := uniform_pair_inner_budget M N hM v hnorm htight a b hab
      have hbound : euclideanOperatorNorm (commutator (effect (1/M) (v a)) (effect (1/M) (v b)))≤
          (N/M)^2*|s/N| := by
        simpa only [hscalar] using effect_matrix_commutator_bound (1/M) N hN (v a) (v b) (hnorm a) (hnorm b)
      have hnonneg : 0≤euclideanOperatorNorm (commutator (effect (1/M) (v a)) (effect (1/M) (v b))) := norm_nonneg _
      have hsquare := (sq_le_sq₀ hnonneg (mul_nonneg (sq_nonneg (N/M)) (abs_nonneg (s/N)))).mpr hbound
      calc
        _≤((N/M)^2*|s/N|)^2 := hsquare
        _=(N^2/M^4)*s^2 := by
          rw [mul_pow,sq_abs,div_pow]
          field_simp [ne_of_gt hN,ne_of_gt hM] <;> ring
        _≤(N^2/M^4)*(N*(M-N)) := mul_le_mul_of_nonneg_left hbudget (div_nonneg (sq_nonneg N) (pow_nonneg hM.le _))
        _=(N/M)^3*(1-N/M) := by field_simp [ne_of_gt hM] <;> ring
end
end EntropyDesigns.Quantum
