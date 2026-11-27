/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Star
public import Mathlib.Tactic.FieldSimp
public import EntropyQuantum.FrameRigidity
public import EntropyQuantum.ExactDefects
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

def UniformHadamardMeasurement (w : α → ℝ) (v : α → ι → ℝ) : Prop :=
  ∃ e : α ≃ ι,Matrix.IsHadamard (fun i j => v (e.symm i) j) ∧
    ∀ a,w a=1/(Fintype.card ι:ℝ)

theorem sign_norm (v : ι → ℝ) (hsign : ∀ i,v i=1 ∨ v i= -1) :
    inner v v=(Fintype.card ι:ℝ) := by
  have hs (i : ι) : v i*v i=1 := by rcases hsign i with h|h <;> rw [h] <;> ring
  simp [inner,hs]

theorem tight_mass (o : ι) (w : α → ℝ) (v : α → ι → ℝ)
    (hv : ∀ a,v a o=1) (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) :
    ∑ a,w a=1 := by
  have h := congrArg (fun M : Matrix ι ι ℝ => M o o) htight
  simpa [Matrix.sum_apply,effect,outer,hv] using h

theorem projective_uniform_hadamard (o : ι) (w : α → ℝ) (v : α → ι → ℝ)
    (hw : ∀ a,0<w a) (hv : ∀ a,v a o=1) (hsign : ∀ a i,v a i=1 ∨ v a i= -1)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ))
    (hp : ∀ a,effect (w a) (v a)*effect (w a) (v a)=effect (w a) (v a)) :
    UniformHadamardMeasurement w v := by
  have hcard : 0<Fintype.card ι := Fintype.card_pos_iff.mpr ⟨o⟩
  have hN : (0:ℝ)<Fintype.card ι := by exact_mod_cast hcard
  have hnorm := fun a => sign_norm (v a) (hsign a)
  have hweight (a : α) : w a=1/(Fintype.card ι:ℝ) := by
    apply (eq_div_iff (ne_of_gt hN)).mpr
    exact normalized_projective_weight o (w a) _ (hw a) (v a) (hv a) (hnorm a) (hp a)
  have hmass := tight_mass o w v hv htight
  have hcardR : (Fintype.card α:ℝ)=(Fintype.card ι:ℝ) := by
    simp_rw [hweight] at hmass
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hmass
    field_simp [ne_of_gt hN] at hmass
    nlinarith
  have hcards : Fintype.card α=Fintype.card ι := by exact_mod_cast hcardR
  let e : α ≃ ι := Fintype.equivOfCardEq hcards
  have horth := projective_tight_orthogonal o _ hN w v hw hv hnorm htight hp
  refine ⟨e,?_,hweight⟩
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hsign (e.symm i) j)
  · ext i j
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    change inner (v (e.symm i)) (v (e.symm j))=_
    by_cases hij : i=j
    · subst j;simpa using hnorm (e.symm i)
    · have he : e.symm i≠e.symm j := fun h => hij (e.symm.injective h)
      simpa [hij] using horth _ _ he
  · exact isRegular_iff_ne_zero.mpr (ne_of_gt hN)

theorem hadamard_measurement_orthogonal (w : α → ℝ) (v : α → ι → ℝ)
    (h : UniformHadamardMeasurement w v) : ∀ a b,a≠b → inner (v a) (v b)=0 := by
  obtain ⟨e,hH,_⟩ := h
  intro a b hab
  have hrow := congrArg (fun M : Matrix ι ι ℝ => M (e a) (e b)) hH.mul_conjTranspose
  have he : e a≠e b := fun h => hab (e.injective h)
  simp only [Matrix.smul_apply,Matrix.one_apply,he,ite_false,smul_eq_mul,mul_zero] at hrow
  change (∑ k,v (e.symm (e a)) k * star (v (e.symm (e b)) k))=0 at hrow
  simpa only [Equiv.symm_apply_apply,star_trivial,inner] using hrow

theorem exact_projective_commuting_criteria (o : ι) (w : α → ℝ) (v : α → ι → ℝ)
    (hw : ∀ a,0<w a) (hv : ∀ a,v a o=1) (hsign : ∀ a i,v a i=1 ∨ v a i= -1)
    (hinj : Function.Injective v)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) :
    (UniformHadamardMeasurement w v ↔ ∀ a,effect (w a) (v a)*effect (w a) (v a)=effect (w a) (v a)) ∧
    (UniformHadamardMeasurement w v ↔ ∀ a b,effect (w a) (v a)*effect (w b) (v b)=effect (w b) (v b)*effect (w a) (v a)) ∧
    (UniformHadamardMeasurement w v ↔ commutatorEnergy w v=0) := by
  have hp : UniformHadamardMeasurement w v ↔ ∀ a,effect (w a) (v a)*effect (w a) (v a)=effect (w a) (v a) :=
    ⟨fun h => orthogonal_tight_projective w v htight (hadamard_measurement_orthogonal w v h),
      projective_uniform_hadamard o w v hw hv hsign htight⟩
  have hc : UniformHadamardMeasurement w v ↔ ∀ a b,effect (w a) (v a)*effect (w b) (v b)=effect (w b) (v b)*effect (w a) (v a) := by
    constructor
    · intro h a b
      by_cases hab : a=b
      · subst b;rfl
      · exact orthogonal_effects_commute _ _ _ _ (hadamard_measurement_orthogonal w v h a b hab)
    · intro h
      apply hp.mpr
      apply orthogonal_tight_projective w v htight
      intro a b hab
      exact commuting_distinct_normalized o _ _ (ne_of_gt (hw a)) (ne_of_gt (hw b)) _ _
        (hv a) (hv b) (fun he => hab (hinj he)) (h a b)
  exact ⟨hp,hc,hc.trans (zero_energy_iff_commuting w v).symm⟩
end
end EntropyDesigns.Quantum
