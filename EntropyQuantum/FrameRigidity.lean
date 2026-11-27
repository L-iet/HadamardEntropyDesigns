/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantum.CommutingCriteria
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem outer_effect_trace (v w : ι → ℝ) (a : ℝ) :
    Matrix.trace (outer v v*effect a w)=a*(inner v w)^2 := by
  rw [effect,Matrix.mul_smul,outer_mul,Matrix.trace_smul,Matrix.trace_smul,trace_outer]
  simp only [smul_eq_mul]
  ring

theorem tight_inner_energy (w : α → ℝ) (v : α → ι → ℝ)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) (u : ι → ℝ) :
    (∑ a,w a*(inner u (v a))^2)=inner u u := by
  have h := congrArg (fun M : Matrix ι ι ℝ => Matrix.trace (outer u u*M)) htight
  simpa only [Finset.mul_sum,Matrix.trace_sum,outer_effect_trace,Matrix.mul_one,trace_outer] using h

theorem normalized_projective_weight (o : ι) (a N : ℝ) (ha : 0<a)
    (v : ι → ℝ) (hv : v o=1) (hnorm : inner v v=N)
    (hp : effect a v*effect a v=effect a v) : a*N=1 := by
  rw [effect_square,hnorm] at hp
  have hh := congrArg (fun M : Matrix ι ι ℝ => M o o) hp
  have hscalar : a^2*N=a := by simpa [effect,outer,Matrix.smul_apply,hv] using hh
  have hf : a*(a*N-1)=0 := by nlinarith
  have hz := (mul_eq_zero.mp hf).resolve_left (ne_of_gt ha)
  linarith

theorem projective_of_weight (a N : ℝ) (v : ι → ℝ)
    (hnorm : inner v v=N) (hweight : a*N=1) : effect a v*effect a v=effect a v := by
  rw [effect_square,hnorm]
  have hh : a^2*N=a := by
    calc a^2*N=a*(a*N) := by ring
         _=a := by rw [hweight,mul_one]
  rw [hh]
  rfl

theorem projective_tight_orthogonal (o : ι) (N : ℝ) (hN : 0<N)
    (w : α → ℝ) (v : α → ι → ℝ) (hw : ∀ a,0<w a)
    (hv : ∀ a,v a o=1) (hnorm : ∀ a,inner (v a) (v a)=N)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ))
    (hp : ∀ a,effect (w a) (v a)*effect (w a) (v a)=effect (w a) (v a)) :
    ∀ a b,a≠b → inner (v a) (v b)=0 := by
  intro a b hab
  have hweight := normalized_projective_weight o (w a) N (hw a) (v a) (hv a) (hnorm a) (hp a)
  have henergy := tight_inner_energy w v htight (v a)
  have hself : w a*(inner (v a) (v a))^2=N := by
    rw [hnorm a]
    calc w a*N^2=(w a*N)*N := by ring
         _=N := by rw [hweight,one_mul]
  have hrest : ∑ c∈Finset.univ.erase a,w c*(inner (v a) (v c))^2=0 := by
    have hs := Finset.sum_erase_add (s:=Finset.univ) (f:=fun c => w c*(inner (v a) (v c))^2) (Finset.mem_univ a)
    rw [henergy,hself,hnorm a] at hs
    linarith
  have hz : w b*(inner (v a) (v b))^2=0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_nonneg (hw c).le (sq_nonneg _))).mp hrest
    exact Finset.mem_erase.mpr ⟨hab.symm,Finset.mem_univ b⟩
  have hs := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw b))
  nlinarith [sq_nonneg (inner (v a) (v b))]

theorem orthogonal_tight_projective (w : α → ℝ) (v : α → ι → ℝ)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ))
    (horth : ∀ a b,a≠b → inner (v a) (v b)=0) :
    ∀ a,effect (w a) (v a)*effect (w a) (v a)=effect (w a) (v a) := by
  intro a
  have hprod (b : α) (hba : b≠a) : effect (w b) (v b)*effect (w a) (v a)=0 := by
    simp [effect,Matrix.smul_mul,Matrix.mul_smul,outer_mul,horth b a hba]
  calc
    effect (w a) (v a)*effect (w a) (v a)=∑ b,effect (w b) (v b)*effect (w a) (v a) := by
      symm
      apply Finset.sum_eq_single a
      · intro b _ hba;exact hprod b hba
      · simp
    _=(∑ b,effect (w b) (v b))*effect (w a) (v a) := (Finset.sum_mul _ _ _).symm
    _=effect (w a) (v a) := by rw [htight,Matrix.one_mul]
end
end EntropyDesigns.Quantum
