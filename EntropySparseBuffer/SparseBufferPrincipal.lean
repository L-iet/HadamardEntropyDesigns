/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySparseBuffer.SparseBufferIsotropy
public import EntropySparseBuffer.SparseBufferCollision
@[expose] public section
namespace EntropyDesigns

theorem sparse_uniform_affine_buffer_obstruction {d : ℕ} (hd : 16≤d)
    (hres : (d+4)%4=0) (G : Finset (Fin d → Bool)) (hcard : G.card=d+4) :
    let w := uniformOn G (d+4)
    let K : ℝ := (d:ℝ)*((d:ℝ)+1)/2
    ((∀ i : LowIndex d,fourierCoefficient w lowCharacter i=0) ↔
      (∀ i : Fin d,∑ x,w x*(bitSign (x i):ℝ)=0) ∧
      (∀ i j : Fin d,i≠j → ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)=0)) ∧
    ((∀ i : LowIndex d,fourierCoefficient w lowCharacter i=0) →
      ∃ H : Matrix (Fin (d+4)) (Fin (d+4)) ℝ,Matrix.IsHadamard H) ∧
    ((∃ i : LowIndex d,fourierCoefficient w lowCharacter i≠0) →
      ∀ B : ℝ,0≤B →
        (∀ x,0≤affineCorrection w (lowPolynomial w) ((2:ℝ)^d) B x) →
        1/(2*((d:ℝ)+4)*Real.sqrt K)≤B ∧
        1/(8*((d:ℝ)+4)^2*Real.sqrt K)≤
          1/((d:ℝ)+4)-collision (affineCorrection w (lowPolynomial w) ((2:ℝ)^d) B) ∧
        1/(8*((d:ℝ)+4)^3)<1/(8*((d:ℝ)+4)^2*Real.sqrt K) ∧
        1/(1024*((d:ℝ)+4)^4)<1/(8*((d:ℝ)+4)^3)) := by
  dsimp only
  refine ⟨zero_low_coefficients_iff _,zero_low_uniform_hadamard hd hres G hcard,?_⟩
  intro hnonzero B hB hfeasible
  have heven : Even (d+4) := ⟨(d+4)/2,by omega⟩
  have hmin := minimal_feasible_uniform_buffer_lower hd G hcard heven hnonzero B hB hfeasible
  have hgap := sparse_uniform_feasible_collision_gap hd G hcard heven hnonzero B hB hfeasible
  have hcount : 2*(Fintype.card (LowIndex d):ℝ)=(d:ℝ)*((d:ℝ)+1) := by
    exact_mod_cast lowIndex_card_twice d
  have hK : (Fintype.card (LowIndex d):ℝ)=(d:ℝ)*((d:ℝ)+1)/2 := by linarith
  rw [hK] at hmin hgap
  exact ⟨hmin,hgap⟩

end EntropyDesigns
