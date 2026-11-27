/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.SharpEntropyTheorem
@[expose] public section
namespace EntropyDesigns

theorem parity_collision_equality_two_column_iff {d : ℕ} (hd : 5≤d) (hres : (d+1)%4=2)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ b,0≤w b) (hmass : ∑ b,w b=1)
    (hmean : ∀ i,∑ b,w b*(bitSign (b i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ b,w b*(bitSign (b i) : ℝ)*(bitSign (b j) : ℝ)=0) :
    collision w=1/((d+3 : ℕ) : ℝ) ↔
      (∀ b,w b=0 ∨ w b=1/((d+3 : ℕ) : ℝ)) ∧
      (Finset.univ.filter (fun b => w b ≠ 0)).card=d+3 ∧
      ∃ (H : Matrix (Fin (d+3)) (Fin (d+3)) ℝ)
        (columns : Fin (d+1) ↪ Fin (d+3))
        (rows : {b // w b ≠ 0} ≃ Fin (d+3)),
        Matrix.IsHadamard H ∧ ∀ b i,H (rows b) (columns i)=
          (augmentedSign (fun (b : Fin d → Bool) i => bitSign (b i)) (b : Fin d → Bool) i : ℝ) := by
  classical
  have hr : roundedDimension (d+1)=d+3 := by unfold roundedDimension; omega
  constructor
  · intro heq
    have heq' : collision w=1/(roundedDimension (d+1) : ℝ) := by rw [hr]; exact heq
    have hh := sharp_sign_cube_equality_completion (by omega) w hw hmass hmean hpair heq'
    rw [hr] at hh
    exact hh
  · rintro ⟨huniform,_,_⟩
    have hpoint (b : Fin d → Bool) : w b^2=(1/((d+3 : ℕ) : ℝ))*w b := by
      rcases huniform b with h|h <;> rw [h] <;> ring
    unfold collision
    simp_rw [hpoint]
    rw [← Finset.mul_sum,hmass,mul_one]

theorem parity_collision_attainment_iff_hadamard {d : ℕ} (hd : 5≤d) (hres : (d+1)%4=2) :
    (∃ w : (Fin d → Bool) → ℝ,
      (∀ b,0≤w b) ∧ (∑ b,w b=1) ∧
      (∀ i,∑ b,w b*(bitSign (b i) : ℝ)=0) ∧
      (∀ i j,i≠j → ∑ b,w b*(bitSign (b i) : ℝ)*(bitSign (b j) : ℝ)=0) ∧
      collision w=1/((d+3 : ℕ) : ℝ)) ↔
        ∃ H : Matrix (Fin (d+3)) (Fin (d+3)) ℝ,Matrix.IsHadamard H := by
  have hr : roundedDimension (d+1)=d+3 := by unfold roundedDimension; omega
  have hh := collision_attainment_iff_hadamard (d := d) (by omega)
  rw [hr] at hh
  exact hh
end EntropyDesigns
