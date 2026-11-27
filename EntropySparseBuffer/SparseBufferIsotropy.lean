/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySparseBuffer.SparseBufferBase
public import EntropyDesigns.SharpEntropyTheorem
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns
theorem zero_low_coefficients_iff {d : ℕ} (w : (Fin d → Bool) → ℝ) :
    (∀ i : LowIndex d,fourierCoefficient w lowCharacter i=0) ↔
      (∀ i : Fin d,∑ x,w x*(bitSign (x i):ℝ)=0) ∧
      (∀ i j : Fin d,i≠j → ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)=0) := by
  constructor
  · intro h
    constructor
    · intro i
      let k : LowIndex d := ⟨{i},by simp⟩
      simpa [fourierCoefficient,lowCharacter,k,walshChar] using h k
    · intro i j hij
      let k : LowIndex d := ⟨{i,j},by simp [hij]⟩
      simpa [fourierCoefficient,lowCharacter,k,walshChar,hij,mul_assoc] using h k
  · rintro ⟨hm,hp⟩ i
    have hcard : i.val.card=1 ∨ i.val.card=2 := by
      have hpos := Finset.card_pos.mpr i.property.1
      have hle := i.property.2
      omega
    rcases hcard with hcard|hcard
    · obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hcard
      simpa [fourierCoefficient,lowCharacter,hj,walshChar] using hm j
    · obtain ⟨j,k,hjk,hjk'⟩ := Finset.card_eq_two.mp hcard
      simpa [fourierCoefficient,lowCharacter,hjk',walshChar,hjk,mul_assoc] using hp j k hjk

theorem zero_low_uniform_hadamard {d : ℕ} (hd : 16≤d) (hres : (d+4)%4=0)
    (G : Finset (Fin d → Bool)) (hcard : G.card=d+4)
    (hzero : ∀ i : LowIndex d,fourierCoefficient (uniformOn G (d+4)) lowCharacter i=0) :
    ∃ H : Matrix (Fin (d+4)) (Fin (d+4)) ℝ,Matrix.IsHadamard H := by
  have hr : roundedDimension (d+1)=d+4 := by unfold roundedDimension; omega
  have hw := uniformOn_nonneg G (d+4)
  have hm := uniformOn_mass G (d+4) (by omega) hcard
  obtain ⟨hmean,hpair⟩ := (zero_low_coefficients_iff _).mp hzero
  have hc := uniformOn_collision G (d+4) (by omega) hcard
  have hceq : collision (uniformOn G (d+4))=1/(roundedDimension (d+1):ℝ) := by
    rw [hr]
    exact hc
  obtain ⟨_,_,H,columns,rows,hH,_⟩ := sharp_sign_cube_equality_completion
    (by omega) (uniformOn G (d+4)) hw hm hmean hpair hceq
  have hex : ∃ H : Matrix (Fin (roundedDimension (d+1))) (Fin (roundedDimension (d+1))) ℝ,
      Matrix.IsHadamard H := ⟨H,hH⟩
  rwa [hr] at hex

end EntropyDesigns
