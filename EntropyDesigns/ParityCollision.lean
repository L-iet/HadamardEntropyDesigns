/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.SharpEntropyTheorem
public import EntropyDesigns.WalshBlocks
@[expose] public section
namespace EntropyDesigns

theorem residue_two_cube_collision_sharp {d : ℕ} (hd : 5≤d) (hres : (d+1)%4=2)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ b,0≤w b) (hmass : ∑ b,w b=1)
    (hmean : ∀ i,∑ b,w b*(bitSign (b i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ b,w b*(bitSign (b i) : ℝ)*(bitSign (b j) : ℝ)=0) :
    collision w≤1/((d : ℝ)+3) ∧
      ((∃ H : Matrix (Fin (d+3)) (Fin (d+3)) ℝ,Matrix.IsHadamard H) →
        ∃ v : (Fin d → Bool) → ℝ,
          (∀ b,0≤v b) ∧ (∑ b,v b=1) ∧
          (∀ i,∑ b,v b*(bitSign (b i) : ℝ)=0) ∧
          (∀ i j,i≠j → ∑ b,v b*(bitSign (b i) : ℝ)*(bitSign (b j) : ℝ)=0) ∧
          collision v=1/((d : ℝ)+3)) := by
  have hr : roundedDimension (d+1)=d+3 := by unfold roundedDimension; omega
  constructor
  · simpa only [hr,Nat.cast_add,Nat.cast_ofNat] using
      (sharp_sign_cube_entropy_bounds (by omega) w hw hmass hmean hpair).1
  · intro hH
    have hH' : ∃ H : Matrix (Fin (roundedDimension (d+1))) (Fin (roundedDimension (d+1))) ℝ,Matrix.IsHadamard H := by
      rw [hr]
      exact hH
    obtain ⟨H,hH⟩ := hH'
    obtain ⟨v,hv,hm,hmean',hpair',hc,_,_⟩ := cube_law_of_hadamard (by omega) H hH
    exact ⟨v,hv,hm,hmean',hpair',by simpa only [hr,Nat.cast_add,Nat.cast_ofNat] using hc⟩

theorem five_bit_collision_eighth_attained :
    ∃ w : (Fin 5 → Bool) → ℝ,
      (∀ b,0≤w b) ∧ (∑ b,w b=1) ∧
      (∀ i,∑ b,w b*(bitSign (b i) : ℝ)=0) ∧
      (∀ i j,i≠j → ∑ b,w b*(bitSign (b i) : ℝ)*(bitSign (b j) : ℝ)=0) ∧
      collision w=1/8 := by
  let e : Finset (Fin 3) ≃ Fin 8 := (Fintype.equivFin _).trans (finCongr (by decide))
  have hH := (walshSquare_hadamard 3).reindex e e
  have hr : roundedDimension (5+1)=8 := by decide
  have hH' : ∃ H : Matrix (Fin (roundedDimension (5+1))) (Fin (roundedDimension (5+1))) ℝ,Matrix.IsHadamard H := by
    simpa only [hr] using ⟨_,hH⟩
  obtain ⟨H,hH⟩ := hH'
  obtain ⟨w,hw,hm,hmean,hpair,hc,_,_⟩ := cube_law_of_hadamard (d := 5) (by decide) H hH
  exact ⟨w,hw,hm,hmean,hpair,by norm_num [roundedDimension] at hc ⊢; exact hc⟩
end EntropyDesigns
