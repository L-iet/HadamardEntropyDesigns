/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySparseBuffer.SparseBufferBase
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns
theorem sparse_uniform_feasible_collision_gap {d : ℕ} (hd : 16≤d)
    (G : Finset (Fin d → Bool)) (hcard : G.card=d+4) (heven : Even (d+4))
    (hnonzero : ∃ i : LowIndex d,fourierCoefficient (uniformOn G (d+4)) lowCharacter i≠0)
    (B : ℝ) (hB : 0≤B)
    (hfeasible : ∀ x,0≤affineCorrection (uniformOn G (d+4))
      (lowPolynomial (uniformOn G (d+4))) ((2:ℝ)^d) B x) :
    1/(8*((d:ℝ)+4)^2*Real.sqrt (Fintype.card (LowIndex d)))≤
      1/((d:ℝ)+4)-collision (affineCorrection (uniformOn G (d+4))
        (lowPolynomial (uniformOn G (d+4))) ((2:ℝ)^d) B) ∧
    1/(8*((d:ℝ)+4)^3)<1/(8*((d:ℝ)+4)^2*Real.sqrt (Fintype.card (LowIndex d))) ∧
    1/(1024*((d:ℝ)+4)^4)<1/(8*((d:ℝ)+4)^3) := by
  classical
  let w := uniformOn G (d+4)
  let N : ℝ := (d:ℝ)+4
  let K : ℝ := Fintype.card (LowIndex d)
  let S := ∑ i : LowIndex d,fourierCoefficient w lowCharacter i^2
  let q := affineCorrection w (lowPolynomial w) ((2:ℝ)^d) B
  let b := 1/(2*N*Real.sqrt K)
  have hdR : (16:ℝ)≤d := by exact_mod_cast hd
  have hN : 0<N := by dsimp [N]; linarith
  have hN20 : 20≤N := by dsimp [N]; linarith
  have hcount : 2*K=(d:ℝ)*((d:ℝ)+1) := by
    dsimp only [K]
    exact_mod_cast lowIndex_card_twice d
  have hK : 1≤K := by nlinarith
  have hr : 1≤Real.sqrt K := Real.one_le_sqrt.mpr hK
  have hroot : 0<Real.sqrt K := by linarith
  have hb : 0<b := by dsimp [b]; positivity
  have hb1 : b≤1 := by
    dsimp only [b]
    apply (div_le_iff₀ (by positivity : 0<2*N*Real.sqrt K)).mpr
    nlinarith
  have hbB : b≤B := minimal_feasible_uniform_buffer_lower hd G hcard heven hnonzero B hB hfeasible
  have hM : 2*N≤(2:ℝ)^d := by
    have hh := cube_card_ge_twice_target (by omega : 4≤d)
    dsimp only [N]
    exact_mod_cast hh
  have hS : 0≤S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hmass := uniformOn_mass G (d+4) (by omega) hcard
  have hQ : collision q=1/((2:ℝ)^d)+(1/N-(1+S)/((2:ℝ)^d))/(1+B)^2 := by
    have hh := affineCorrection_collision_identity w (lowPolynomial w)
      (M := (2:ℝ)^d) (B := B) (S := S) (by positivity) hB (by simp) hmass
      (lowPolynomial_sum_zero w) (fourierPolynomial_weighted w lowCharacter)
      (fourierPolynomial_square _ _ _ lowCharacter_orthogonality)
    have hwc : collision w=1/N := by
      have hc := uniformOn_collision G (d+4) (by omega) hcard
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hc
    rw [hwc] at hh
    exact hh
  have hgap := feasible_buffer_collision_gap hN hM hb hb1 hbB hS hQ
  have hid : b/(4*N)=1/(8*N^2*Real.sqrt K) := by dsimp only [b]; field_simp; ring
  rw [hid] at hgap
  have hrootN : Real.sqrt K<N := by
    have hs := Real.sq_sqrt (by linarith : 0≤K)
    dsimp only [N]
    nlinarith
  have hden : 8*N^2*Real.sqrt K<8*N^3 := by
    have hh := mul_pos (by positivity : 0<8*N^2) (sub_pos.mpr hrootN)
    nlinarith
  have hgap2 := one_div_lt_one_div_of_lt (by positivity : 0<8*N^2*Real.sqrt K) hden
  have hden3 : 8*N^3<1024*N^4 := by
    have hh := mul_pos (show 0<128*N-1 by linarith) (pow_pos hN 3)
    nlinarith
  have hgap3 := one_div_lt_one_div_of_lt (by positivity : 0<8*N^3) hden3
  exact ⟨hgap,hgap2,hgap3⟩

end EntropyDesigns
