module

public import EntropyDesigns.MinimalBinarySeed

/-! # Quantitative separation of the smallest binary seed from extraction -/

@[expose] public section
namespace EntropyDesigns

theorem binary_ceiling_range (m : ℕ) (hm : 1 < m) :
    m ≤ 2 ^ Nat.clog 2 m ∧ 2 ^ Nat.clog 2 m < 2 * m := by
  refine ⟨Nat.le_pow_clog (by decide) m, ?_⟩
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) hm
  have hpos := Nat.clog_pos (by decide : 1 < (2 : ℕ)) hm
  have hpower : 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m).pred := by
    calc
      _ = 2 ^ ((Nat.clog 2 m).pred + 1) :=
        congrArg (fun k : ℕ => 2 ^ k) (Nat.succ_pred_eq_of_pos hpos).symm
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  omega

theorem minimal_seed_order_bounds (N : ℕ) (hN : 12 ≤ N) (hdiv : 4 ∣ N)
    (hnotpower : ∀ a : ℕ, N ≠ 2 ^ a) :
    N + 4 ≤ 2 ^ Nat.clog 2 (N - 3) ∧ 2 ^ Nat.clog 2 (N - 3) < 2 * N := by
  let r := Nat.clog 2 (N - 3)
  let L := 2 ^ r
  have hr : 3 < r := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2 : ℕ))).mpr
    norm_num
    omega
  have hdivL : 4 ∣ L := by
    refine ⟨2 ^ (r - 2), ?_⟩
    change 2 ^ r = 4 * 2 ^ (r - 2)
    calc
      _ = 2 ^ (2 + (r - 2)) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num
  have hrange := binary_ceiling_range (N - 3) (by omega)
  have hlower : N - 3 ≤ L := hrange.1
  have hupper : L < 2 * (N - 3) := hrange.2
  have hLne : L ≠ N := fun h => hnotpower r h.symm
  have hlarge : N + 4 ≤ L := by
    obtain ⟨a, ha⟩ := hdiv
    obtain ⟨b, hb⟩ := hdivL
    omega
  have hstrict : 2 * (N - 3) < 2 * N := by omega
  exact ⟨hlarge, hupper.trans hstrict⟩

theorem reciprocal_minimal_seed_gap {N L : ℝ} (hN : 0 < N)
    (hlarge : N + 4 ≤ L) (hsmall : L < 2 * N) :
    2 / N ^ 2 < 1 / N - 1 / L := by
  have hL : 0 < L := by linarith
  have hgap : 4 ≤ L - N := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hgap hN.le
  have hineq : 2 * L < N * (L - N) := by nlinarith
  have hid : 1 / N - 1 / L = (L - N) / (N * L) := by field_simp
  rw [hid]
  apply (div_lt_div_iff₀ (pow_pos hN 2) (mul_pos hN hL)).mpr
  nlinarith [mul_lt_mul_of_pos_left hineq hN]

theorem minimal_binary_seed_gap {r : ℕ} (N : ℕ) (hN : 12 ≤ N) (hdiv : 4 ∣ N)
    (hnotpower : ∀ a : ℕ, N ≠ 2 ^ a)
    (B : Finset (Finset (Fin r))) (hB : ∅ ∉ B) (hcard : B.card = N - 4)
    (hminimum : r = Nat.clog 2 (B.card + 1))
    (hspan : Submodule.span (ZMod 2)
      (Set.range (fun S : B => binarySeed (maskSeed S.val))) = ⊤)
    (w : (Fin r → Bool) → ℝ) (hmass : ∑ x, w x = 1)
    (hmean : ∀ S ∈ B, walshCoefficient w S = 0)
    (hpair : ∀ S ∈ B, ∀ T ∈ B, S ≠ T →
      ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0) :
    2 / (N : ℝ) ^ 2 < 1 / (N : ℝ) - collision (pushLaw (characterCode B) w) ∧
      1 / (1024 * (N : ℝ) ^ 4) < 1 / (N : ℝ) - collision (pushLaw (characterCode B) w) := by
  have hr : r = Nat.clog 2 (N - 3) := by
    rw [hminimum, hcard]
    congr 1
    omega
  have hC := (minimum_binary_seed_observed_law B hB hminimum hspan w hmass hmean hpair).2.2.2.2.2
  have hbounds := minimal_seed_order_bounds N hN hdiv hnotpower
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlarge : (N : ℝ) + 4 ≤ (2 : ℝ) ^ r := by
    rw [hr]
    exact_mod_cast hbounds.1
  have hsmall : (2 : ℝ) ^ r < 2 * (N : ℝ) := by
    rw [hr]
    exact_mod_cast hbounds.2
  have hgap : 2 / (N : ℝ) ^ 2 < 1 / (N : ℝ) - collision (pushLaw (characterCode B) w) := by
    rw [hC]
    exact reciprocal_minimal_seed_gap hNpos hlarge hsmall
  refine ⟨hgap, ?_⟩
  have hN12 : (12 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hden : (N : ℝ) ^ 2 < 2 * (1024 * (N : ℝ) ^ 4) := by
    nlinarith [sq_nonneg ((N : ℝ) ^ 2 - 1)]
  have hwindow : 1 / (1024 * (N : ℝ) ^ 4) < 2 / (N : ℝ) ^ 2 := by
    apply (div_lt_div_iff₀ (by positivity) (pow_pos hNpos 2)).mpr
    simpa only [one_mul] using hden
  exact hwindow.trans hgap

end EntropyDesigns
