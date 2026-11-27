module

public import EntropyDesigns.BinaryObservables
public import Mathlib.Data.Nat.Log

/-! # The smallest possible binary seed forces a uniform power-of-two law -/

@[expose] public section
namespace EntropyDesigns

theorem minimum_binary_seed_cover {r : ℕ} (B : Finset (Finset (Fin r))) (hB : ∅ ∉ B)
    (hminimum : r = Nat.clog 2 (B.card + 1)) : maskSumset (insert ∅ B) = Finset.univ := by
  apply more_than_half_mask_cover
  rw [Finset.card_insert_of_notMem hB]
  by_cases hzero : B.card = 0
  · have hr : r = 0 := by simp [hminimum, hzero]
    simp [hr, hzero]
  · have hcard : 1 < B.card + 1 := by omega
    have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) hcard
    have hrpos := Nat.clog_pos (by decide : 1 < (2 : ℕ)) hcard
    rw [← hminimum] at hpred hrpos
    have hpower : 2 ^ r = 2 * 2 ^ r.pred := by
      calc
        _ = 2 ^ (r.pred + 1) :=
          congrArg (fun k : ℕ => 2 ^ k) (Nat.succ_pred_eq_of_pos hrpos).symm
        _ = _ := by rw [pow_succ, Nat.mul_comm]
    omega

theorem minimum_binary_seed_uniform {r : ℕ} (B : Finset (Finset (Fin r))) (hB : ∅ ∉ B)
    (hminimum : r = Nat.clog 2 (B.card + 1))
    (w : (Fin r → Bool) → ℝ) (hmass : ∑ x, w x = 1)
    (hmean : ∀ S ∈ B, walshCoefficient w S = 0)
    (hpair : ∀ S ∈ B, ∀ T ∈ B, S ≠ T →
      ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0) :
    ∀ x, w x = 1 / (2 : ℝ) ^ r :=
  full_mask_cover_uniform B hB (minimum_binary_seed_cover B hB hminimum) w hmass ⟨hmean, hpair⟩

theorem minimum_binary_seed_observed_law {r : ℕ} (B : Finset (Finset (Fin r))) (hB : ∅ ∉ B)
    (hminimum : r = Nat.clog 2 (B.card + 1))
    (hspan : Submodule.span (ZMod 2)
      (Set.range (fun S : B => binarySeed (maskSeed S.val))) = ⊤)
    (w : (Fin r → Bool) → ℝ) (hmass : ∑ x, w x = 1)
    (hmean : ∀ S ∈ B, walshCoefficient w S = 0)
    (hpair : ∀ S ∈ B, ∀ T ∈ B, S ≠ T →
      ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0) :
    (∀ x, w x = 1 / (2 : ℝ) ^ r) ∧
      (∀ y, 0 ≤ pushLaw (characterCode B) w y) ∧
      (∑ y, pushLaw (characterCode B) w y = 1) ∧
      (∀ y, pushLaw (characterCode B) w y = 0 ∨
        pushLaw (characterCode B) w y = 1 / (2 : ℝ) ^ r) ∧
      (Finset.univ.filter (fun y => pushLaw (characterCode B) w y ≠ 0)).card = 2 ^ r ∧
      collision (pushLaw (characterCode B) w) = 1 / (2 : ℝ) ^ r := by
  classical
  have huniform := minimum_binary_seed_uniform B hB hminimum w hmass hmean hpair
  have hw : ∀ x, 0 ≤ w x := by intro x; rw [huniform x]; positivity
  have hmassq : (∑ y, pushLaw (characterCode B) w y) = 1 :=
    (pushLaw_mass _ w).trans hmass
  have hweights := pushLaw_injective_weights (characterCode B) (characterCode_injective B hspan)
    w (1 / (2 : ℝ) ^ r) huniform
  have hcard : (Finset.univ.filter (fun y => pushLaw (characterCode B) w y ≠ 0)).card = 2 ^ r := by
    apply support_card_of_uniform_weights _ (2 ^ r) (by positivity) hmassq
    intro y
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hweights y
  have hcollision := (entropy_of_uniform_weights w (by positivity : (0 : ℝ) < 2 ^ r)
    hmass (fun x => Or.inr (huniform x))).1
  exact ⟨huniform, pushLaw_nonneg _ w hw, hmassq, hweights, hcard,
    (characterCode_collision B hspan w).trans hcollision⟩

end EntropyDesigns
