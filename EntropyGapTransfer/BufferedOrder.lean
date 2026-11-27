/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyGapTransfer.DyadicBuffer
public import EntropyCompleteSequence.SummaryInput
@[expose] public section
namespace EntropyDesigns.GapTransfer
open Filter Asymptotics Set
open scoped Topology

def knownHadamardOrder (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ,Matrix.IsHadamard H

def uniformGapInput (G : ℝ → ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop,∃ k : ℕ,knownHadamardOrder k ∧ x-G x≤(k:ℝ) ∧ (k:ℝ)≤x

/-- The complete finite-law witness is selected from exactly the paper's
uniform known-order gap hypothesis; no new Hadamard existence input is
silently assumed. The quantitative asymptotic rates are separate. -/
theorem buffered_hadamard_order_exists (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x))
    (hpos : ∀ x : ℝ,0≤x → 0≤G x) (hmono : MonotoneOn G (Ici 0))
    (hgap : uniformGapInput G) :
    ∀ᶠ s : ℕ in atTop,∃ k : ℕ,knownHadamardOrder k ∧
      2*dyadicBuffer G s≤(2:ℝ)^s-(k:ℝ) ∧
      (2:ℝ)^s-(k:ℝ)≤3*dyadicBuffer G s ∧
      s≤2^s-k ∧ 2^s-k<2^s/2 ∧ Nonempty (RelativeSequence.CompleteLawData k s) := by
  have ht := shifted_dyadic_tends_infinity G hG hpos
  have hw := ht.eventually hgap
  have hx := ht.eventually_ge_atTop 0
  filter_upwards [hw,hx,dyadic_buffer_eventually_small G hG] with s horder hx0 hsmall
  obtain ⟨k,hKnown,hlo,hhi⟩ := horder
  have ha := dyadic_buffer_positive G hpos s
  have hh : (0:ℝ)<(2:ℝ)^s := pow_pos (by norm_num) s
  have hs0 : (0:ℝ)≤s := Nat.cast_nonneg s
  have hxle : (2:ℝ)^s-2*dyadicBuffer G s≤(2:ℝ)^s := by linarith
  have hmon : G ((2:ℝ)^s-2*dyadicBuffer G s)≤G ((2:ℝ)^s) := hmono hx0 hh.le hxle
  have hGa : G ((2:ℝ)^s)≤dyadicBuffer G s := by
    dsimp [dyadicBuffer]
    linarith
  have hlower : 2*dyadicBuffer G s≤(2:ℝ)^s-(k:ℝ) := by linarith
  have hupper : (2:ℝ)^s-(k:ℝ)≤3*dyadicBuffer G s := by linarith
  have hkl : k<2^s := by
    have hreal : (k:ℝ)<(2:ℝ)^s := by linarith
    exact_mod_cast hreal
  have hhalf : 2^s<2*k := by
    have hreal : (2:ℝ)^s<2*(k:ℝ) := by linarith
    exact_mod_cast hreal
  have hcast : ((2^s-k:ℕ):ℝ)=(2:ℝ)^s-(k:ℝ) := by
    rw [Nat.cast_sub hkl.le,Nat.cast_pow,Nat.cast_ofNat]
  have hbudget : s≤2^s-k := by
    have hg := hpos ((2:ℝ)^s) hh.le
    have hb : (s:ℝ)≤(2:ℝ)^s-(k:ℝ) := by
      dsimp [dyadicBuffer] at hlower
      linarith
    rw [← hcast] at hb
    exact_mod_cast hb
  have hsmallNat := (RelativeSequence.power_half_gap hkl hhalf).2
  obtain ⟨K,hK⟩ := hKnown
  exact ⟨k,⟨K,hK⟩,hlower,hupper,hbudget,hsmallNat,
    RelativeSequence.spanning_summary_input hbudget hsmallNat K hK⟩

end EntropyDesigns.GapTransfer
