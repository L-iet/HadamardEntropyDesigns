/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyGapTransfer.LawRates
@[expose] public section
namespace EntropyDesigns.GapTransfer
noncomputable section
open Filter Asymptotics Set RelativeSequence
open scoped Topology

theorem indexed_buffered_laws (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x))
    (hpos : ∀ x : ℝ,0≤x → 0≤G x) (hmono : MonotoneOn G (Ici 0))
    (hgap : uniformGapInput G) :
    ∃ S : ℕ,∃ k : ℕ → ℕ,∃ D : (i : ℕ) → CompleteLawData (k i) (S+i),
      ∀ i : ℕ,knownHadamardOrder (k i) ∧
        2*dyadicBuffer G (S+i)≤(2:ℝ)^(S+i)-(k i:ℝ) ∧
        (2:ℝ)^(S+i)-(k i:ℝ)≤3*dyadicBuffer G (S+i) ∧
        3*dyadicBuffer G (S+i)<(2:ℝ)^(S+i)/2 := by
  classical
  have he : ∀ᶠ s : ℕ in atTop,∃ k : ℕ,knownHadamardOrder k ∧
      2*dyadicBuffer G s≤(2:ℝ)^s-(k:ℝ) ∧
      (2:ℝ)^s-(k:ℝ)≤3*dyadicBuffer G s ∧
      3*dyadicBuffer G s<(2:ℝ)^s/2 ∧ Nonempty (CompleteLawData k s) := by
    filter_upwards [buffered_hadamard_order_exists G hG hpos hmono hgap,
      dyadic_buffer_eventually_small G hG] with s hs hsmall
    obtain ⟨k,hK,hlo,hhi,hbudget,hsmallNat,hData⟩ := hs
    exact ⟨k,hK,hlo,hhi,hsmall,hData⟩
  obtain ⟨S,hS⟩ := eventually_atTop.1 he
  have hex (i : ℕ) : ∃ k : ℕ,∃ D : CompleteLawData k (S+i),
      knownHadamardOrder k ∧ 2*dyadicBuffer G (S+i)≤(2:ℝ)^(S+i)-(k:ℝ) ∧
      (2:ℝ)^(S+i)-(k:ℝ)≤3*dyadicBuffer G (S+i) ∧
      3*dyadicBuffer G (S+i)<(2:ℝ)^(S+i)/2 := by
    obtain ⟨k,hK,hlo,hhi,hsmall,⟨D⟩⟩ := hS (S+i) (Nat.le_add_right S i)
    exact ⟨k,D,hK,hlo,hhi,hsmall⟩
  choose k D hK hlo hhi hsmall using hex
  exact ⟨S,k,D,fun i => ⟨hK i,hlo i,hhi i,hsmall i⟩⟩

end
end EntropyDesigns.GapTransfer
