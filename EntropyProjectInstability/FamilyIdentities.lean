/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.FamilyNumericRates
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open RelativeSequence GapTransfer SupportFace
noncomputable section

/-- The numerical near-square scales are the ACTUAL support, deficits and
common entropy excess of the displayed law, at actual known matrix orders. -/
theorem dyadic_family_law_identities (F : DyadicLawFamily) (i : ℕ) :
    knownHadamardOrder (F.lowOrder i) ∧ knownHadamardOrder (F.fullOrder i) ∧
    (Concentration.observedAtoms (F.D i).law).card=(F.seedOrder i)^2 ∧
    collision (F.D i).law=1/(F.seedOrder i:ℝ)^2 ∧
    collision (F.D i).optimizer=1/(F.fullOrder i:ℝ) ∧
    1-collision (F.D i).law/collision (F.D i).optimizer=(F.gapOrder i:ℝ)/(F.seedOrder i:ℝ) ∧
    collision (F.D i).optimizer-collision (F.D i).law=
      (F.gapOrder i:ℝ)/((F.lowOrder i:ℝ)*(F.seedOrder i:ℝ)^2) ∧
    ((Concentration.observedAtoms (F.D i).law).card:ℝ)-(F.fullOrder i:ℝ)=
      (F.seedOrder i:ℝ)*(F.gapOrder i:ℝ) ∧
    (∀ α : ℝ,0<α → renyiEntropy (F.D i).law α-renyiEntropy (F.D i).optimizer α=
      Real.log ((F.seedOrder i:ℝ)/(F.lowOrder i:ℝ))) ∧
    minEntropy (F.D i).law-minEntropy (F.D i).optimizer=
      Real.log ((F.seedOrder i:ℝ)/(F.lowOrder i:ℝ)) := by
  have hs : (0:ℝ)<F.seedOrder i := by dsimp [DyadicLawFamily.seedOrder];positivity
  have hk : (0:ℝ)<F.lowOrder i := by exact_mod_cast (dyadic_family_orders F i).1
  have hgap : (F.seedOrder i:ℝ)-(F.lowOrder i:ℝ)=(F.gapOrder i:ℝ) := by
    have h := dyadic_family_cast_identity F i
    linarith
  have hcard : (Concentration.observedAtoms (F.D i).law).card=(F.seedOrder i)^2 :=
    complete_law_support_card (F.D i)
  have hpc : collision (F.D i).law=1/(F.seedOrder i:ℝ)^2 := by
    simpa only [CompleteLawData.law,DyadicLawFamily.lowOrder,DyadicLawFamily.gapOrder,DyadicLawFamily.seedOrder,Nat.cast_pow,Nat.cast_ofNat] using
      (F.D i).properties.2.2.2.1
  have hqc : collision (F.D i).optimizer=1/(F.fullOrder i:ℝ) := (F.D i).optimizer_collision
  have hratio : collision (F.D i).law/collision (F.D i).optimizer=(F.lowOrder i:ℝ)/(F.seedOrder i:ℝ) := by
    simpa only [CompleteLawData.law,DyadicLawFamily.lowOrder,DyadicLawFamily.seedOrder,DyadicLawFamily.gapOrder,Nat.cast_pow,Nat.cast_ofNat] using
      (F.D i).ratio
  obtain ⟨K,hK⟩ := F.known i
  have hfull : knownHadamardOrder (F.fullOrder i) := known_scaled_hadamard_exists (F.D i).i0 K hK
  refine ⟨F.known i,hfull,hcard,hpc,hqc,?_,?_,?_,?_,?_⟩
  · rw [hratio,←hgap]
    field_simp [hs.ne'] <;> ring
  · rw [hqc,hpc,←hgap]
    simp only [DyadicLawFamily.fullOrder,Nat.cast_mul]
    field_simp [hk.ne',hs.ne'] <;> ring
  · rw [hcard,←hgap]
    simp only [DyadicLawFamily.fullOrder,Nat.cast_mul,Nat.cast_pow]
    ring
  · intro α hα
    simpa only [CompleteLawData.law,DyadicLawFamily.lowOrder,DyadicLawFamily.gapOrder,DyadicLawFamily.seedOrder,Nat.cast_pow,Nat.cast_ofNat] using (F.D i).entropy_excess α hα
  · simpa only [CompleteLawData.law,DyadicLawFamily.lowOrder,DyadicLawFamily.gapOrder,DyadicLawFamily.seedOrder,Nat.cast_pow,Nat.cast_ofNat] using (F.D i).minentropy_excess

end
end EntropyDesigns.ProjectInstability
