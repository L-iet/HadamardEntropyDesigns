/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyGapTransfer.BufferedOrder
public import EntropyGapTransfer.RateBounds
@[expose] public section
namespace EntropyDesigns.GapTransfer
noncomputable section
open RelativeSequence ConcentratedFamily SupportFace

theorem complete_law_support_card {k s : ℕ} (D : CompleteLawData k s) :
    (Concentration.observedAtoms D.law).card=(2^s)^2 := by
  classical
  have hc := D.properties.2.2.1
  have hp : 0<(planeSupport D.hs D.e D.i0 D.t).card := by rw [hc];positivity
  have hn : ((planeSupport D.hs D.e D.i0 D.t).card:ℝ)≠0 := by exact_mod_cast hp.ne'
  have heq : Concentration.observedAtoms D.law=planeSupport D.hs D.e D.i0 D.t := by
    ext y
    simp only [Concentration.observedAtoms,Finset.mem_filter,Finset.mem_univ,true_and,
      CompleteLawData.law,uniformFiniteLaw]
    by_cases hy : y∈planeSupport D.hs D.e D.i0 D.t <;> simp [hy,hn]
  rw [heq,hc]

theorem complete_law_rate_bounds {k s : ℕ} (D : CompleteLawData k s) (A : ℝ) (ha : 0≤A)
    (hhalf : (2:ℝ)^s/2<(k:ℝ)) (hkh : (k:ℝ)<(2:ℝ)^s)
    (hlow : 2*A≤(2:ℝ)^s-(k:ℝ)) (hupp : (2:ℝ)^s-(k:ℝ)≤3*A) :
    (2*A/(2:ℝ)^s≤1-collision D.law/collision D.optimizer ∧
      1-collision D.law/collision D.optimizer≤3*A/(2:ℝ)^s) ∧
    (2*A/((2:ℝ)^s)^3≤collision D.optimizer-collision D.law ∧
      collision D.optimizer-collision D.law≤6*A/((2:ℝ)^s)^3) ∧
    (2*(2:ℝ)^s*A≤((Concentration.observedAtoms D.law).card:ℝ)-((k*2^s:ℕ):ℝ) ∧
      ((Concentration.observedAtoms D.law).card:ℝ)-((k*2^s:ℕ):ℝ)≤3*(2:ℝ)^s*A) := by
  have hr : collision D.law/collision D.optimizer=(k:ℝ)/(2:ℝ)^s := by
    simpa only [CompleteLawData.law] using D.ratio
  have hp : collision D.law=1/((2:ℝ)^s)^2 := by
    simpa only [CompleteLawData.law] using D.properties.2.2.2.1
  have hq := D.optimizer_collision
  have hcard := complete_law_support_card D
  rw [hr,hp,hq,hcard]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  exact gap_rate_bounds ((2:ℝ)^s) (k:ℝ) A (pow_pos (by norm_num) s) ha hhalf hkh hlow hupp

end
end EntropyDesigns.GapTransfer
