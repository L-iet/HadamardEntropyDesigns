/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentratedFamily.ConcentratedWitness
public import EntropyConcentratedFamily.FamilyGeometry
public import EntropySupportDistance.DistanceLimit
public import Mathlib.Topology.Constructions.SumProd
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace Filter
open scoped Topology

theorem concentrated_canonical_limits :
    (∀ r : ℕ,1≤r → 2≤2^r ∧ 2*((2^r)-1)<2^(2*r) ∧ 2^(2*r)=(2^r)^2) ∧
      (∀ r : ℕ,(1/((2:ℝ)^(2*r))^2)/(1/((2^r*2^(2*r):ℕ):ℝ))=1/(2:ℝ)^r) ∧
      Tendsto (fun r : ℕ =>
        ((1/((2:ℝ)^(2*r))^2)/(1/((2^r*2^(2*r):ℕ):ℝ)),1-1/(2:ℝ)^r))
        atTop (nhds ((0:ℝ),(1:ℝ))) := by
  have hratio (r : ℕ) : (1/((2:ℝ)^(2*r))^2)/(1/((2^r*2^(2*r):ℕ):ℝ))=1/(2:ℝ)^r := by
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    have hpow : (2:ℝ)^(2*r)=((2:ℝ)^r)^2 := by rw [Nat.mul_comm,pow_mul]
    rw [hpow]
    have h2 : (2:ℝ)^r≠0 := pow_ne_zero r (by norm_num)
    field_simp <;> ring
  refine ⟨(fun r hr => canonical_family_parameters hr),hratio,?_⟩
  have hpow : Tendsto (fun r : ℕ => (1/(2:ℝ))^r) atTop (nhds (0:ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hzero : Tendsto (fun r : ℕ => 1/(2:ℝ)^r) atTop (nhds (0:ℝ)) := by
    simpa only [div_pow,one_pow] using hpow
  have hpair := hzero.prodMk_nhds sharp_distance_tends_to_one
  simpa only [hratio] using hpair

end
end EntropyDesigns.ConcentratedFamily
