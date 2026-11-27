/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.RepairLower
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open Filter
open scoped Topology

theorem sharp_distance_tends_to_one :
    Tendsto (fun r : ℕ => 1-1/(2:ℝ)^r) atTop (nhds (1:ℝ)) := by
  have h : Tendsto (fun r : ℕ => (1/(2:ℝ))^r) atTop (nhds (0:ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hh : Tendsto (fun r : ℕ => 1-(1/(2:ℝ))^r) atTop (nhds ((1:ℝ)-0)) :=
    tendsto_const_nhds.sub h
  simpa only [div_pow,one_pow,sub_zero] using hh

end
end EntropyDesigns.SupportFace
