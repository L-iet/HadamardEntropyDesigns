/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.DyadicScaleBounds
public import HadamardMultibase.Basic
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open Filter Asymptotics RelativeSequence GapTransfer
open scoped Topology
noncomputable section

def bufferExponent (T : ℕ → ℕ) (s : ℕ) : ℕ := max (T s) (Nat.clog 2 s)

theorem buffer_exponent_ratio_zero (T : ℕ → ℕ)
    (hT : Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    Tendsto (fun s => (bufferExponent T s:ℝ)/(s:ℝ)) atTop (nhds 0) := by
  have ht := hT.add ceiling_log_ratio_zero
  have ht' : Tendsto (fun s => ((T s:ℝ)+(Nat.clog 2 s:ℝ))/(s:ℝ)) atTop (nhds 0) := by
    simpa only [add_div,zero_add] using ht
  apply squeeze_zero (fun s => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ ht'
  intro s
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg s)
  have hb : bufferExponent T s≤T s+Nat.clog 2 s := by
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  exact_mod_cast hb

theorem buffer_exponent_eventually_small (T : ℕ → ℕ)
    (hT : Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    ∀ᶠ s : ℕ in atTop,bufferExponent T s+2<s ∧ 2^(bufferExponent T s)<2^s/2 := by
  have ht := (buffer_exponent_ratio_zero T hT).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [ht,eventually_ge_atTop (6:ℕ)] with s hs h6
  have hsR : (6:ℝ)≤s := by exact_mod_cast h6
  have hmul := (div_lt_iff₀ (by linarith : (0:ℝ)<s)).mp hs
  have hS : bufferExponent T s+2<s := by exact_mod_cast (show (bufferExponent T s:ℝ)+2<(s:ℝ) by linarith)
  have hp := Nat.pow_le_pow_right (by decide : 0<2) hS.le
  have he : (2:ℕ)^(bufferExponent T s+2)=2^(bufferExponent T s)*4 := by rw [pow_add];norm_num
  rw [he] at hp
  have hg : 0<(2:ℕ)^(bufferExponent T s) := pow_pos (by decide) _
  exact ⟨hS,by omega⟩

theorem uniform_known_order_lift (T S s : ℕ) (hTS : T≤S)
    (hu : ∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^T*q)) :
    ∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^S*q) := by
  intro q hq hqs
  have hqp : 0<q := hq.pos
  have hh : HadamardMultibase.HadamardOrder (2^T*q) := ⟨mul_pos (pow_pos (by decide) _) hqp,hu q hq hqs⟩
  have hd := hh.two_pow_mul (S-T)
  have he : 2^(S-T)*(2^T*q)=2^S*q := by
    rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hTS]
  rw [he] at hd
  exact hd.2

theorem eventually_buffered_uniform_laws (T : ℕ → ℕ)
    (hT : Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0))
    (hu : ∀ᶠ s : ℕ in atTop, ∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^(T s)*q)) :
    ∀ᶠ s : ℕ in atTop,
      knownHadamardOrder (2^s-2^(bufferExponent T s)) ∧
      Nonempty (CompleteLawData (2^s-2^(bufferExponent T s)) s) ∧
      2^s-(2^s-2^(bufferExponent T s))=2^(bufferExponent T s) := by
  filter_upwards [buffer_exponent_eventually_small T hT,hu] with s hs hu
  apply buffered_uniform_exponent_law s (bufferExponent T s) (by omega)
    (ceiling_buffer_budget s (T s)) hs.2
  exact uniform_known_order_lift (T s) (bufferExponent T s) s (le_max_left _ _) hu

end
end EntropyDesigns.ProjectInstability
