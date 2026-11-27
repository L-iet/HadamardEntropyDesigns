/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.EntropyCoveringUpper
public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.LiminfLimsup
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open Filter
open scoped Topology

 theorem ereal_limsup_le_of_eventual_upper (f : ℕ → ℝ) (B : ℝ)
    (hf : ∀ ε : ℝ,0<ε → ∀ᶠ m : ℕ in atTop,f m≤B+ε) :
    Filter.limsup (fun m : ℕ => (f m:EReal)) atTop≤(B:EReal) := by
  by_contra h
  have hgt : (B:EReal)<Filter.limsup (fun m : ℕ => (f m:EReal)) atTop := lt_of_not_ge h
  obtain ⟨y,hBy,hyL⟩ := EReal.exists_between_coe_real hgt
  have hByR : B<y := EReal.coe_lt_coe_iff.mp hBy
  have hev := hf (y-B) (sub_pos.mpr hByR)
  have hlim : Filter.limsup (fun m : ℕ => (f m:EReal)) atTop≤(y:EReal) := by
    apply Filter.limsup_le_of_le (by isBoundedDefault)
    filter_upwards [hev] with m hm
    apply EReal.coe_le_coe
    linarith
  exact (not_le_of_gt hyL) hlim

 theorem second_order_covering_limsup {r : ℕ} (hr : 2≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) :
    Filter.limsup (fun m : ℕ => (normalizedCoveringRemainder b m:EReal)) atTop≤
      (entropyLinearConstant b:EReal) :=
  ereal_limsup_le_of_eventual_upper _ _
    (fun ε hε => normalized_covering_remainder_eventual_upper hr b hb hind ε hε)

end EntropyDesigns.WeightedSimplex
