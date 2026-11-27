/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SourceOrthogonality
@[expose] public section
namespace EntropyDesigns.PlotkinSupport
noncomputable section
open SupportFace
open scoped BigOperators

theorem shared_seed_equal_count {k s : ℕ} (hk : k≤2^s)
    (e : Finset (Fin s)) (i0 : Fin k) (x y : BlockSeeds k s)
    (hshared : x i0=y i0) (horth : fullSourceInner e i0 x y=0) :
    (∑ j : Fin k,if x j=y j then (1:ℤ) else 0)=1 := by
  classical
  let c : ℤ := ∑ j : Fin k,if x j=y j then (1:ℤ) else 0
  have hc : 1≤c := by
    have h := Finset.single_le_sum (fun j (_ : j∈Finset.univ) =>
      show (0:ℤ)≤(if x j=y j then (1:ℤ) else 0) by split <;> norm_num)
      (Finset.mem_univ i0)
    simpa [hshared,c] using h
  have hformula := fullSourceInner_formula e i0 x y
  have hmix := relative_sum_lower e i0 x y
  have hcast : (k:ℤ)≤(2:ℤ)^s := by exact_mod_cast hk
  have hpos : (0:ℤ)<(2:ℤ)^s := pow_pos (by decide) s
  change fullSourceInner e i0 x y=(2:ℤ)^s*c-(k:ℤ)+_ at hformula
  rw [horth] at hformula
  change c=1
  by_contra hne
  have hc2 : 2≤c := by omega
  have hm := mul_le_mul_of_nonneg_left hc2 hpos.le
  nlinarith

theorem shared_seed_relative_sum {k s : ℕ} (hk : k≤2^s)
    (e : Finset (Fin s)) (i0 : Fin k) (x y : BlockSeeds k s)
    (hshared : x i0=y i0) (horth : fullSourceInner e i0 x y=0) :
    (∑ j : Fin k,relativeChar e x y i0*relativeChar e x y j)=
      (k:ℤ)-(2:ℤ)^s := by
  have h := fullSourceInner_formula e i0 x y
  rw [horth,shared_seed_equal_count hk e i0 x y hshared horth] at h
  linarith

end
end EntropyDesigns.PlotkinSupport
