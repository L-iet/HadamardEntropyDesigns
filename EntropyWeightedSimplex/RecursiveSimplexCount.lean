/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.PowerSumBounds
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

noncomputable def simplexCount : List ℝ → ℝ → ℕ
  | [], L => if 0≤L then 1 else 0
  | c::cs, L => ∑ a∈Finset.range (⌊L/c⌋₊+1),simplexCount cs (L-c*(a:ℝ))

 theorem positive_weights_product (cs : List ℝ) (hc : ∀ c∈cs,0<c) : 0<cs.prod := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.prod_cons]
    exact mul_pos (hc c (by simp)) (ih (fun a ha => hc a (by simp [ha])))

 theorem positive_weights_sum (cs : List ℝ) (hc : ∀ c∈cs,0<c) : 0≤cs.sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.sum_cons]
    exact add_nonneg (hc c (by simp)).le (ih (fun a ha => hc a (by simp [ha])))

 theorem recursive_simplex_count_bounds (cs : List ℝ) (hc : ∀ c∈cs,0<c)
    (L : ℝ) (hL : 0≤L) :
    L^cs.length/((cs.length.factorial:ℝ)*cs.prod)≤(simplexCount cs L:ℝ) ∧
    (simplexCount cs L:ℝ)≤(L+cs.sum)^cs.length/((cs.length.factorial:ℝ)*cs.prod) := by
  induction cs generalizing L with
  | nil => simp [simplexCount,hL]
  | cons c cs ih =>
    have hcpos : 0<c := hc c (by simp)
    have hcs : ∀ a∈cs,0<a := fun a ha => hc a (by simp [ha])
    let B : ℝ := (cs.length.factorial:ℝ)*cs.prod
    have hB : 0<B := mul_pos (by exact_mod_cast Nat.factorial_pos cs.length)
      (positive_weights_product cs hcs)
    have hpoint (a : ℕ) (ha : a∈Finset.range (⌊L/c⌋₊+1)) : 0≤L-c*(a:ℝ) := by
      have ham : a≤⌊L/c⌋₊ := by have hh := Finset.mem_range.mp ha;omega
      have hamR : (a:ℝ)≤(⌊L/c⌋₊:ℝ) := by exact_mod_cast ham
      have hf := Nat.floor_le (div_nonneg hL hcpos.le)
      have hh := (le_div_iff₀ hcpos).mp (hamR.trans hf)
      nlinarith
    have hlow : (∑ a∈Finset.range (⌊L/c⌋₊+1),(L-c*(a:ℝ))^cs.length)/B≤
        (simplexCount (c::cs) L:ℝ) := by
      rw [Finset.sum_div]
      simp only [simplexCount,Nat.cast_sum]
      change (∑ a∈Finset.range (⌊L/c⌋₊+1),(L-c*(a:ℝ))^cs.length/B)≤
        ∑ a∈Finset.range (⌊L/c⌋₊+1),(simplexCount cs (L-c*(a:ℝ)):ℝ)
      exact Finset.sum_le_sum fun a ha => (ih hcs (L-c*(a:ℝ)) (hpoint a ha)).1
    have hupp : (simplexCount (c::cs) L:ℝ)≤
        (∑ a∈Finset.range (⌊L/c⌋₊+1),(L+cs.sum-c*(a:ℝ))^cs.length)/B := by
      rw [Finset.sum_div]
      simp only [simplexCount,Nat.cast_sum]
      change (∑ a∈Finset.range (⌊L/c⌋₊+1),(simplexCount cs (L-c*(a:ℝ)):ℝ))≤
        ∑ a∈Finset.range (⌊L/c⌋₊+1),(L+cs.sum-c*(a:ℝ))^cs.length/B
      apply Finset.sum_le_sum
      intro a ha
      have he : L-c*(a:ℝ)+cs.sum=L+cs.sum-c*(a:ℝ) := by ring
      simpa only [he] using (ih hcs (L-c*(a:ℝ)) (hpoint a ha)).2
    have hden : (((c::cs).length.factorial:ℝ)*(c::cs).prod)=B*(c*((cs.length:ℝ)+1)) := by
      simp only [List.length_cons,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,List.prod_cons,B]
      ring
    have hpL := decreasing_power_floor_sum_lower L c hL hcpos cs.length
    have hpU := decreasing_power_floor_sum_upper L cs.sum c hL (positive_weights_sum cs hcs) hcpos cs.length
    constructor
    · calc
        _=(L^(cs.length+1)/(c*((cs.length:ℝ)+1)))/B := by
          rw [hden]
          simp only [List.length_cons,div_div]
          ring
        _≤(∑ a∈Finset.range (⌊L/c⌋₊+1),(L-c*(a:ℝ))^cs.length)/B :=
          div_le_div_of_nonneg_right hpL hB.le
        _≤_ := hlow
    · calc
        _≤(∑ a∈Finset.range (⌊L/c⌋₊+1),(L+cs.sum-c*(a:ℝ))^cs.length)/B := hupp
        _≤((L+cs.sum+c)^(cs.length+1)/(c*((cs.length:ℝ)+1)))/B :=
          div_le_div_of_nonneg_right hpU hB.le
        _=_ := by
          rw [hden]
          simp only [List.length_cons,List.sum_cons,div_div]
          have he : L+(c+cs.sum)=L+cs.sum+c := by ring
          rw [he]
          ring

end EntropyDesigns.WeightedSimplex
