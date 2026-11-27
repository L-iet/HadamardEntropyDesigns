/- Copyright (c) 2026 Joshua Mark. Apache-2.0. Independent mathlib-only specification; intentional theorem placeholders only. -/
module
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.LiminfLimsup
@[expose] public section
namespace HadamardMultibase
open scoped BigOperators
def SumOfAtMost (S : Set ℕ) (m n : ℕ) : Prop :=
  ∃ l : List ℕ,l.length≤m ∧ (∀ x∈l,x∈S) ∧ l.sum=n
def powerProduct {r : ℕ} (b e : Fin r → ℕ) : ℕ := ∏ i,b i^e i
def powerMonoid {r : ℕ} (b : Fin r → ℕ) : Set ℕ := Set.range (powerProduct b)
noncomputable def truncatedMonoid {r : ℕ} (b : Fin r → ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N+1)).filter (fun x => x∈powerMonoid b)
theorem powerProduct_pos {r : ℕ} {b : Fin r → ℕ} (hb : ∀ i,2≤b i)
    (a : Fin r → ℕ) : 0<powerProduct b a := by
  apply Finset.prod_pos
  intro i _
  exact pow_pos (show 0<b i by have hh := hb i;omega) _
end HadamardMultibase

namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators
open Set MeasureTheory

 theorem antitone_integral_le_floor_sum (f : ℝ → ℝ) (hf : Continuous f)
    (u : ℝ) (hu : 0≤u) (ha : AntitoneOn f (Icc 0 u))
    (hn : 0≤f (⌊u⌋₊:ℝ)) :
    (∫ x in (0:ℝ)..u,f x)≤∑ a∈Finset.range (⌊u⌋₊+1),f (a:ℝ) := by
  sorry

 theorem antitone_floor_sum_le_integral (f : ℝ → ℝ) (M : ℕ)
    (ha : AntitoneOn f (Icc (-1) (M:ℝ))) :
    (∑ a∈Finset.range (M+1),f (a:ℝ))≤∫ x in (-1:ℝ)..(M:ℝ),f x := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators
open Set MeasureTheory

 theorem integral_decreasing_affine_power (L c a b : ℝ) (hc : c≠0) (k : ℕ) :
    (∫ x in a..b,(L-c*x)^k)=
      ((L-c*a)^(k+1)-(L-c*b)^(k+1))/(c*((k:ℝ)+1)) := by
  sorry

 theorem decreasing_affine_power_antitone (L c a b : ℝ) (hc : 0<c) (hb : b≤L/c) (k : ℕ) :
    AntitoneOn (fun x : ℝ => (L-c*x)^k) (Icc a b) := by
  sorry

 theorem decreasing_power_floor_sum_lower (L c : ℝ) (hL : 0≤L) (hc : 0<c) (k : ℕ) :
    L^(k+1)/(c*((k:ℝ)+1))≤
      ∑ a∈Finset.range (⌊L/c⌋₊+1),(L-c*(a:ℝ))^k := by
  sorry

 theorem decreasing_power_floor_sum_upper (L C c : ℝ) (hL : 0≤L) (hC : 0≤C)
    (hc : 0<c) (k : ℕ) :
    (∑ a∈Finset.range (⌊L/c⌋₊+1),(L+C-c*(a:ℝ))^k)≤
      (L+C+c)^(k+1)/(c*((k:ℝ)+1)) := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

noncomputable def simplexCount : List ℝ → ℝ → ℕ
  | [], L => if 0≤L then 1 else 0
  | c::cs, L => ∑ a∈Finset.range (⌊L/c⌋₊+1),simplexCount cs (L-c*(a:ℝ))

 theorem positive_weights_product (cs : List ℝ) (hc : ∀ c∈cs,0<c) : 0<cs.prod := by
  sorry

 theorem positive_weights_sum (cs : List ℝ) (hc : ∀ c∈cs,0<c) : 0≤cs.sum := by
  sorry

 theorem recursive_simplex_count_bounds (cs : List ℝ) (hc : ∀ c∈cs,0<c)
    (L : ℝ) (hL : 0≤L) :
    L^cs.length/((cs.length.factorial:ℝ)*cs.prod)≤(simplexCount cs L:ℝ) ∧
    (simplexCount cs L:ℝ)≤(L+cs.sum)^cs.length/((cs.length.factorial:ℝ)*cs.prod) := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

noncomputable def SimplexChoices : List ℝ → ℝ → Type
  | [], L => {u : Unit // 0≤L}
  | c::cs, L => (a : Fin (⌊L/c⌋₊+1)) × SimplexChoices cs (L-c*(a.val:ℝ))

noncomputable instance simplexChoicesFintype (cs : List ℝ) (L : ℝ) :
    Fintype (SimplexChoices cs L) := by
  induction cs generalizing L with
  | nil => change Fintype {u : Unit // 0≤L};infer_instance
  | cons c cs ih =>
    change Fintype ((a : Fin (⌊L/c⌋₊+1)) × SimplexChoices cs (L-c*(a.val:ℝ)))
    letI (a : Fin (⌊L/c⌋₊+1)) : Fintype (SimplexChoices cs (L-c*(a.val:ℝ))) := ih _
    infer_instance

 theorem simplex_choices_card (cs : List ℝ) (L : ℝ) :
    Fintype.card (SimplexChoices cs L)=simplexCount cs L := by
  sorry

 def weightedExponentSum (cs : List ℝ) (a : Fin cs.length → ℕ) : ℝ :=
  ∑ i,cs.get i*(a i:ℝ)

 theorem weighted_exponent_sum_cons (c : ℝ) (cs : List ℝ)
    (a : Fin (c::cs).length → ℕ) :
    weightedExponentSum (c::cs) a=c*(a 0:ℝ)+weightedExponentSum cs (Fin.tail a) := by
  sorry

 theorem weighted_exponent_sum_nonnegative (cs : List ℝ) (hc : ∀ c∈cs,0<c)
    (a : Fin cs.length → ℕ) : 0≤weightedExponentSum cs a := by
  sorry

noncomputable def choiceTuple : (cs : List ℝ) → (L : ℝ) →
    SimplexChoices cs L → (Fin cs.length → ℕ)
  | [], _, _ => Fin.elim0
  | c::cs, L, q => Fin.cons q.1.val (choiceTuple cs (L-c*(q.1.val:ℝ)) q.2)

 theorem choice_tuple_weight_bound (cs : List ℝ) (L : ℝ) (q : SimplexChoices cs L) :
    weightedExponentSum cs (choiceTuple cs L q)≤L := by
  sorry

 theorem choice_tuple_injective (cs : List ℝ) (L : ℝ) :
    Function.Injective (choiceTuple cs L) := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

 theorem bounded_exponent_tuple_is_choice (cs : List ℝ) (hc : ∀ c∈cs,0<c)
    (L : ℝ) (a : Fin cs.length → ℕ) (ha : weightedExponentSum cs a≤L) :
    ∃ q : SimplexChoices cs L,choiceTuple cs L q=a := by
  sorry

noncomputable def simplexChoiceEquivTuples (cs : List ℝ) (hc : ∀ c∈cs,0<c) (L : ℝ) :
    SimplexChoices cs L ≃ {a : Fin cs.length → ℕ // weightedExponentSum cs a≤L} :=
  Equiv.ofBijective (fun q => ⟨choiceTuple cs L q,choice_tuple_weight_bound cs L q⟩)
    ⟨fun x y he => choice_tuple_injective cs L (congrArg Subtype.val he),
      fun a => by
        obtain ⟨q,hq⟩ := bounded_exponent_tuple_is_choice cs hc L a.val a.property
        exact ⟨q,Subtype.ext hq⟩⟩

 theorem simplex_lattice_card (cs : List ℝ) (hc : ∀ c∈cs,0<c) (L : ℝ) :
    Nat.card {a : Fin cs.length → ℕ // weightedExponentSum cs a≤L}=simplexCount cs L := by
  sorry

 theorem weighted_simplex_lattice_bounds (cs : List ℝ) (hc : ∀ c∈cs,0<c)
    (L : ℝ) (hL : 0≤L) :
    L^cs.length/((cs.length.factorial:ℝ)*cs.prod)≤
        (Nat.card {a : Fin cs.length → ℕ // weightedExponentSum cs a≤L}:ℝ) ∧
    (Nat.card {a : Fin cs.length → ℕ // weightedExponentSum cs a≤L}:ℝ)≤
        (L+cs.sum)^cs.length/((cs.length.factorial:ℝ)*cs.prod) := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Topology
open Filter

 theorem shifted_power_remainder_bound (T C : ℝ) (hT : 1≤T) (hC : 0≤C) (r : ℕ) :
    (T+C)^r-T^r≤(1+C)^r*T^(r-1) := by
  sorry

 theorem relative_simplex_error_bound (f T C D : ℝ) (r : ℕ) (hr : 1≤r)
    (hT : 1≤T) (hC : 0≤C) (hD : 0<D)
    (hl : T^r/D≤f) (hu : f≤(T+C)^r/D) :
    0≤f/(T^r/D)-1 ∧ f/(T^r/D)-1≤(1+C)^r/T := by
  sorry

 theorem relative_simplex_error_isBigO (f : ℝ → ℝ) (r : ℕ) (hr : 1≤r)
    (C D : ℝ) (hC : 0≤C) (hD : 0<D)
    (hb : ∀ L : ℝ,0≤L → L^r/D≤f L ∧ f L≤(L+C)^r/D) :
    (fun L : ℝ => f L/(L^r/D)-1) =O[atTop] (fun L : ℝ => 1/L) := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

 theorem finite_simplex_index_transport {r : ℕ} (c : Fin r → ℝ) (L : ℝ) :
    Nat.card {a : Fin (List.ofFn c).length → ℕ // weightedExponentSum (List.ofFn c) a≤L}=
      Nat.card {a : Fin r → ℕ // (∑ i,c i*(a i:ℝ))≤L} := by
  sorry

 theorem finite_weighted_simplex_bounds {r : ℕ} (c : Fin r → ℝ) (hc : ∀ i,0<c i)
    (L : ℝ) (hL : 0≤L) :
    L^r/((r.factorial:ℝ)*(∏ i,c i))≤
        (Nat.card {a : Fin r → ℕ // (∑ i,c i*(a i:ℝ))≤L}:ℝ) ∧
    (Nat.card {a : Fin r → ℕ // (∑ i,c i*(a i:ℝ))≤L}:ℝ)≤
        (L+∑ i,c i)^r/((r.factorial:ℝ)*(∏ i,c i)) := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

 def IndependentIntegerBases {r : ℕ} (b : Fin r → ℕ) : Prop :=
  Function.Injective (HadamardMultibase.powerProduct b)

noncomputable def powerCount {r : ℕ} (b : Fin r → ℕ) (N : ℝ) : ℕ :=
  Nat.card {n : ℕ // 1≤n ∧ (n:ℝ)≤N ∧ n∈HadamardMultibase.powerMonoid b}

 theorem power_product_log {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i)
    (a : Fin r → ℕ) :
    Real.log (HadamardMultibase.powerProduct b a:ℝ)=∑ i,Real.log (b i:ℝ)*(a i:ℝ) := by
  sorry

 theorem exponent_weight_iff_product_bound {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i)
    (a : Fin r → ℕ) (L : ℝ) :
    (∑ i,Real.log (b i:ℝ)*(a i:ℝ))≤L ↔ (HadamardMultibase.powerProduct b a:ℝ)≤Real.exp L := by
  sorry

noncomputable def exponentTupleEquivProducts {r : ℕ} (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (L : ℝ) :
    {a : Fin r → ℕ // (∑ i,Real.log (b i:ℝ)*(a i:ℝ))≤L} ≃
      {n : ℕ // 1≤n ∧ (n:ℝ)≤Real.exp L ∧ n∈HadamardMultibase.powerMonoid b} :=
  Equiv.ofBijective (fun a => ⟨HadamardMultibase.powerProduct b a.val,
    ⟨by have hh := HadamardMultibase.powerProduct_pos hb a.val;omega,
      (exponent_weight_iff_product_bound b hb a.val L).mp a.property,⟨a.val,rfl⟩⟩⟩)
    ⟨fun x y he => Subtype.ext (hind (congrArg Subtype.val he)),
      fun n => by
        obtain ⟨a,ha⟩ := n.property.2.2
        refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
        apply (exponent_weight_iff_product_bound b hb a L).mpr
        rw [ha]
        exact n.property.2.1⟩

 theorem power_count_exponential_eq_tuple_card {r : ℕ} (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (L : ℝ) :
    powerCount b (Real.exp L)=
      Nat.card {a : Fin r → ℕ // (∑ i,Real.log (b i:ℝ)*(a i:ℝ))≤L} := by
  sorry

 theorem power_product_simplex_bounds {r : ℕ} (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (L : ℝ) (hL : 0≤L) :
    L^r/((r.factorial:ℝ)*(∏ i,Real.log (b i:ℝ)))≤(powerCount b (Real.exp L):ℝ) ∧
    (powerCount b (Real.exp L):ℝ)≤
      (L+∑ i,Real.log (b i:ℝ))^r/((r.factorial:ℝ)*(∏ i,Real.log (b i:ℝ))) := by
  sorry

 theorem power_count_nat_eq_truncated {r : ℕ} (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (N : ℕ) :
    powerCount b (N:ℝ)=(HadamardMultibase.truncatedMonoid b N).card := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Topology
open Filter

noncomputable def simplexDenominator {r : ℕ} (b : Fin r → ℕ) : ℝ :=
  (r.factorial:ℝ)*(∏ i,Real.log (b i:ℝ))

noncomputable def simplexShift {r : ℕ} (b : Fin r → ℕ) : ℝ :=
  ∑ i,Real.log (b i:ℝ)

noncomputable def simplexLeadingCoefficient {r : ℕ} (b : Fin r → ℕ) : ℝ :=
  1/simplexDenominator b

 theorem simplex_denominator_positive {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i) :
    0<simplexDenominator b := by
  sorry

 theorem simplex_shift_nonnegative {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i) :
    0≤simplexShift b := by
  sorry

 theorem power_count_relative_error_isBigO {r : ℕ} (hr : 1≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) :
    (fun N : ℝ => (powerCount b N:ℝ)/(simplexLeadingCoefficient b*(Real.log N)^r)-1)
      =O[atTop] (fun N : ℝ => 1/Real.log N) := by
  sorry

 theorem power_count_asymptotic {r : ℕ} (hr : 1≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) :
    ∃ error : ℝ → ℝ,error =O[atTop] (fun N : ℝ => 1/Real.log N) ∧
      ∀ᶠ N : ℝ in atTop,(powerCount b N:ℝ)=
        simplexLeadingCoefficient b*(Real.log N)^r*(1+error N) := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open Filter
open scoped Topology

noncomputable def entropyTrialExponent (a k d : ℝ) (m : ℕ) : ℝ :=
  a*(m:ℝ)*Real.log m+k*(m:ℝ)*Real.log (Real.log m)+d*(m:ℝ)

noncomputable def entropyTrialOrder (a k d : ℝ) (m : ℕ) : ℕ :=
  ⌈Real.exp (entropyTrialExponent a k d m)⌉₊

 theorem entropy_base_scale_tendsto :
    Tendsto (fun m : ℕ => (m:ℝ)*Real.log m) atTop atTop := by
  sorry

 theorem entropy_trial_exponent_scaled_limit (a k d : ℝ) :
    Tendsto (fun m : ℕ => entropyTrialExponent a k d m/((m:ℝ)*Real.log m))
      atTop (𝓝 a) := by
  sorry

 theorem entropy_trial_exponent_eventually_positive (a k d : ℝ) (ha : 0<a) :
    ∀ᶠ m : ℕ in atTop,0<entropyTrialExponent a k d m := by
  sorry

 theorem entropy_trial_log_order_bounds (a k d : ℝ) (ha : 0<a) :
    ∀ᶠ m : ℕ in atTop,entropyTrialExponent a k d m≤Real.log (entropyTrialOrder a k d m:ℝ) ∧
      Real.log (entropyTrialOrder a k d m:ℝ)≤entropyTrialExponent a k d m+Real.log 2 := by
  sorry

 theorem entropy_trial_log_order_scaled_limit (a k d : ℝ) (ha : 0<a) :
    Tendsto (fun m : ℕ => Real.log (entropyTrialOrder a k d m:ℝ)/((m:ℝ)*Real.log m))
      atTop (𝓝 a) := by
  sorry

 theorem entropy_trial_shifted_log_scaled_limit (a k d C : ℝ) (ha : 0<a) :
    Tendsto (fun m : ℕ => (Real.log (entropyTrialOrder a k d m:ℝ)+C)/((m:ℝ)*Real.log m))
      atTop (𝓝 a) := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open Filter
open scoped BigOperators Topology

noncomputable def entropyCountEnvelope (a k d C D : ℝ) (r m : ℕ) : ℝ :=
  (Real.log (entropyTrialOrder a k d m:ℝ)+C)^r/D+(m:ℝ)

 theorem entropy_linear_over_scale_power_limit (r : ℕ) (hr : 2≤r) :
    Tendsto (fun m : ℕ => (m:ℝ)/((m:ℝ)*Real.log m)^r) atTop (𝓝 (0:ℝ)) := by
  sorry

 theorem entropy_count_envelope_scaled_limit (a k d C D : ℝ) (r : ℕ)
    (hr : 2≤r) (ha : 0<a) :
    Tendsto (fun m : ℕ => entropyCountEnvelope a k d C D r m/((m:ℝ)*Real.log m)^r)
      atTop (𝓝 (a^r/D)) := by
  sorry

 theorem entropy_count_envelope_log_limit (a k d C D : ℝ) (r : ℕ)
    (hr : 2≤r) (ha : 0<a) (hD : 0<D) :
    Tendsto (fun m : ℕ => Real.log (entropyCountEnvelope a k d C D r m)-
      (r:ℝ)*Real.log m-(r:ℝ)*Real.log (Real.log m))
      atTop (𝓝 ((r:ℝ)*Real.log a-Real.log D)) := by
  sorry

 theorem entropy_trial_order_positive (a k d : ℝ) (m : ℕ) :
    0<entropyTrialOrder a k d m := by
  sorry

 theorem truncated_monoid_sharp_log_upper {r : ℕ} (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (N : ℕ) (hN : 1≤N) :
    ((HadamardMultibase.truncatedMonoid b N).card:ℝ)≤
      (Real.log (N:ℝ)+simplexShift b)^r/simplexDenominator b := by
  sorry

 theorem entropy_trial_log_alphabet_upper {r : ℕ} (hr : 2≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b)
    (a k d ε : ℝ) (ha : 0<a) (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log ((((HadamardMultibase.truncatedMonoid b (entropyTrialOrder a k d m)).card+m:ℕ):ℝ))≤
        (r:ℝ)*Real.log m+(r:ℝ)*Real.log (Real.log m)+
          (r:ℝ)*Real.log a-Real.log (simplexDenominator b)+ε := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open Filter
open scoped BigOperators Topology Classical

noncomputable def entropyLinearConstant {r : ℕ} (b : Fin r → ℕ) : ℝ :=
  1+(r:ℝ)*Real.log ((r:ℝ)-1)-Real.log (simplexDenominator b)

noncomputable def firstUnrepresented {r : ℕ} (b : Fin r → ℕ) (m : ℕ) : ℕ :=
  sInf {n : ℕ | 0<n ∧ ¬HadamardMultibase.SumOfAtMost (HadamardMultibase.powerMonoid b) m n}

noncomputable def coveringTrialOrder {r : ℕ} (b : Fin r → ℕ) (η : ℝ) (m : ℕ) : ℕ :=
  entropyTrialOrder ((r:ℝ)-1) (r:ℝ) (entropyLinearConstant b+η/2) m

noncomputable def normalizedCoveringRemainder {r : ℕ} (b : Fin r → ℕ) (m : ℕ) : ℝ :=
  (Real.log (firstUnrepresented b m:ℝ)-((r:ℝ)-1)*(m:ℝ)*Real.log m-
    (r:ℝ)*(m:ℝ)*Real.log (Real.log m))/(m:ℝ)

 theorem first_unrepresented_spec {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i) (m : ℕ) :
    0<firstUnrepresented b m ∧
      ¬HadamardMultibase.SumOfAtMost (HadamardMultibase.powerMonoid b) m (firstUnrepresented b m) := by
  sorry

 theorem first_unrepresented_le_missing {r : ℕ} (b : Fin r → ℕ) (m n : ℕ)
    (hn : 0<n) (hmiss : ¬HadamardMultibase.SumOfAtMost (HadamardMultibase.powerMonoid b) m n) :
    firstUnrepresented b m≤n := by
  sorry

 theorem entropy_trial_choose_lt_order {r : ℕ} (hr : 2≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (η : ℝ) (hη : 0<η) :
    ∀ᶠ m : ℕ in atTop,
      ((HadamardMultibase.truncatedMonoid b (coveringTrialOrder b η m)).card+m).choose m<
        coveringTrialOrder b η m := by
  sorry

 theorem second_order_covering_upper {r : ℕ} (hr : 2≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (η : ℝ) (hη : 0<η) :
    ∀ᶠ m : ℕ in atTop,Real.log (firstUnrepresented b m:ℝ)≤
      ((r:ℝ)-1)*(m:ℝ)*Real.log m+(r:ℝ)*(m:ℝ)*Real.log (Real.log m)+
        (entropyLinearConstant b+η)*(m:ℝ) := by
  sorry

 theorem normalized_covering_remainder_eventual_upper {r : ℕ} (hr : 2≤r)
    (b : Fin r → ℕ) (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ m : ℕ in atTop,normalizedCoveringRemainder b m≤entropyLinearConstant b+η := by
  sorry

end EntropyDesigns.WeightedSimplex


namespace EntropyDesigns.WeightedSimplex
open Filter
open scoped Topology

 theorem ereal_limsup_le_of_eventual_upper (f : ℕ → ℝ) (B : ℝ)
    (hf : ∀ ε : ℝ,0<ε → ∀ᶠ m : ℕ in atTop,f m≤B+ε) :
    Filter.limsup (fun m : ℕ => (f m:EReal)) atTop≤(B:EReal) := by
  sorry

 theorem second_order_covering_limsup {r : ℕ} (hr : 2≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) :
    Filter.limsup (fun m : ℕ => (normalizedCoveringRemainder b m:EReal)) atTop≤
      (entropyLinearConstant b:EReal) := by
  sorry

end EntropyDesigns.WeightedSimplex
