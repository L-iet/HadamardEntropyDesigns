/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.FiniteSimplexBounds
public import HadamardMultibase.MultiBase
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Classical

 def IndependentIntegerBases {r : ℕ} (b : Fin r → ℕ) : Prop :=
  Function.Injective (HadamardMultibase.powerProduct b)

noncomputable def powerCount {r : ℕ} (b : Fin r → ℕ) (N : ℝ) : ℕ :=
  Nat.card {n : ℕ // 1≤n ∧ (n:ℝ)≤N ∧ n∈HadamardMultibase.powerMonoid b}

 theorem power_product_log {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i)
    (a : Fin r → ℕ) :
    Real.log (HadamardMultibase.powerProduct b a:ℝ)=∑ i,Real.log (b i:ℝ)*(a i:ℝ) := by
  unfold HadamardMultibase.powerProduct
  simp only [Nat.cast_prod,Nat.cast_pow]
  rw [Real.log_prod]
  · simp only [Real.log_pow]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    apply pow_ne_zero
    have h : (0:ℝ)<b i := by exact_mod_cast (show 0<b i by have hh := hb i;omega)
    exact h.ne'

 theorem exponent_weight_iff_product_bound {r : ℕ} (b : Fin r → ℕ) (hb : ∀ i,2≤b i)
    (a : Fin r → ℕ) (L : ℝ) :
    (∑ i,Real.log (b i:ℝ)*(a i:ℝ))≤L ↔ (HadamardMultibase.powerProduct b a:ℝ)≤Real.exp L := by
  rw [←power_product_log b hb a]
  have hp : (0:ℝ)<HadamardMultibase.powerProduct b a := by
    exact_mod_cast HadamardMultibase.powerProduct_pos hb a
  exact Real.log_le_iff_le_exp hp

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
      Nat.card {a : Fin r → ℕ // (∑ i,Real.log (b i:ℝ)*(a i:ℝ))≤L} :=
  (Nat.card_congr (exponentTupleEquivProducts b hb hind L)).symm

 theorem power_product_simplex_bounds {r : ℕ} (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (L : ℝ) (hL : 0≤L) :
    L^r/((r.factorial:ℝ)*(∏ i,Real.log (b i:ℝ)))≤(powerCount b (Real.exp L):ℝ) ∧
    (powerCount b (Real.exp L):ℝ)≤
      (L+∑ i,Real.log (b i:ℝ))^r/((r.factorial:ℝ)*(∏ i,Real.log (b i:ℝ))) := by
  rw [power_count_exponential_eq_tuple_card b hb hind L]
  apply finite_weighted_simplex_bounds _ _ L hL
  intro i
  apply Real.log_pos
  exact_mod_cast (show 1<b i by have hh := hb i;omega)

 theorem power_count_nat_eq_truncated {r : ℕ} (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (N : ℕ) :
    powerCount b (N:ℝ)=(HadamardMultibase.truncatedMonoid b N).card := by
  let e : {n : ℕ // 1≤n ∧ (n:ℝ)≤(N:ℝ) ∧ n∈HadamardMultibase.powerMonoid b} ≃
      (HadamardMultibase.truncatedMonoid b N) :=
    { toFun := fun q => ⟨q.val,(HadamardMultibase.mem_truncatedMonoid b N q.val).mpr
        ⟨by exact_mod_cast q.property.2.1,q.property.2.2⟩⟩
      invFun := fun q => by
        have hq := (HadamardMultibase.mem_truncatedMonoid b N q.val).mp q.property
        refine ⟨q.val,?_,?_,hq.2⟩
        · obtain ⟨a,ha⟩ := hq.2
          have hp := HadamardMultibase.powerProduct_pos hb a
          omega
        · exact_mod_cast hq.1
      left_inv := fun q => rfl
      right_inv := fun q => rfl }
  calc
    _=Nat.card (HadamardMultibase.truncatedMonoid b N) := Nat.card_congr e
    _=Fintype.card (HadamardMultibase.truncatedMonoid b N) := Nat.card_eq_fintype_card
    _=_ := Fintype.card_coe _

end EntropyDesigns.WeightedSimplex
