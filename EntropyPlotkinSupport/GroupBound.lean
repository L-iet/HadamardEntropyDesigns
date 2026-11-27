/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPlotkinSupport.MixedRows
@[expose] public section
namespace EntropyDesigns.PlotkinSupport
noncomputable section
open SupportFace
open scoped BigOperators

theorem shared_seed_group_bound {k s : ℕ} (hk : k≤2^s)
    (e : Finset (Fin s)) (i0 : Fin k) (a : Fin s → Bool)
    (T : Finset (BlockSeeds k s)) (hseed : ∀ x∈T,x i0=a)
    (horth : ∀ x∈T,∀ y∈T,x≠y → fullSourceInner e i0 x y=0) :
    T.card≤2^s/(2^s-k+1) := by
  classical
  by_cases hT : T.Nonempty
  · letI : Nonempty {x // x∈T} := ⟨⟨hT.choose,hT.choose_spec⟩⟩
    have hk1 : 1≤k := by have hi := i0.isLt;omega
    have hkc : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub hk1];norm_num
    have hdc : ((2^s-k+1:ℕ):ℝ)=(2:ℝ)^s-(k:ℝ)+1 := by
      rw [Nat.cast_add,Nat.cast_sub hk,Nat.cast_pow];norm_num
    have hg := constant_negative_gram_bound
      (fun x : {x // x∈T} => mixedRow e i0 x.val)
      ((k-1:ℕ):ℝ) ((2:ℝ)^s-(k:ℝ)+1)
      (fun x => mixedRow_self e i0 x.val)
      (by
        intro x y hne
        apply mixedRow_pair hk e i0 x.val y.val
        · rw [hseed x.val x.property,hseed y.val y.property]
        · exact horth x.val x.property y.val y.property (fun h => hne (Subtype.ext h)))
    have hbound : ((T.card*(2^s-k+1):ℕ):ℝ)≤(2:ℝ)^s := by
      rw [Nat.cast_mul,hdc]
      have hcard : Fintype.card {x // x∈T}=T.card := Fintype.card_coe T
      rw [hcard,hkc] at hg
      linarith
    apply (Nat.le_div_iff_mul_le (by omega : 0<2^s-k+1)).2
    exact_mod_cast hbound
  · have hz : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [hz]

end
end EntropyDesigns.PlotkinSupport
