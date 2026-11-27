/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.PaleyApproximation
public import EntropyDesigns.WalshSubset
public import EntropyDesigns.SharpEntropyTheorem
public import Mathlib.Analysis.SpecificLimits.Normed
@[expose] public section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology
namespace EntropyDesigns

theorem paley_asymptotic_orders :
    ∃ n r : ℕ → ℕ,
      (∀ k,28 ≤ 3^(2*n k+1)+1 ∧ 3 ≤ r k ∧
        3^(2*n k+1)+1+4 ≤ 2^(r k) ∧
        2^(r k) ≤ 2*(3^(2*n k+1)+1-4)) ∧
      Tendsto (fun k => 3^(2*n k+1)+1) atTop atTop ∧
      Tendsto r atTop atTop ∧
      Tendsto (fun k => ((3^(2*n k+1)+1 : ℕ) : ℝ)/(2 : ℝ)^(r k)) atTop (𝓝 1) ∧
      Tendsto (fun k => ((2 : ℝ)^(r k)-((3^(2*n k+1)+1 : ℕ) : ℝ))/
        ((3^(2*n k+1)+1 : ℕ) : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun k => ((r k+4 : ℕ) : ℝ)/((3^(2*n k+1)+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hex (k : ℕ) := paley_near_binary_orders ((1/2 : ℝ)^k/4) (by positivity) (2^k)
  choose n r htail hn hr hN hgap hhalf hratio using hex
  let N : ℕ → ℕ := fun k => 3^(2*n k+1)+1
  have hNr (k : ℕ) : N k ≤ 2^(r k) := by have := hgap k; dsimp [N]; omega
  have hnq (k : ℕ) : n k < 3^(2*n k+1) := by
    exact lt_of_lt_of_le (Nat.lt_pow_self (by decide : 1<3))
      (Nat.pow_le_pow_right (by decide : 0<3) (by omega : n k ≤ 2*n k+1))
  have hkr (k : ℕ) : k ≤ r k := by
    have hp : 2^k < 2^(r k) := by have := htail k; have := hnq k; have := hgap k; omega
    have := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hp
    omega
  have hkN (k : ℕ) : k ≤ N k := by
    have hpow := Nat.lt_pow_self (n := k) (by decide : 1<2)
    have := htail k
    have := hnq k
    dsimp [N]
    omega
  have hNt : Tendsto N atTop atTop := tendsto_atTop_mono hkN tendsto_id
  have hrt : Tendsto r atTop atTop := tendsto_atTop_mono hkr tendsto_id
  have hδt : Tendsto (fun k : ℕ => (1/2 : ℝ)^k/4) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2)
      (by norm_num : (1/2 : ℝ)<1)).div_const 4
  have hquot : Tendsto (fun k => (N k : ℝ)/(2 : ℝ)^(r k)) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun k => 1-(1/2 : ℝ)^k/4) atTop (𝓝 1) from by
        simpa using tendsto_const_nhds.sub hδt) tendsto_const_nhds
    · intro k; simpa only [N,Nat.cast_pow,Nat.cast_ofNat] using (hratio k).le
    · intro k
      apply (div_le_one (by positivity)).mpr
      have hh : (N k : ℝ) ≤ ((2^(r k) : ℕ) : ℝ) := Nat.cast_le.mpr (hNr k)
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hmoment : Tendsto (fun k => ((2 : ℝ)^(r k)-(N k : ℝ))/(N k : ℝ)) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hquot).div hquot (by norm_num : (1 : ℝ)≠0)
    simp only [sub_self,zero_div] at hh
    convert hh using 1
    funext k
    have hNp : (0 : ℝ)<N k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<28) (hN k))
    change ((2 : ℝ)^(r k)-(N k : ℝ))/(N k : ℝ) =
      (1-(N k : ℝ)/(2 : ℝ)^(r k))/((N k : ℝ)/(2 : ℝ)^(r k))
    field_simp
    <;> ring
  have hbase : Tendsto (fun j : ℕ => 2*((j+4 : ℕ) : ℝ)/(2 : ℝ)^j) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ)<2)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ)<2)
    have hh := (h1.add (h0.const_mul 4)).const_mul 2
    simp only [pow_one,pow_zero,mul_zero,add_zero] at hh
    convert hh using 1
    funext j
    push_cast
    ring
  have hsmall : Tendsto (fun k => ((r k+4 : ℕ) : ℝ)/(N k : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => by positivity) _ (hbase.comp hrt)
    intro k
    have hNp : (0 : ℝ)<N k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<28) (hN k))
    have hLle : (2 : ℝ)^(r k) ≤ 2*(N k : ℝ) := by
      have hh : 2^(r k) ≤ 2*N k := le_trans (hhalf k) (Nat.mul_le_mul_left 2 (Nat.sub_le _ _))
      exact_mod_cast hh
    apply (div_le_div_iff₀ hNp (by positivity)).mpr
    nlinarith [show (0 : ℝ)≤((r k+4 : ℕ) : ℝ) by positivity]
  exact ⟨n,r,(fun k => ⟨hN k,hr k,hgap k,hhalf k⟩),hNt,hrt,hquot,hmoment,hsmall⟩

def exactPairwiseLaw {d : ℕ} (q : (Fin d → Bool) → ℝ) : Prop :=
  (∀ x,0≤q x) ∧ (∑ x,q x)=1 ∧
  (∀ i,∑ x,q x*(bitSign (x i) : ℝ)=0) ∧
  (∀ i j,i≠j → ∑ x,q x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0)

theorem probability_totalVariation_le_one {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ x,0≤p x) (hq : ∀ x,0≤q x)
    (hpm : ∑ x,p x=1) (hqm : ∑ x,q x=1) : totalVariation p q≤1 := by
  have hh : (∑ x,|p x-q x|)≤∑ x,(p x+q x) := by
    apply Finset.sum_le_sum
    intro x _
    exact abs_le.mpr ⟨by linarith [hp x,hq x],by linarith [hp x,hq x]⟩
  rw [Finset.sum_add_distrib,hpm,hqm] at hh
  unfold totalVariation
  linarith

theorem paley_nonvacuous_rounding_obstruction :
    ∃ (N : ℕ → ℕ) (P U : (k : ℕ) → (Fin (N k-4) → Bool) → ℝ) (ε : ℕ → ℝ),
      Tendsto N atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ k,12≤N k ∧ N k%8=4 ∧
        (∃ H : Matrix (Fin (N k)) (Fin (N k)) ℝ,Matrix.IsHadamard H) ∧
        (∀ x,0≤P k x) ∧ (∑ x,P k x)=1 ∧
        (activeSupport (P k)).card=N k ∧ collision (P k)=1/(N k : ℝ) ∧
        (∀ i,|∑ x,P k x*(bitSign (x i) : ℝ)|≤ε k) ∧
        (∀ i j,i≠j → |∑ x,P k x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)|≤ε k) ∧
        exactPairwiseLaw (U k) ∧
        (∃ q : (Fin (N k-4) → Bool) → ℝ,exactPairwiseLaw q ∧ (activeSupport q).card≤N k)) ∧
      Tendsto (fun k => totalVariation (P k) (U k)) atTop (𝓝 0) ∧
      Tendsto (fun k => (N k : ℝ)*collision (U k)) atTop (𝓝 1) ∧
      ∀ Q : (k : ℕ) → (Fin (N k-4) → Bool) → ℝ,
        (∀ k,exactPairwiseLaw (Q k) ∧ (activeSupport (Q k)).card≤N k) →
        Tendsto (fun k => totalVariation (P k) (Q k)) atTop (𝓝 1) := by
  classical
  obtain ⟨n,r,hsize,hNt,hrt,hquot,hmoment,hsmall⟩ := paley_asymptotic_orders
  let N : ℕ → ℕ := fun k => 3^(2*n k+1)+1
  have hN (k : ℕ) : 12≤N k := by have := (hsize k).1; dsimp [N]; omega
  have hres (k : ℕ) : N k%8=4 := paley_three_power_order_residue (n k)
  have hNL (k : ℕ) : N k≤2^(r k) := by have := (hsize k).2.2.1; dsimp [N]; omega
  have hhalf (k : ℕ) : 2^(r k)/2≤N k-4 := by
    have := (hsize k).2.2.2
    change 2^(r k)≤2*(N k-4) at this
    omega
  have hsub (k : ℕ) : ∃ A : Finset (Fin (r k) → Bool),A.card=N k := by
    have hc : (Finset.univ : Finset (Fin (r k) → Bool)).card=2^(r k) := by simp
    have hnc : N k≤(Finset.univ : Finset (Fin (r k) → Bool)).card := by
      rw [hc]
      exact hNL k
    obtain ⟨A,_,hA⟩ := Finset.exists_subset_card_eq hnc
    exact ⟨A,hA⟩
  choose A hA using hsub
  let P := fun k => walshSubsetLaw (N k-4) (A k)
  let U := fun k => walshSubsetLaw (r := r k) (N k-4) Finset.univ
  let ε := fun k => ((2 : ℝ)^(r k)-(N k : ℝ))/(N k : ℝ)
  have hf (k : ℕ) := walsh_subset_candidate_full (hN k) (hres k) (hNL k) (hhalf k) (A k) (hA k)
  have hhad (k : ℕ) : ∃ H : Matrix (Fin (N k)) (Fin (N k)) ℝ,Matrix.IsHadamard H :=
    paley_three_power_exists (n k)
  have hnonempty (k : ℕ) : ∃ q : (Fin (N k-4) → Bool) → ℝ,
      exactPairwiseLaw q ∧ (activeSupport q).card≤N k := by
    have hd : 2≤N k-4 := by have := hN k; omega
    have hround : roundedDimension (N k-4+1)=N k := by
      have := hres k
      have := hN k
      unfold roundedDimension
      omega
    have hh : ∃ H : Matrix (Fin (roundedDimension (N k-4+1)))
        (Fin (roundedDimension (N k-4+1))) ℝ,Matrix.IsHadamard H := by
      rw [hround]
      exact hhad k
    obtain ⟨q,hq,hm,hmean,hpair,hc⟩ := (collision_attainment_iff_hadamard hd).mpr hh
    have hcard := (sharp_sign_cube_equality_completion hd q hq hm hmean hpair hc).2.1
    rw [hround] at hcard
    exact ⟨q,⟨hq,hm,hmean,hpair⟩,hcard.le⟩
  refine ⟨N,P,U,ε,hNt,hmoment,?_,?_,?_,?_⟩
  · intro k
    rcases hf k with ⟨hp,hm,hcard,hc,hmean,hpair,hpu,huc,hu,hum,humean,hupair,hsep⟩
    exact ⟨hN k,hres k,hhad k,hp,hm,hcard,hc,hmean,hpair,⟨hu,hum,humean,hupair⟩,hnonempty k⟩
  · have hh : Tendsto (fun k => 1-(N k : ℝ)/(2 : ℝ)^(r k)) atTop (𝓝 0) := by
      simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hquot
    convert hh using 1
    funext k
    exact (hf k).2.2.2.2.2.2.1
  · convert hquot using 1
    funext k
    have hc := (hf k).2.2.2.2.2.2.2.1
    change (N k : ℝ)*collision (U k)=(N k : ℝ)/(2 : ℝ)^(r k)
    rw [hc]
    ring
  · intro Q hQ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun k => 1-((r k+4 : ℕ) : ℝ)/(N k : ℝ)) atTop (𝓝 1) from by
        simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall) tendsto_const_nhds
    · intro k
      rcases hQ k with ⟨⟨hq,hm,hmean,hpair⟩,hcard⟩
      exact (hf k).2.2.2.2.2.2.2.2.2.2.2.2 (Q k) hq hm hmean hpair hcard
    · intro k
      exact probability_totalVariation_le_one (P k) (Q k) (hf k).1 (hQ k).1.1
        (hf k).2.1 (hQ k).1.2.1

end EntropyDesigns
