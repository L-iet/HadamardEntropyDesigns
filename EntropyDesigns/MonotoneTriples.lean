/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.HammingWeight
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
@[expose] public section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns
open Finset
noncomputable def tripleFamily (d : ℕ) : Finset (Finset (Fin d)) := univ.filter (fun T => T.card=3)
noncomputable def pairFamily (d : ℕ) : Finset (Finset (Fin d)) := univ.filter (fun S => S.card=2)
noncomputable def tripleTotal {d : ℕ} (t : Finset (Fin d) → ℕ) : ℤ := ∑ T∈tripleFamily d,(t T : ℤ)
noncomputable def tripleSingletonLoad {d : ℕ} (t : Finset (Fin d) → ℕ) (i : Fin d) : ℤ :=
  ∑ T∈tripleFamily d,if i∈T then (t T : ℤ) else 0
noncomputable def triplePairLoad {d : ℕ} (t : Finset (Fin d) → ℕ) (S : Finset (Fin d)) : ℤ :=
  ∑ T∈tripleFamily d,if S⊆T then (t T : ℤ) else 0
noncomputable def canonicalSignedCount (d L : ℕ) (S : Finset (Fin d)) : ℤ :=
  if S.card=0 then (L : ℤ)*((d.choose 2 : ℤ)-2*d+4)
  else if S.card=1 then (L : ℤ)*(3-(d : ℤ))
  else if S.card=2 then L else 0
noncomputable def monotoneTripleCount {d : ℕ} (L : ℕ) (t : Finset (Fin d) → ℕ)
    (S : Finset (Fin d)) : ℤ := canonicalSignedCount d L S+
  ∑ T∈tripleFamily d,(t T : ℤ)*(if S⊆T then (-1 : ℤ)^(3-S.card) else 0)

theorem triple_singleton_double_count {d : ℕ} (t : Finset (Fin d) → ℕ) :
    (∑ i,tripleSingletonLoad t i)=3*tripleTotal t := by
  classical
  unfold tripleSingletonLoad tripleTotal
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hcard : T.card=3 := (Finset.mem_filter.mp hT).2
  have hf : (Finset.univ.filter (fun i : Fin d => i∈T))=T := by ext i; simp
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,hf,hcard]
  norm_num

theorem triple_pair_double_count {d : ℕ} (t : Finset (Fin d) → ℕ) :
    (∑ S∈pairFamily d,triplePairLoad t S)=3*tripleTotal t := by
  classical
  unfold triplePairLoad tripleTotal
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hcard : T.card=3 := (Finset.mem_filter.mp hT).2
  have hf : ((pairFamily d).filter (fun S => S⊆T))=T.powersetCard 2 := by
    ext S
    simp only [pairFamily,mem_filter,mem_univ,true_and,mem_powersetCard]
    tauto
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,hf,Finset.card_powersetCard,hcard]
  norm_num

theorem monotoneTripleCount_singleton {d : ℕ} (L : ℕ) (t : Finset (Fin d) → ℕ) (i : Fin d) :
    monotoneTripleCount L t {i}=(L : ℤ)*(3-(d : ℤ))+tripleSingletonLoad t i := by
  classical
  simp only [monotoneTripleCount,canonicalSignedCount,Finset.card_singleton]
  norm_num only
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  simp only [Finset.singleton_subset_iff]
  split_ifs <;> norm_num

theorem monotoneTripleCount_pair {d : ℕ} (L : ℕ) (t : Finset (Fin d) → ℕ)
    (S : Finset (Fin d)) (hS : S.card=2) :
    monotoneTripleCount L t S=(L : ℤ)-triplePairLoad t S := by
  classical
  simp only [monotoneTripleCount,canonicalSignedCount,hS]
  norm_num only
  rw [sub_eq_add_neg]
  congr 1
  rw [triplePairLoad,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> norm_num

theorem monotoneTripleCount_empty {d : ℕ} (L : ℕ) (t : Finset (Fin d) → ℕ) :
    monotoneTripleCount L t ∅=(L : ℤ)*((d.choose 2 : ℤ)-2*d+4)-tripleTotal t := by
  classical
  simp only [monotoneTripleCount,canonicalSignedCount,Finset.card_empty,ite_true,Finset.empty_subset]
  norm_num only
  rw [sub_eq_add_neg]
  congr 1
  rw [tripleTotal,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem pairFamily_card (d : ℕ) : (pairFamily d).card=d.choose 2 := by
  classical
  have hh : pairFamily d=(Finset.univ : Finset (Fin d)).powersetCard 2 := by
    ext S
    simp [pairFamily,Finset.mem_powersetCard]
  rw [hh,Finset.card_powersetCard]
  simp

theorem monotone_triple_aggregate_bounds {d L : ℕ} (t : Finset (Fin d) → ℕ)
    (hpos : ∀ S,0≤monotoneTripleCount L t S) :
    (d : ℤ)*((d : ℤ)-3)*L≤3*tripleTotal t ∧
      3*tripleTotal t≤(d.choose 2 : ℤ)*L := by
  classical
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show ((d : ℤ)-3)*L≤tripleSingletonLoad t i from by
        have hi := hpos {i}
        rw [monotoneTripleCount_singleton] at hi
        nlinarith)
    rw [triple_singleton_double_count] at hh
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh
  · have hh := Finset.sum_le_sum (s := pairFamily d) (fun S hS =>
      show triplePairLoad t S≤(L : ℤ) from by
        have hi := hpos S
        rw [monotoneTripleCount_pair L t S ((Finset.mem_filter.mp hS).2)] at hi
        linarith)
    rw [triple_pair_double_count] at hh
    simpa only [Finset.sum_const,pairFamily_card,nsmul_eq_mul] using hh

theorem monotone_triple_high_dimension_impossible {d L : ℕ} (hd : 6≤d) (hL : 0<L)
    (t : Finset (Fin d) → ℕ) : ¬ ∀ S,0≤monotoneTripleCount L t S := by
  intro hpos
  obtain ⟨hlow,hupp⟩ := monotone_triple_aggregate_bounds t hpos
  have hb := Nat.add_one_mul_choose_eq (d-1) 1
  rw [show d-1+1=d by omega,Nat.choose_one_right] at hb
  have hbZ : (d : ℤ)*((d : ℤ)-1)=2*(d.choose 2 : ℤ) := by
    have hpred : ((d-1 : ℕ) : ℤ)=(d : ℤ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    have hh : (d : ℤ)*((d-1 : ℕ) : ℤ)=(d.choose 2 : ℤ)*2 := by exact_mod_cast hb
    rw [hpred] at hh
    linarith
  have hbL := congrArg (fun z : ℤ => z*(L : ℤ)) hbZ
  have hdZ : (6 : ℤ)≤d := by exact_mod_cast hd
  have hLZ : (0 : ℤ)<L := by exact_mod_cast hL
  have hpositive : 0<(d : ℤ)*((d : ℤ)-5)*L := mul_pos (mul_pos (by omega) (by omega)) hLZ
  nlinarith

theorem monotone_triple_five_necessary {L : ℕ} (t : Finset (Fin 5) → ℕ)
    (hpos : ∀ S,0≤monotoneTripleCount L t S) : 3∣L := by
  obtain ⟨hlow,hupp⟩ := monotone_triple_aggregate_bounds t hpos
  norm_num [Nat.choose] at hlow hupp
  have hz : (L : ℤ)%3=0 := by omega
  exact_mod_cast (Int.dvd_of_emod_eq_zero hz)


theorem tripleFamily_eq (d : ℕ) : tripleFamily d=(Finset.univ : Finset (Fin d)).powersetCard 3 := by
  classical
  ext T
  simp [tripleFamily,Finset.mem_powersetCard]

theorem monotoneTripleCount_uniform {d : ℕ} (L w : ℕ) (S : Finset (Fin d)) (hS : S.card≤3) :
    monotoneTripleCount L (fun _ => w) S=canonicalSignedCount d L S+
      ((d-S.card).choose (3-S.card) : ℤ)*((w : ℤ)*(-1 : ℤ)^(3-S.card)) := by
  classical
  have hcount := Finset.card_filter_powersetCard_subset S (Finset.univ : Finset (Fin d)) 3
    (Finset.subset_univ S) hS
  simp only [Finset.card_univ,Fintype.card_fin] at hcount
  unfold monotoneTripleCount
  congr 1
  simp only [tripleFamily_eq,mul_ite,mul_zero]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,hcount]

theorem monotoneTripleCount_large {d : ℕ} (L : ℕ) (t : Finset (Fin d) → ℕ)
    (S : Finset (Fin d)) (hS : 3<S.card) : monotoneTripleCount L t S=0 := by
  classical
  have hbase : canonicalSignedCount d L S=0 := by
    simp only [canonicalSignedCount]
    split_ifs <;> omega
  rw [monotoneTripleCount,hbase,zero_add]
  apply Finset.sum_eq_zero
  intro T hT
  have hc : T.card=3 := (Finset.mem_filter.mp hT).2
  have hn : ¬ S⊆T := by intro hs; have := Finset.card_le_card hs; omega
  simp only [if_neg hn,mul_zero]

theorem monotone_triple_four_sufficient {L : ℕ} (hL : 2≤L) :
    ∀ S : Finset (Fin 4),0≤monotoneTripleCount L (fun _ => L/2) S := by
  intro S
  by_cases hS : S.card≤3
  · rw [monotoneTripleCount_uniform L (L/2) S hS]
    have hdiv : 2*(L/2)≤L := Nat.mul_div_le L 2
    have hmod : L≤2*(L/2)+1 := by omega
    interval_cases hc : S.card <;>
      norm_num [canonicalSignedCount,hc,Nat.choose] <;> omega
  · rw [monotoneTripleCount_large L _ S (by omega)]

theorem monotone_triple_five_sufficient {L : ℕ} (hL : 3∣L) :
    ∀ S : Finset (Fin 5),0≤monotoneTripleCount L (fun _ => L/3) S := by
  intro S
  have hdiv : L=3*(L/3) := by omega
  by_cases hS : S.card≤3
  · rw [monotoneTripleCount_uniform L (L/3) S hS]
    interval_cases hc : S.card <;>
      norm_num [canonicalSignedCount,hc,Nat.choose] <;> omega
  · rw [monotoneTripleCount_large L _ S (by omega)]


theorem monotone_triple_four_necessary {L : ℕ} (hL : 0<L) (t : Finset (Fin 4) → ℕ)
    (hpos : ∀ S,0≤monotoneTripleCount L t S) : 2≤L := by
  classical
  by_contra hnot
  have hL1 : L=1 := by omega
  subst L
  obtain ⟨hlow,hupp⟩ := monotone_triple_aggregate_bounds t hpos
  norm_num [Nat.choose] at hlow hupp
  have htotal : tripleTotal t=2 := by omega
  have hpair (P : Finset (Fin 4)) (hP : P.card=2) : triplePairLoad t P≤1 := by
    have hh := hpos P
    rw [monotoneTripleCount_pair 1 t P hP] at hh
    norm_num at hh
    linarith
  have hnonneg (P U : Finset (Fin 4)) : (0 : ℤ)≤(if P⊆U then (t U : ℤ) else 0) := by
    split_ifs <;> positivity
  have hsmall (T : Finset (Fin 4)) (hT : T∈tripleFamily 4) : t T≤1 := by
    have hcard : T.card=3 := (Finset.mem_filter.mp hT).2
    obtain ⟨P,hPT,hP⟩ := Finset.exists_subset_card_eq (by omega : 2≤T.card)
    have hh := Finset.single_le_sum (fun U (_ : U∈tripleFamily 4) => hnonneg P U) hT
    rw [if_pos hPT] at hh
    have hload : (t T : ℤ)≤triplePairLoad t P := hh
    have := hpair P hP
    omega
  obtain ⟨T,hT,ht⟩ : ∃ T∈tripleFamily 4,0<t T := by
    by_contra hn
    have hall (T : Finset (Fin 4)) (hT : T∈tripleFamily 4) : t T=0 := by
      by_contra hh
      exact hn ⟨T,hT,Nat.pos_of_ne_zero hh⟩
    have hz : tripleTotal t=0 := by
      unfold tripleTotal
      apply Finset.sum_eq_zero
      intro T hT
      rw [hall T hT]
      rfl
    omega
  have hother (U : Finset (Fin 4)) (hU : U∈tripleFamily 4) (hne : U≠T) : t U=0 := by
    by_contra hUn
    have hUp : 0<t U := Nat.pos_of_ne_zero hUn
    have hTc : T.card=3 := (Finset.mem_filter.mp hT).2
    have hUc : U.card=3 := (Finset.mem_filter.mp hU).2
    have hbound : (T∪U).card≤4 := by
      have hh := Finset.card_le_card (Finset.subset_univ (T∪U))
      simpa using hh
    have hcount := Finset.card_union_add_card_inter T U
    have hinter : 2≤(T∩U).card := by omega
    obtain ⟨P,hPsub,hP⟩ := Finset.exists_subset_card_eq hinter
    have hPT : P⊆T := hPsub.trans Finset.inter_subset_left
    have hPU : P⊆U := hPsub.trans Finset.inter_subset_right
    have hsub : ({T,U} : Finset (Finset (Fin 4)))⊆tripleFamily 4 := by
      intro V hV
      rcases Finset.mem_insert.mp hV with hh|hh
      · simpa only [hh] using hT
      · simpa only [Finset.mem_singleton.mp hh] using hU
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun V (_ : V∈tripleFamily 4) _ => hnonneg P V)
    have hTU : T≠U := Ne.symm hne
    rw [Finset.sum_pair hTU,if_pos hPT,if_pos hPU] at hh
    have hload : (t T : ℤ)+(t U : ℤ)≤triplePairLoad t P := hh
    have := hpair P hP
    omega
  have hone : tripleTotal t=(t T : ℤ) := by
    unfold tripleTotal
    apply Finset.sum_eq_single T
    · intro U hU hne
      rw [hother U hU hne]
      rfl
    · intro hbad
      exact (hbad hT).elim
  have := hsmall T hT
  omega

theorem monotone_triple_conversion_classification {d L : ℕ} (hd : 4≤d) (hL : 0<L) :
    (∃ t : Finset (Fin d) → ℕ,∀ S,0≤monotoneTripleCount L t S) ↔
      (d=4 ∧ 2≤L) ∨ (d=5 ∧ 3∣L) := by
  constructor
  · rintro ⟨t,ht⟩
    by_cases h4 : d=4
    · subst d
      exact Or.inl ⟨rfl,monotone_triple_four_necessary hL t ht⟩
    by_cases h5 : d=5
    · subst d
      exact Or.inr ⟨rfl,monotone_triple_five_necessary t ht⟩
    exact (monotone_triple_high_dimension_impossible (by omega) hL t ht).elim
  · rintro (⟨rfl,hfour⟩|⟨rfl,hfive⟩)
    · exact ⟨fun _ => L/2,monotone_triple_four_sufficient hfour⟩
    · exact ⟨fun _ => L/3,monotone_triple_five_sufficient hfive⟩


theorem interval_subset_sum {d : ℕ} (K T : Finset (Fin d)) (hKT : K⊆T)
    (f : Finset (Fin d) → ℤ) :
    (∑ S : Finset (Fin d),if K⊆S then (if S⊆T then f S else 0) else 0)=
      ∑ R∈(T \ K).powerset,f (R∪K) := by
  classical
  have he (S : Finset (Fin d)) :
      (if K⊆S then (if S⊆T then f S else 0) else 0)=
      if S∈(T.powerset.filter (fun S => K⊆S)) then f S else 0 := by
    by_cases h1 : K⊆S <;> by_cases h2 : S⊆T <;> simp [h1,h2]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  symm
  apply Finset.sum_bij (fun R _ => R∪K)
  · intro R hR
    have hRT : R⊆T \ K := Finset.mem_powerset.mp hR
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.union_subset (hRT.trans Finset.sdiff_subset) hKT),Finset.subset_union_right⟩
  · intro R hR V hV heq
    have hRd : Disjoint R K := Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hR) disjoint_sdiff_self_left
    have hVd : Disjoint V K := Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hV) disjoint_sdiff_self_left
    have hh := congrArg (fun S => S \ K) heq
    simpa only [Finset.union_sdiff_cancel_right hRd,Finset.union_sdiff_cancel_right hVd] using hh
  · intro S hS
    obtain ⟨hST,hKS⟩ := Finset.mem_filter.mp hS
    have hST' := Finset.mem_powerset.mp hST
    refine ⟨S \ K,Finset.mem_powerset.mpr ?_,Finset.sdiff_union_of_subset hKS⟩
    exact Finset.sdiff_subset_sdiff hST' (Finset.Subset.refl K)
  · intro R hR
    rfl

theorem origin_triple_move_moments {d : ℕ} (T K : Finset (Fin d)) (hT : T.card=3)
    (hK : K.card≤2) :
    (∑ S : Finset (Fin d),if K⊆S then
      (if S⊆T then (-1 : ℤ)^(3-S.card) else 0) else 0)=0 := by
  classical
  by_cases hKT : K⊆T
  · rw [interval_subset_sum K T hKT]
    have hnon : (T \ K).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff_of_subset hKT,hT]
      omega
    have hterm (R : Finset (Fin d)) (hR : R∈(T \ K).powerset) :
        (-1 : ℤ)^(3-(R∪K).card)=(-1 : ℤ)^(3-K.card)*(-1 : ℤ)^R.card := by
      have hRT := Finset.mem_powerset.mp hR
      have hdis : Disjoint R K := Finset.disjoint_of_subset_left hRT disjoint_sdiff_self_left
      rw [Finset.card_union_of_disjoint hdis]
      have hbound : R.card+K.card≤3 := by
        have hh := Finset.card_le_card hRT
        rw [Finset.card_sdiff_of_subset hKT,hT] at hh
        omega
      have hRc : R.card≤3 := by omega
      interval_cases hk : K.card <;> interval_cases hr : R.card <;> norm_num at *
    rw [Finset.sum_congr rfl hterm,← Finset.mul_sum,
      Finset.sum_powerset_neg_one_pow_card_of_nonempty hnon,mul_zero]
  · apply Finset.sum_eq_zero
    intro S _
    by_cases hKS : K⊆S
    · have hn : ¬ S⊆T := by intro hh; exact hKT (hKS.trans hh)
      simp only [if_pos hKS,if_neg hn]
    · simp only [if_neg hKS]


theorem monotoneTripleCount_moments_eq_canonical {d : ℕ} (L : ℕ)
    (t : Finset (Fin d) → ℕ) (K : Finset (Fin d)) (hK : K.card≤2) :
    (∑ S : Finset (Fin d),if K⊆S then monotoneTripleCount L t S else 0)=
      ∑ S : Finset (Fin d),if K⊆S then canonicalSignedCount d L S else 0 := by
  classical
  have he (S : Finset (Fin d)) :
      (if K⊆S then monotoneTripleCount L t S else 0)=
      (if K⊆S then canonicalSignedCount d L S else 0)+
      ∑ T∈tripleFamily d,(t T : ℤ)*
        (if K⊆S then (if S⊆T then (-1 : ℤ)^(3-S.card) else 0) else 0) := by
    by_cases hKS : K⊆S
    · simp only [if_pos hKS,monotoneTripleCount]
    · simp only [if_neg hKS,mul_zero,Finset.sum_const_zero,add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  have hz : (∑ T∈tripleFamily d,∑ S : Finset (Fin d),(t T : ℤ)*
      (if K⊆S then (if S⊆T then (-1 : ℤ)^(3-S.card) else 0) else 0))=0 := by
    apply Finset.sum_eq_zero
    intro T hT
    rw [← Finset.mul_sum,origin_triple_move_moments T K ((Finset.mem_filter.mp hT).2) hK,mul_zero]
  rw [hz,add_zero]


noncomputable def fixedCardMoment {d : ℕ} (K : Finset (Fin d)) (k : ℕ) : ℤ :=
  ∑ S : Finset (Fin d),if K⊆S ∧ S.card=k then 1 else 0

theorem fixedCardMoment_eq {d : ℕ} (K : Finset (Fin d)) (k : ℕ) :
    fixedCardMoment K k=if K.card≤k then ((d-K.card).choose (k-K.card) : ℤ) else 0 := by
  classical
  by_cases hK : K.card≤k
  · have hf : (Finset.univ.filter (fun S : Finset (Fin d) => K⊆S ∧ S.card=k))=
        ((Finset.univ : Finset (Fin d)).powersetCard k).filter (fun S => K⊆S) := by
      ext S
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powersetCard,Finset.subset_univ,and_comm]
    have hc := Finset.card_filter_powersetCard_subset K (Finset.univ : Finset (Fin d)) k
      (Finset.subset_univ K) hK
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    simp only [fixedCardMoment,if_pos hK,Finset.sum_ite,Finset.sum_const_zero,add_zero,
      Finset.sum_const,nsmul_eq_mul,mul_one,hf,hc]
  · rw [if_neg hK]
    unfold fixedCardMoment
    apply Finset.sum_eq_zero
    intro S _
    have hn : ¬ (K⊆S ∧ S.card=k) := by
      rintro ⟨hKS,hSk⟩
      have := Finset.card_le_card hKS
      omega
    exact if_neg hn

theorem canonicalSignedCount_moment_decomposition {d : ℕ} (L : ℕ) (K : Finset (Fin d)) :
    (∑ S : Finset (Fin d),if K⊆S then canonicalSignedCount d L S else 0)=
      ((L : ℤ)*((d.choose 2 : ℤ)-2*d+4))*fixedCardMoment K 0+
      ((L : ℤ)*(3-(d : ℤ)))*fixedCardMoment K 1+
      (L : ℤ)*fixedCardMoment K 2 := by
  classical
  simp only [fixedCardMoment,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hKS : K⊆S <;> by_cases h0 : S.card=0 <;>
    by_cases h1 : S.card=1 <;> by_cases h2 : S.card=2 <;>
    simp [canonicalSignedCount,hKS,h0,h1,h2] <;> omega

theorem canonicalSignedCount_moments {d : ℕ} (hd : 4≤d) (L : ℕ)
    (K : Finset (Fin d)) (hK : K.card≤2) :
    (∑ S : Finset (Fin d),if K⊆S then canonicalSignedCount d L S else 0)=
      if K.card=0 then (4 : ℤ)*L else if K.card=1 then (2 : ℤ)*L else L := by
  have hb := Nat.add_one_mul_choose_eq (d-1) 1
  rw [show d-1+1=d by omega,Nat.choose_one_right] at hb
  have hpred : ((d-1 : ℕ) : ℤ)=(d : ℤ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hbZ : (d : ℤ)*((d : ℤ)-1)=2*(d.choose 2 : ℤ) := by
    have hh : (d : ℤ)*((d-1 : ℕ) : ℤ)=(d.choose 2 : ℤ)*2 := by exact_mod_cast hb
    rw [hpred] at hh
    linarith
  rw [canonicalSignedCount_moment_decomposition]
  simp only [fixedCardMoment_eq]
  interval_cases hk : K.card
  · norm_num only [hk,Nat.sub_zero,Nat.choose_zero_right,Nat.choose_one_right,ite_true,ite_false]
    nlinarith [congrArg (fun z : ℤ => z*(L : ℤ)) hbZ]
  · norm_num only [hk,Nat.choose_zero_right,Nat.choose_one_right,ite_true,ite_false]
    rw [hpred]
    ring
  · norm_num only [hk,Nat.choose_zero_right,ite_true,ite_false]
    ring

theorem monotoneTripleCount_moments {d : ℕ} (hd : 4≤d) (L : ℕ)
    (t : Finset (Fin d) → ℕ) (K : Finset (Fin d)) (hK : K.card≤2) :
    (∑ S : Finset (Fin d),if K⊆S then monotoneTripleCount L t S else 0)=
      if K.card=0 then (4 : ℤ)*L else if K.card=1 then (2 : ℤ)*L else L := by
  rw [monotoneTripleCount_moments_eq_canonical L t K hK]
  exact canonicalSignedCount_moments hd L K hK

end EntropyDesigns
