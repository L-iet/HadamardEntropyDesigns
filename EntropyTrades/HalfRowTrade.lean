/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.CubeIsolation
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns
open scoped Matrix

noncomputable def halfRowSwitch {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℝ) (c₀ c₁ : ι) : Matrix ι ι ℝ :=
  fun r c => if H r c₁=1 ∧ c≠c₀ ∧ c≠c₁ then -H r c else H r c

theorem halfRowSwitch_sign {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (c₀ c₁ r c : ι) :
    halfRowSwitch H c₀ c₁ r c=1 ∨ halfRowSwitch H c₀ c₁ r c= -1 := by
  have hs := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem r c)
  unfold halfRowSwitch
  split_ifs <;> rcases hs with hs|hs <;> simp [hs]

theorem normalized_partial_column_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (c₀ c₁ b : ι)
    (hzero : ∀ r,H r c₀=1) (hb₀ : b≠c₀) (hb₁ : b≠c₁) :
    (∑ r,if H r c₁=1 then H r b else 0)=0 := by
  have hfirst : (∑ r,H r b)=0 := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M c₀ b) hH.conjTranspose_mul
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,hzero,hb₀.symm] using hh
  have hother : (∑ r,H r c₁*H r b)=0 := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M c₁ b) hH.conjTranspose_mul
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,hb₁.symm] using hh
  have hpoint (r : ι) : (if H r c₁=1 then H r b else 0)=(H r b+H r c₁*H r b)/2 := by
    rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem r c₁) with h|h <;>
      norm_num [h] <;> ring
  simp_rw [hpoint]
  rw [← Finset.sum_div,Finset.sum_add_distrib,hfirst,hother]
  norm_num

theorem halfRowSwitch_column_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (c₀ c₁ : ι)
    (hzero : ∀ r,H r c₀=1) :
    (halfRowSwitch H c₀ c₁)ᵀ*halfRowSwitch H c₀ c₁=Hᵀ*H := by
  have hcross (a b : ι) (ha : a=c₀ ∨ a=c₁) (hb : b≠c₀ ∧ b≠c₁) :
      (∑ r,halfRowSwitch H c₀ c₁ r a*halfRowSwitch H c₀ c₁ r b)=∑ r,H r a*H r b := by
    have hsum : (∑ r,if H r c₁=1 then H r a*H r b else 0)=0 := by
      have hp (r : ι) : (if H r c₁=1 then H r a*H r b else 0)=
          if H r c₁=1 then H r b else 0 := by
        by_cases hr : H r c₁=1
        · rcases ha with rfl|rfl <;> simp [hr,hzero]
        · simp [hr]
      simp_rw [hp]
      exact normalized_partial_column_sum H hH c₀ c₁ b hzero hb.1 hb.2
    have hp (r : ι) : halfRowSwitch H c₀ c₁ r a*halfRowSwitch H c₀ c₁ r b=
        H r a*H r b-2*(if H r c₁=1 then H r a*H r b else 0) := by
      by_cases hr : H r c₁=1 <;> rcases ha with rfl|rfl <;>
        simp [halfRowSwitch,hr,hb.1,hb.2] <;> ring
    simp_rw [hp]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hsum,mul_zero,sub_zero]
  ext a b
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  by_cases ha : a=c₀ ∨ a=c₁
  · by_cases hb : b=c₀ ∨ b=c₁
    · apply Finset.sum_congr rfl
      intro r _
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> simp [halfRowSwitch]
    · exact hcross a b ha (by simpa only [not_or] using hb)
  · by_cases hb : b=c₀ ∨ b=c₁
    · simpa only [mul_comm] using hcross b a hb (by simpa only [not_or] using ha)
    · have ha' : a≠c₀ ∧ a≠c₁ := by simpa only [not_or] using ha
      have hb' : b≠c₀ ∧ b≠c₁ := by simpa only [not_or] using hb
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : H r c₁=1 <;> simp [halfRowSwitch,hr,ha',hb']

theorem halfRowSwitch_hadamard {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (c₀ c₁ : ι)
    (hzero : ∀ r,H r c₀=1) : Matrix.IsHadamard (halfRowSwitch H c₀ c₁) := by
  have ht : Matrix.IsHadamard (halfRowSwitch H c₀ c₁)ᵀ := by
    apply Matrix.IsHadamard.of_mul_conjTranspose
    · intro i j
      apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
      exact halfRowSwitch_sign H hH c₀ c₁ j i
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose]
        using (halfRowSwitch_column_gram H hH c₀ c₁ hzero).trans
          (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.conjTranspose_mul)
    · apply isRegular_iff_ne_zero.mpr
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι≠0)
  simpa only [Matrix.transpose_transpose] using ht.transpose

theorem halfRowSwitch_selected_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (c₀ c₁ : ι)
    (hcols : c₁≠c₀) (hzero : ∀ r,H r c₀=1) :
    2*(Finset.univ.filter (fun r => H r c₁=1)).card=Fintype.card ι := by
  classical
  have hz : (∑ r,H r c₁)=0 := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M c₀ c₁) hH.conjTranspose_mul
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,hzero,hcols.symm] using hh
  have hp (r : ι) : H r c₁=2*(if H r c₁=1 then (1:ℝ) else 0)-1 := by
    rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem r c₁) with h|h <;> norm_num [h]
  have hc : ((Finset.univ.filter (fun r => H r c₁=1)).card:ℝ)=
      ∑ r,if H r c₁=1 then (1:ℝ) else 0 := by
    rw [Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum,Nat.cast_one,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : H r c₁=1 <;> simp [hr]
  have hsum : (∑ r,H r c₁)=2*((Finset.univ.filter (fun r => H r c₁=1)).card:ℝ)-Fintype.card ι := by
    calc
      _ = ∑ r,(2*(if H r c₁=1 then (1:ℝ) else 0)-1) :=
        Finset.sum_congr rfl (fun r _ => hp r)
      _ = _ := by
        rw [Finset.sum_sub_distrib,← Finset.mul_sum,← hc]
        simp
  have hh : 2*((Finset.univ.filter (fun r => H r c₁=1)).card:ℝ)=(Fintype.card ι:ℝ) := by linarith
  exact_mod_cast hh

theorem halfRowSwitch_row_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (c₀ c₁ r s : ι)
    (hcols : c₁≠c₀) (hzero : ∀ r,H r c₀=1) (hr : H r c₁=1) :
    (∑ c,halfRowSwitch H c₀ c₁ r c*H s c)=
      -(Fintype.card ι:ℝ)*(if r=s then 1 else 0)+2+2*H s c₁ := by
  have hexp (c : ι) : halfRowSwitch H c₀ c₁ r c=
      -H r c+(if c=c₀ then 2 else 0)+(if c=c₁ then 2 else 0) := by
    by_cases h₀ : c=c₀
    · subst c
      norm_num [halfRowSwitch,hzero,hcols.symm]
    · by_cases h₁ : c=c₁
      · subst c
        norm_num [halfRowSwitch,hr,h₀]
      · simp [halfRowSwitch,hr,h₀,h₁]
  have hrow : (∑ c,H r c*H s c)=(Fintype.card ι:ℝ)*(if r=s then 1 else 0) := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M r s) hH.mul_conjTranspose
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul] using hh
  calc
    _ = -(∑ c,H r c*H s c)+2*H s c₀+2*H s c₁ := by
      simp_rw [hexp,add_mul,neg_mul,ite_mul,zero_mul]
      simp [Finset.sum_add_distrib,Finset.sum_neg_distrib]
    _ = _ := by rw [hrow,hzero]; ring

theorem halfRowSwitch_new_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (c₀ c₁ : ι)
    (hn : 4<Fintype.card ι) (hcols : c₁≠c₀) (hzero : ∀ r,H r c₀=1)
    (r : ι) (hr : H r c₁=1) (s : ι) :
    halfRowSwitch H c₀ c₁ r≠H s := by
  intro heq
  have hi := halfRowSwitch_row_inner H hH c₀ c₁ r s hcols hzero hr
  have hself : (∑ c,H s c*H s c)=(Fintype.card ι:ℝ) := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M s s) hH.mul_conjTranspose
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply] using hh
  have hinner : (∑ c,halfRowSwitch H c₀ c₁ r c*H s c)=(Fintype.card ι:ℝ) := by
    rw [heq]
    exact hself
  have hnR : (4:ℝ)<Fintype.card ι := by exact_mod_cast hn
  rw [hinner] at hi
  by_cases hrs : r=s <;> rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem s c₁) with h|h <;>
    norm_num [hrs,h] at hi <;> nlinarith

theorem hadamard_rows_injective {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) : Function.Injective H := by
  intro r s heq
  by_contra hrs
  have hcross : (∑ c,H r c*H s c)=0 := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M r s) hH.mul_conjTranspose
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,hrs] using hh
  have hself : (∑ c,H r c*H r c)=(Fintype.card ι:ℝ) := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M r r) hH.mul_conjTranspose
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply] using hh
  rw [← heq,hself] at hcross
  have hn : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
  linarith

noncomputable def signObservation {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℝ) (c₀ r : ι) : {c : ι // c≠c₀} → Bool :=
  fun c => decide (H r c.val= -1)

theorem signObservation_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (c₀ r : ι) (c : {c : ι // c≠c₀}) :
    (bitSign (signObservation H c₀ r c):ℝ)=H r c.val := by
  rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem r c.val) with h|h <;>
    norm_num [signObservation,bitSign,h]

theorem signObservation_injective {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℝ) (hH : Matrix.IsHadamard H) (c₀ : ι) (hzero : ∀ r,H r c₀=1) :
    Function.Injective (signObservation H c₀) := by
  intro r s heq
  apply hadamard_rows_injective H hH
  funext c
  by_cases hc : c=c₀
  · subst c; rw [hzero,hzero]
  · let j : {c : ι // c≠c₀} := ⟨c,hc⟩
    have hh := congrArg (fun b : Bool => (bitSign b:ℝ)) (congrFun heq j)
    rw [signObservation_value H hH c₀ r j,signObservation_value H hH c₀ s j] at hh
    exact hh

def IsReducedObservationTrade {n : ℕ}
    (H K : Matrix (Fin n) (Fin n) ℝ) (c₀ : Fin n) (I : Finset (Fin n)) : Prop :=
  (∀ r,K r c₀=1) ∧
  Function.Injective (signObservation H c₀) ∧
  Function.Injective (signObservation K c₀) ∧
  (∀ r,r∉I → signObservation K c₀ r=signObservation H c₀ r) ∧
  (∀ r,r∈I → ∀ s,signObservation K c₀ r≠signObservation H c₀ s) ∧
  (∀ c : {c : Fin n // c≠c₀},
    (∑ r,(bitSign (signObservation K c₀ r c):ℝ))=
      ∑ r,(bitSign (signObservation H c₀ r c):ℝ)) ∧
  (∀ c d : {c : Fin n // c≠c₀},
    (∑ r,(bitSign (signObservation K c₀ r c):ℝ)*(bitSign (signObservation K c₀ r d):ℝ))=
      ∑ r,(bitSign (signObservation H c₀ r c):ℝ)*(bitSign (signObservation H c₀ r d):ℝ))

theorem universal_half_row_trade {n : ℕ} (hn : 4<n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Matrix.IsHadamard H)
    (c₀ : Fin n) (hzero : ∀ r,H r c₀=1) :
    ∃ I : Finset (Fin n),∃ K : Matrix (Fin n) (Fin n) ℝ,
      Matrix.IsHadamard K ∧ I.card=n/2 ∧ IsReducedObservationTrade H K c₀ I := by
  classical
  letI : Nonempty (Fin n) := ⟨c₀⟩
  let c₁ : Fin n := if c₀.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hcols : c₁≠c₀ := by
    intro heq
    have hh := congrArg Fin.val heq
    by_cases hc : c₀.val=0 <;> simp [c₁,hc] at hh <;> omega
  let I := Finset.univ.filter (fun r => H r c₁=1)
  let K := halfRowSwitch H c₀ c₁
  have hK : Matrix.IsHadamard K := halfRowSwitch_hadamard H hH c₀ c₁ hzero
  have hKzero (r : Fin n) : K r c₀=1 := by simp [K,halfRowSwitch,hzero]
  have hcard : I.card=n/2 := by
    have hh := halfRowSwitch_selected_card H hH c₀ c₁ hcols hzero
    simp only [Fintype.card_fin] at hh
    change 2*I.card=n at hh
    omega
  have hret (r : Fin n) (hr : r∉I) : K r=H r := by
    have hsel : H r c₁≠1 := by simpa [I] using hr
    funext c
    simp [K,halfRowSwitch,hsel]
  have hnew (r : Fin n) (hr : r∈I) (s : Fin n) :
      signObservation K c₀ r≠signObservation H c₀ s := by
    have hsel : H r c₁=1 := (Finset.mem_filter.mp hr).2
    intro heq
    apply halfRowSwitch_new_rows H hH c₀ c₁ (by simpa using hn) hcols hzero r hsel s
    change K r=H s
    funext c
    by_cases hc : c=c₀
    · subst c; rw [hKzero,hzero]
    · let j : {c : Fin n // c≠c₀} := ⟨c,hc⟩
      have hh := congrArg (fun b : Bool => (bitSign b:ℝ)) (congrFun heq j)
      rw [signObservation_value K hK c₀ r j,signObservation_value H hH c₀ s j] at hh
      exact hh
  have hgram : Kᵀ*K=Hᵀ*H := halfRowSwitch_column_gram H hH c₀ c₁ hzero
  refine ⟨I,K,hK,hcard,hKzero,signObservation_injective H hH c₀ hzero,
    signObservation_injective K hK c₀ hKzero,?_,hnew,?_,?_⟩
  · intro r hr
    funext c
    change decide (K r c.val= -1)=decide (H r c.val= -1)
    rw [hret r hr]
  · intro c
    simp_rw [signObservation_value K hK,signObservation_value H hH]
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M c₀ c.val) hgram
    simpa [Matrix.mul_apply,Matrix.transpose_apply,hKzero,hzero] using hh
  · intro c d
    simp_rw [signObservation_value K hK,signObservation_value H hH]
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M c.val d.val) hgram
    simpa only [Matrix.mul_apply,Matrix.transpose_apply] using hh

theorem binary_pair_count_formula {α : Type*} [Fintype α] [DecidableEq α]
    (u v : α → Bool) (a b : Bool) :
    (4:ℝ)*((Finset.univ.filter (fun r => u r=a ∧ v r=b)).card:ℝ)=
      Fintype.card α+(bitSign a:ℝ)*(∑ r,(bitSign (u r):ℝ))+
      (bitSign b:ℝ)*(∑ r,(bitSign (v r):ℝ))+
      ((bitSign a:ℝ)*(bitSign b:ℝ))*(∑ r,(bitSign (u r):ℝ)*(bitSign (v r):ℝ)) := by
  have hc : ((Finset.univ.filter (fun r => u r=a ∧ v r=b)).card:ℝ)=
      ∑ r,if u r=a ∧ v r=b then (1:ℝ) else 0 := by
    rw [Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> norm_num
  have hp (r : α) : (4:ℝ)*(if u r=a ∧ v r=b then 1 else 0)=
      1+(bitSign a:ℝ)*(bitSign (u r):ℝ)+(bitSign b:ℝ)*(bitSign (v r):ℝ)+
      ((bitSign a:ℝ)*(bitSign b:ℝ))*((bitSign (u r):ℝ)*(bitSign (v r):ℝ)) := by
    cases a <;> cases b <;> cases hu : u r <;> cases hv : v r <;> norm_num [hu,hv,bitSign]
  rw [hc,Finset.mul_sum]
  simp_rw [hp]
  simp [Finset.sum_add_distrib,← Finset.mul_sum]

theorem universal_half_row_observation_trade {n : ℕ} (hn : 4<n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Matrix.IsHadamard H)
    (c₀ : Fin n) (hzero : ∀ r,H r c₀=1) :
    ∃ I : Finset (Fin n),∃ K : Matrix (Fin n) (Fin n) ℝ,
      Matrix.IsHadamard K ∧ I.card=n/2 ∧ IsReducedObservationTrade H K c₀ I ∧
      ∀ c d : {c : Fin n // c≠c₀},∀ a b : Bool,
        (Finset.univ.filter (fun r => signObservation K c₀ r c=a ∧ signObservation K c₀ r d=b)).card=
        (Finset.univ.filter (fun r => signObservation H c₀ r c=a ∧ signObservation H c₀ r d=b)).card := by
  classical
  obtain ⟨I,K,hK,hcard,htrade⟩ := universal_half_row_trade hn H hH c₀ hzero
  have hm := htrade.2.2.2.2.2.1
  have hp := htrade.2.2.2.2.2.2
  refine ⟨I,K,hK,hcard,htrade,?_⟩
  intro c d a b
  have hnew := binary_pair_count_formula (fun r => signObservation K c₀ r c)
    (fun r => signObservation K c₀ r d) a b
  have hold := binary_pair_count_formula (fun r => signObservation H c₀ r c)
    (fun r => signObservation H c₀ r d) a b
  rw [hm c,hm d,hp c d] at hnew
  have hfour := hnew.trans hold.symm
  have heq := mul_left_cancel₀ (by norm_num : (4:ℝ)≠0) hfour
  exact_mod_cast heq

end EntropyDesigns
