/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.PaleySecond
public import EntropyDesigns.CubeIsolation
public import Mathlib.NumberTheory.FrobeniusNumber
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
namespace EntropyDesigns

theorem two_generator_conductor {a b n : ℕ} (ha : 0<a) (hb : 0<b)
    (hc : a.Coprime b) (hn : (a-1)*(b-1)≤n) :
    ∃ x y : ℕ,x*a+y*b=n := by
  by_cases h₁ : a=1
  · exact ⟨n,0,by simp [h₁]⟩
  by_cases h₂ : b=1
  · exact ⟨0,n,by simp [h₂]⟩
  have ha' : 1<a := by omega
  have hb' : 1<b := by omega
  have hpos : 0<(a-1)*(b-1) := Nat.mul_pos (by omega) (by omega)
  have hidentity : (a-1)*(b-1)+a+b=a*b+1 := by
    have hA : a-1+1=a := Nat.sub_add_cancel ha
    have hB : b-1+1=b := Nat.sub_add_cancel hb
    nlinarith
  have hlarge : a*b-a-b<n := by omega
  have hm := (frobeniusNumber_iff.mp (frobeniusNumber_pair hc ha' hb')).2 n hlarge
  simpa only [AddSubmonoid.mem_closure_pair,smul_eq_mul] using hm

theorem binary_design_of_hadamard {N d : ℕ} (hle : d+1≤N)
    (H : Matrix (Fin N) (Fin N) ℝ) (hH : Matrix.IsHadamard H) :
    ∃ rows : Fin N → Fin d → Bool,IsBinaryStrengthTwo rows := by
  classical
  let J : Fin (d + 1) ↪ Fin N :=
    ⟨Fin.castLE hle, fun _ _ h => Fin.ext (congrArg (fun k : Fin N => k.val) h)⟩
  let j₀ := J 0
  have hsign : ∀ a j, H a j = 1 ∨ H a j = -1 :=
    fun a j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem a j)
  have hsquare : ∀ a, H a j₀ ^ 2 = 1 := by
    intro a
    rcases hsign a j₀ with h | h <;> simp [h]
  let x : Fin N → Fin d → ℤ :=
    fun a i => if H a j₀ * H a (J i.succ) = 1 then 1 else -1
  have hxsign : ∀ a i, x a i = 1 ∨ x a i = -1 := by
    intro a i
    dsimp [x]
    split_ifs <;> simp
  have hvalue : ∀ a i, (x a i : ℝ) = H a j₀ * H a (J i.succ) := by
    intro a i
    rcases hsign a j₀ with h | h <;>
      rcases hsign a (J i.succ) with h' | h' <;> norm_num [x, h, h']
  have hmean : ∀ i, ∑ a, (x a i : ℝ) = 0 := by
    intro i
    simp_rw [hvalue]
    have hne : j₀ ≠ J i.succ := by
      intro h
      have : (0 : Fin (d + 1)) = i.succ := J.injective h
      exact (Fin.succ_ne_zero i) this.symm
    have hc := congrArg (fun M => M j₀ (J i.succ)) hH.conjTranspose_mul
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, hne, ite_false, mul_zero] using hc
  have hpair : ∀ i j, i ≠ j → ∑ a, (x a i : ℝ) * (x a j : ℝ) = 0 := by
    intro i j hij
    have hne : J i.succ ≠ J j.succ := by
      intro h
      apply hij
      exact Fin.ext (Nat.succ.inj (congrArg (fun k : Fin (d + 1) => k.val) (J.injective h)))
    calc
      ∑ a, (x a i : ℝ) * (x a j : ℝ) =
          ∑ a, H a (J i.succ) * H a (J j.succ) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hvalue, hvalue]
        calc
          _ = H a j₀ ^ 2 * (H a (J i.succ) * H a (J j.succ)) := by ring
          _ = _ := by rw [hsquare, one_mul]
      _ = 0 := by
        have hc := congrArg (fun M => M (J i.succ) (J j.succ)) hH.conjTranspose_mul
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
          Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
          Matrix.one_apply, smul_eq_mul, hne, ite_false, mul_zero] using hc
  let rows : Fin N → Fin d → Bool := fun a i => decide (x a i= -1)
  have hb (a : Fin N) (i : Fin d) : bitSign (rows a i)=x a i := by
    rcases hxsign a i with h|h <;> simp [rows,bitSign,h]
  refine ⟨rows,sign_moments_strength_two rows ?_ ?_⟩
  · intro i
    simp_rw [hb]
    exact_mod_cast hmean i
  · intro i j hij
    simp_rw [hb]
    exact_mod_cast hpair i j hij

theorem binary_design_stack {a b d : ℕ} (hd : 2≤d)
    (u : Fin a → Fin d → Bool) (v : Fin b → Fin d → Bool)
    (hu : IsBinaryStrengthTwo u) (hv : IsBinaryStrengthTwo v) :
    IsBinaryStrengthTwo (fun r => Fin.addCases u v r) := by
  obtain ⟨hf,hp⟩ := strength_two_all_moments hd u hu
  obtain ⟨hg,hq⟩ := strength_two_all_moments hd v hv
  apply sign_moments_strength_two
  · intro i
    rw [Fin.sum_univ_add]
    simpa using congrArg₂ (·+·) (hf i) (hg i)
  · intro i j hij
    rw [Fin.sum_univ_add]
    simpa using congrArg₂ (·+·) (hp i j hij) (hq i j hij)

theorem binary_design_replicate {a d : ℕ} (hd : 2≤d)
    (u : Fin a → Fin d → Bool) (hu : IsBinaryStrengthTwo u) (k : ℕ) :
    ∃ rows : Fin (k*a) → Fin d → Bool,IsBinaryStrengthTwo rows := by
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    refine ⟨fun i => Fin.elim0 i,?_⟩
    intro i j hij x y
    simp
  | succ k hk =>
    obtain ⟨v,hv⟩ := hk
    have hh := binary_design_stack hd v u hv hu
    have hex : ∃ rows : Fin (k*a+a) → Fin d → Bool,IsBinaryStrengthTwo rows := ⟨_,hh⟩
    rw [Nat.add_mul,Nat.one_mul]
    exact hex

theorem binary_design_coprime_conductor {a b d N : ℕ}
    (hd : 2≤d) (ha : 0<a) (hb : 0<b) (hc : a.Coprime b)
    (u : Fin (4*a) → Fin d → Bool) (v : Fin (4*b) → Fin d → Bool)
    (hu : IsBinaryStrengthTwo u) (hv : IsBinaryStrengthTwo v)
    (hN : 4∣N) (hlarge : 4*(a-1)*(b-1)≤N) :
    ∃ rows : Fin N → Fin d → Bool,IsBinaryStrengthTwo rows := by
  obtain ⟨M,rfl⟩ := hN
  have hbound : (a-1)*(b-1)≤M := by nlinarith
  obtain ⟨x,y,hxy⟩ := two_generator_conductor ha hb hc hbound
  obtain ⟨u',hu'⟩ := binary_design_replicate hd u hu x
  obtain ⟨v',hv'⟩ := binary_design_replicate hd v hv y
  have hh := binary_design_stack hd u' v' hu' hv'
  have he : x*(4*a)+y*(4*b)=4*M := by nlinarith [hxy]
  have hex : ∃ rows : Fin (x*(4*a)+y*(4*b)) → Fin d → Bool,IsBinaryStrengthTwo rows := ⟨_,hh⟩
  rwa [he] at hex

theorem binary_power_hadamard (k : ℕ) :
    ∃ H : Matrix (Fin (2^k)) (Fin (2^k)) ℝ,Matrix.IsHadamard H := by
  induction k with
  | zero =>
    refine ⟨1,?_⟩
    apply Matrix.IsHadamard.of_mul_conjTranspose
    · intro i j
      apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
      left
      have hij : i=j := Fin.ext (by have hi := i.isLt; have hj := j.isLt; norm_num at hi hj; omega)
      simp [Matrix.one_apply,hij]
    · simp
    · norm_num [isRegular_iff_ne_zero]
  | succ k hk =>
    obtain ⟨H,hH⟩ := hk
    have hh := orderTwoSign_hadamard.kronecker hH
    let e : (Fin 2 × Fin (2^k)) ≃ Fin (2^(k+1)) :=
      (Fintype.equivFin _).trans (finCongr (by simp [pow_succ,Nat.mul_comm]))
    exact ⟨_,hh.reindex e e⟩

def ternaryPaleyOrder (e : ℕ) : ℕ :=
  if e%2=0 then 2*(3^e+1) else 3^e+1

theorem ternary_power_mod_four (e : ℕ) : 3^e%4=if e%2=0 then 1 else 3 := by
  have he : e=2*(e/2)+e%2 := by omega
  conv_lhs => rw [he,pow_add,pow_mul]
  have hr : e%2=0 ∨ e%2=1 := by omega
  rcases hr with h|h <;> simp [h,Nat.mul_mod,Nat.pow_mod]

theorem ternary_power_mod_eight (e : ℕ) : 3^e%8=if e%2=0 then 1 else 3 := by
  have he : e=2*(e/2)+e%2 := by omega
  conv_lhs => rw [he,pow_add,pow_mul]
  have hr : e%2=0 ∨ e%2=1 := by omega
  rcases hr with h|h <;> simp [h,Nat.mul_mod,Nat.pow_mod]

theorem ternaryPaleyOrder_residue (e : ℕ) : ternaryPaleyOrder e%8=4 := by
  unfold ternaryPaleyOrder
  split_ifs with h
  · simp [Nat.mul_mod,Nat.add_mod,ternary_power_mod_eight,h]
  · simp [Nat.add_mod,ternary_power_mod_eight,h]

theorem ternaryPaleyOrder_exists (e : ℕ) :
    ∃ H : Matrix (Fin (ternaryPaleyOrder e)) (Fin (ternaryPaleyOrder e)) ℝ,
      Matrix.IsHadamard H := by
  classical
  by_cases he : e=0
  · subst e
    change ∃ H : Matrix (Fin 4) (Fin 4) ℝ,Matrix.IsHadamard H
    have hh := binary_power_hadamard 2
    change ∃ H : Matrix (Fin 4) (Fin 4) ℝ,Matrix.IsHadamard H at hh
    exact hh
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let F := GaloisField 3 e
  letI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F=3^e := by
    simpa only [Nat.card_eq_fintype_card] using GaloisField.card (p := 3) (n := e) he
  by_cases hp : e%2=0
  · have hq : Fintype.card F%4=1 := by rw [hc,ternary_power_mod_four]; simp [hp]
    have hh := paley_second_finite_field_exists F hq
    rw [hc] at hh
    unfold ternaryPaleyOrder
    rw [if_pos hp]
    exact hh
  · have hq : Fintype.card F%4=3 := by rw [hc,ternary_power_mod_four]; simp [hp]
    have hh := paley_finite_field_exists F hq
    rw [hc] at hh
    unfold ternaryPaleyOrder
    rw [if_neg hp]
    exact hh

theorem binary_seed_least (d : ℕ) (hd : 2≤d) :
    ∃ k : ℕ,d+1≤4*2^k ∧ 4*2^k<2*(d+1) ∧
      ∀ j<k,4*2^j<d+1 := by
  have hex : ∃ k : ℕ,d+1≤4*2^k := by
    refine ⟨d+1,?_⟩
    have hh := Nat.lt_two_pow_self (n := d+1)
    omega
  let k := Nat.find hex
  have hk : d+1≤4*2^k := Nat.find_spec hex
  have hmin (j : ℕ) (hj : j<k) : 4*2^j<d+1 := by
    have hh := Nat.find_min hex hj
    omega
  refine ⟨k,hk,?_,hmin⟩
  cases he : k with
  | zero => simp [he]; omega
  | succ l =>
    have hh := hmin l (by omega)
    rw [pow_succ]
    nlinarith

theorem ternaryPaleyOrder_ge (e : ℕ) : 3^e+1≤ternaryPaleyOrder e := by
  unfold ternaryPaleyOrder
  split_ifs <;> omega

theorem ternaryPaleyOrder_step (e : ℕ) :
    ternaryPaleyOrder (e+1)<6*ternaryPaleyOrder e := by
  have hp : e%2=0 ∨ e%2=1 := by omega
  rcases hp with hp|hp
  · have hq : (e+1)%2=1 := by omega
    simp only [ternaryPaleyOrder,hp,hq,ite_true,show ¬(1:ℕ)=0 by decide,ite_false,pow_succ]
    omega
  · have hq : (e+1)%2=0 := by omega
    simp only [ternaryPaleyOrder,hp,hq,ite_true,show ¬(1:ℕ)=0 by decide,ite_false,pow_succ]
    omega

theorem ternary_seed_least (d : ℕ) (hd : 2≤d) :
    ∃ e : ℕ,0<e ∧ d+1≤ternaryPaleyOrder e ∧ ternaryPaleyOrder e<6*(d+1) ∧
      ∀ j<e,0<j → ternaryPaleyOrder j<d+1 := by
  have hex : ∃ e : ℕ,0<e ∧ d+1≤ternaryPaleyOrder e := by
    refine ⟨d+1,by omega,?_⟩
    have hp : d+1<3^(d+1) := Nat.lt_pow_self (by decide)
    have hh := ternaryPaleyOrder_ge (d+1)
    omega
  let e := Nat.find hex
  have he := Nat.find_spec hex
  have hmin (j : ℕ) (hj : j<e) (hpos : 0<j) : ternaryPaleyOrder j<d+1 := by
    have hh := Nat.find_min hex hj
    omega
  refine ⟨e,he.1,he.2,?_,hmin⟩
  cases hidx : e with
  | zero => omega
  | succ l =>
    by_cases hl : l=0
    · subst l
      norm_num [ternaryPaleyOrder]
      omega
    · have hh := hmin l (by omega) (by omega)
      have hs := ternaryPaleyOrder_step l
      omega

theorem explicit_cofinite_central_ray (d : ℕ) (hd : 2≤d) :
    ∃ k e A B : ℕ,
      A=2^k ∧ 0<e ∧ 4*B=ternaryPaleyOrder e ∧
      d+1≤4*A ∧ (∀ j<k,4*2^j<d+1) ∧
      d+1≤4*B ∧ (∀ j<e,0<j → ternaryPaleyOrder j<d+1) ∧
      4*(A-1)*(B-1)<3*(d+1)^2 ∧
      ∀ N : ℕ,0<N → 4∣N → 4*(A-1)*(B-1)≤N →
        ∃ rows : Fin N → Fin d → Bool,IsBinaryStrengthTwo rows := by
  classical
  obtain ⟨k,hk,hks,hkmin⟩ := binary_seed_least d hd
  obtain ⟨e,hepos,he,hes,hemin⟩ := ternary_seed_least d hd
  let A := 2^k
  let b := ternaryPaleyOrder e
  let B := b/4
  have hbmod : b%8=4 := ternaryPaleyOrder_residue e
  have hb4 : 4*B=b := by dsimp [B]; omega
  have hA : 0<A := Nat.pow_pos (by decide)
  have hB : 0<B := by omega
  have hodd : ¬2∣B := by omega
  have hcop : A.Coprime B := by
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).pow_left k
  have has : 4*A<2*(d+1) := hks
  have hbs : 4*B<6*(d+1) := by rw [hb4]; exact hes
  have hprod : (4*A)*(4*B)<(2*(d+1))*(6*(d+1)) := by
    have h₁ := Nat.mul_lt_mul_of_pos_right has (by omega : 0<4*B)
    have h₂ := Nat.mul_lt_mul_of_pos_left hbs (by omega : 0<2*(d+1))
    omega
  have hsub : (A-1)*(B-1)≤A*B := Nat.mul_le_mul (Nat.sub_le A 1) (Nat.sub_le B 1)
  have hthreshold : 4*(A-1)*(B-1)<3*(d+1)^2 := by nlinarith
  refine ⟨k,e,A,B,rfl,hepos,hb4,hk,hkmin,?_,hemin,hthreshold,?_⟩
  · rw [hb4]; exact he
  · intro N hN hdiv hlarge
    have hpow : 2^(k+2)=4*A := by dsimp [A]; ring
    have hha := binary_power_hadamard (k+2)
    rw [hpow] at hha
    obtain ⟨Ha,hHa⟩ := hha
    obtain ⟨u,hu⟩ := binary_design_of_hadamard hk Ha hHa
    have hhb := ternaryPaleyOrder_exists e
    have hbe : 4*B=ternaryPaleyOrder e := hb4
    rw [← hbe] at hhb
    obtain ⟨Hb,hHb⟩ := hhb
    have hle : d+1≤4*B := by rw [hb4]; exact he
    obtain ⟨v,hv⟩ := binary_design_of_hadamard hle Hb hHb
    exact binary_design_coprime_conductor hd hA hB hcop u v hu hv hdiv hlarge

end EntropyDesigns
