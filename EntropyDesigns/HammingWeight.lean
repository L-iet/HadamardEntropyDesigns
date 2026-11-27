/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.SaturatedAtom
public import EntropyDesigns.Projection
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns

noncomputable def hammingWeight {d : ℕ} (x : Fin d → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i=true)).card

theorem hammingWeight_spin_sum {d : ℕ} (x : Fin d → Bool) :
    2*(hammingWeight x : ℝ)=(d : ℝ)-(∑ i,(bitSign (x i) : ℝ)) := by
  classical
  have hc : (hammingWeight x : ℝ)=(∑ i : Fin d,if x i=true then (1 : ℝ) else 0) := by
    unfold hammingWeight
    rw [Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum,Nat.cast_one,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases h : x i <;> norm_num [h]
  rw [hc,Finset.mul_sum]
  have ht (i : Fin d) : 2*(if x i=true then (1 : ℝ) else 0)=1-(bitSign (x i) : ℝ) := by
    cases h : x i <;> norm_num [h,bitSign]
  simp_rw [ht]
  simp [Finset.sum_sub_distrib]

theorem hamming_moments {d : ℕ}
    (w : (Fin d → Bool) → ℝ) (hmass : ∑ x,w x=1)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    (∑ x,w x*(hammingWeight x : ℝ))=(d : ℝ)/2 ∧
      (∑ x,w x*(hammingWeight x : ℝ)^2)=(d : ℝ)*((d : ℝ)+1)/4 := by
  classical
  let v : (Fin d → Bool) → Fin d → ℝ := fun x i => bitSign (x i)
  let S : (Fin d → Bool) → ℝ := fun x => ∑ i,v x i
  have hiso (i j : Fin d) : (∑ x,w x*v x i*v x j)=if i=j then 1 else 0 := by
    by_cases h : i=j
    · subst j
      have ht (x : Fin d → Bool) : w x*v x i*v x i=w x := by
        have hs : v x i^2=1 := by cases h : x i <;> norm_num [v,h,bitSign]
        calc
          _ = w x*(v x i)^2 := by ring
          _ = _ := by rw [hs,mul_one]
      simp_rw [ht]
      simp [hmass]
    · simpa only [if_neg h] using hpair i j h
  have hS : (∑ x,w x*S x)=0 := by
    simp only [S,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [v,hmean]
  have hS2 : (∑ x,w x*S x^2)=(d : ℝ) := by
    have hh := linear_form_second_moment v w (fun _ => 1) hiso
    simpa [S] using hh
  have hW (x : Fin d → Bool) : (hammingWeight x : ℝ)=((d : ℝ)-S x)/2 := by
    have hh := hammingWeight_spin_sum x
    change 2*(hammingWeight x : ℝ)=(d : ℝ)-S x at hh
    linarith
  constructor
  · simp_rw [hW]
    have ht (x : Fin d → Bool) : w x*(((d : ℝ)-S x)/2)=((d : ℝ)/2)*w x-(1/2 : ℝ)*(w x*S x) := by ring
    simp_rw [ht]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hmass,hS]
    ring
  · simp_rw [hW]
    have ht (x : Fin d → Bool) : w x*(((d : ℝ)-S x)/2)^2=
        ((d : ℝ)^2/4)*w x-((d : ℝ)/2)*(w x*S x)+(1/4 : ℝ)*(w x*S x^2) := by ring
    simp_rw [ht]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hmass,hS,hS2]
    ring

theorem pairwise_independent_weight_lower {d K : ℕ} (hd : 0<d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0)
    (hweight : ∀ x,0<w x → hammingWeight x≤K) : (d+2)/2≤K := by
  have ht (x : Fin d → Bool) : w x*(hammingWeight x : ℝ)^2≤(K : ℝ)*(w x*(hammingWeight x : ℝ)) := by
    by_cases hz : w x=0
    · simp [hz]
    · have hx := hweight x (lt_of_le_of_ne (hw x) (Ne.symm hz))
      have hx' : (hammingWeight x : ℝ)≤K := by exact_mod_cast hx
      have hn : (0 : ℝ)≤hammingWeight x := Nat.cast_nonneg _
      nlinarith [mul_nonneg (hw x) (mul_nonneg hn (sub_nonneg.mpr hx'))]
  have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin d → Bool))) => ht x)
  rw [← Finset.mul_sum] at hh
  obtain ⟨h1,h2⟩ := hamming_moments w hmass hmean hpair
  rw [h1,h2] at hh
  have hd' : (0 : ℝ)<d := by exact_mod_cast hd
  have hb : (d : ℝ)+1≤2*(K : ℝ) := by
    by_contra h
    have hp : 0<(d : ℝ)*((d : ℝ)+1-2*(K : ℝ)) := mul_pos hd' (by linarith)
    nlinarith
  have hb' : d+1≤2*K := by exact_mod_cast hb
  omega

def integerOrbitRows {d : ℕ} (b : Fin d → Bool) :
    (Equiv.Perm (Fin d) ⊕ (Fin d × Equiv.Perm (Fin d))) → Fin d → Bool
  | Sum.inl _, _ => false
  | Sum.inr a, i => b (a.2 i)

theorem integer_orbit_first {d : ℕ} (b : Fin d → Bool)
    (hb : (∑ i,(bitSign (b i) : ℝ))= -1) (i : Fin d) :
    (∑ a : Equiv.Perm (Fin d) ⊕ (Fin d × Equiv.Perm (Fin d)),bitSign (integerOrbitRows b a i))=0 := by
  have hh := perm_orbit_first_moment (fun i => (bitSign (b i) : ℝ)) hb i
  have hs : (∑ a : Equiv.Perm (Fin d) ⊕ (Fin d × Equiv.Perm (Fin d)),(bitSign (integerOrbitRows b a i) : ℝ))=
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ)+(d : ℝ)*(∑ σ : Equiv.Perm (Fin d),(bitSign (b (σ i)) : ℝ)) := by
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,integerOrbitRows,
      show bitSign false=1 by rfl,Int.cast_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hz : (∑ a : Equiv.Perm (Fin d) ⊕ (Fin d × Equiv.Perm (Fin d)),(bitSign (integerOrbitRows b a i) : ℝ))=0 := by rw [hs]; linarith
  exact_mod_cast hz

theorem integer_orbit_pair {d : ℕ} (hd : 1<d) (b : Fin d → Bool)
    (hb : (∑ i,(bitSign (b i) : ℝ))= -1) (i j : Fin d) (hij : i≠j) :
    (∑ a : Equiv.Perm (Fin d) ⊕ (Fin d × Equiv.Perm (Fin d)),
      bitSign (integerOrbitRows b a i)*bitSign (integerOrbitRows b a j))=0 := by
  have hsq (i : Fin d) : (bitSign (b i) : ℝ)^2=1 := by cases h : b i <;> norm_num [h,bitSign]
  have hh := perm_orbit_pair_moment hd (fun i => (bitSign (b i) : ℝ)) hb hsq i j hij
  have hs : (∑ a : Equiv.Perm (Fin d) ⊕ (Fin d × Equiv.Perm (Fin d)),
      (bitSign (integerOrbitRows b a i) : ℝ)*(bitSign (integerOrbitRows b a j) : ℝ))=
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ)+(d : ℝ)*
        (∑ σ : Equiv.Perm (Fin d),(bitSign (b (σ i)) : ℝ)*(bitSign (b (σ j)) : ℝ)) := by
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,integerOrbitRows,
      show bitSign false=1 by rfl,Int.cast_one,one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hz : (∑ a : Equiv.Perm (Fin d) ⊕ (Fin d × Equiv.Perm (Fin d)),
      (bitSign (integerOrbitRows b a i) : ℝ)*(bitSign (integerOrbitRows b a j) : ℝ))=0 := by rw [hs]; linarith
  exact_mod_cast hz

theorem hammingWeight_perm {d : ℕ} (x : Fin d → Bool) (σ : Equiv.Perm (Fin d)) :
    hammingWeight (fun i => x (σ i))=hammingWeight x := by
  apply (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℝ)))
  have h1 := hammingWeight_spin_sum (fun i => x (σ i))
  have h2 := hammingWeight_spin_sum x
  have he := Equiv.sum_comp σ (fun i => (bitSign (x i) : ℝ))
  linarith

theorem middleSliceSeed_weight (k : ℕ) : hammingWeight (middleSliceSeed k)=k+1 := by
  have hh := hammingWeight_spin_sum (middleSliceSeed k)
  rw [middleSliceSeed_sum] at hh
  have he : (hammingWeight (middleSliceSeed k) : ℝ)=((k+1 : ℕ) : ℝ) := by push_cast at hh ⊢; linarith
  exact_mod_cast he

theorem integer_orbit_weight_bound {d K : ℕ} (b : Fin d → Bool) (hb : hammingWeight b≤K)
    (a : Equiv.Perm (Fin d) ⊕ (Fin d × Equiv.Perm (Fin d))) :
    hammingWeight (integerOrbitRows b a)≤K := by
  classical
  cases a with
  | inl a => simp [integerOrbitRows,hammingWeight]
  | inr a =>
    change hammingWeight (fun i => b (a.2 i))≤K
    rw [hammingWeight_perm]
    exact hb

theorem hammingWeight_restrict {d D : ℕ} (x : Fin D → Bool) (e : Fin d ↪ Fin D) :
    hammingWeight (fun i => x (e i))≤hammingWeight x := by
  classical
  unfold hammingWeight
  apply Finset.card_le_card_of_injOn e
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact e.injective h

def IsBinaryStrengthTwo {N d : ℕ} (rows : Fin N → Fin d → Bool) : Prop :=
  ∀ i j,i≠j → ∀ a b : Bool,
    4*(Finset.univ.filter (fun r => rows r i=a ∧ rows r j=b)).card=N

theorem sign_moments_strength_two {N d : ℕ} (rows : Fin N → Fin d → Bool)
    (hfirst : ∀ i,(∑ r,bitSign (rows r i))=0)
    (hpair : ∀ i j,i≠j → (∑ r,bitSign (rows r i)*bitSign (rows r j))=0) :
    IsBinaryStrengthTwo rows := by
  classical
  intro i j hij a b
  let s := Finset.univ.filter (fun r => rows r i=a ∧ rows r j=b)
  have hc : (s.card : ℤ)=(∑ r : Fin N,if rows r i=a ∧ rows r j=b then (1 : ℤ) else 0) := by
    dsimp [s]
    rw [Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum,Nat.cast_one,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> rfl
  have ht (r : Fin N) : (4 : ℤ)*(if rows r i=a ∧ rows r j=b then 1 else 0)=
      1+bitSign a*bitSign (rows r i)+bitSign b*bitSign (rows r j)+
        (bitSign a*bitSign b)*(bitSign (rows r i)*bitSign (rows r j)) := by
    cases a <;> cases b <;> cases h1 : rows r i <;> cases h2 : rows r j <;> norm_num [h1,h2,bitSign]
  have hh : (4 : ℤ)*(s.card : ℤ)=N := by
    rw [hc,Finset.mul_sum]
    simp_rw [ht]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,hfirst,hpair i j hij,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,mul_zero,add_zero]
  exact_mod_cast hh

theorem sharp_weight_integer_array (d : ℕ) (hd : 2≤d) :
    ∃ (N : ℕ) (rows : Fin N → Fin d → Bool),
      0<N ∧ IsBinaryStrengthTwo rows ∧ (∀ r,hammingWeight (rows r)≤(d+2)/2) ∧
      (∀ i,(∑ r,bitSign (rows r i))=0) ∧
      (∀ i j,i≠j → (∑ r,bitSign (rows r i)*bitSign (rows r j))=0) := by
  classical
  let k := d/2
  let D := 2*k+1
  have hk : 1≤k := by dsimp [k]; omega
  have hdD : d≤D := by dsimp [D,k]; omega
  let e : Fin d ↪ Fin D := ⟨Fin.castLE hdD,fun _ _ h => Fin.ext (congrArg (fun i : Fin D => i.val) h)⟩
  let α := Equiv.Perm (Fin D) ⊕ (Fin D × Equiv.Perm (Fin D))
  let N := Fintype.card α
  let E : α ≃ Fin N := Fintype.equivFin α
  let rows : Fin N → Fin d → Bool := fun r i => integerOrbitRows (middleSliceSeed k) (E.symm r) (e i)
  have hN : 0<N := Fintype.card_pos
  have hfirst (i : Fin d) : (∑ r : Fin N,bitSign (rows r i))=0 := by
    change (∑ r,bitSign (integerOrbitRows (middleSliceSeed k) (E.symm r) (e i)))=0
    exact (Equiv.sum_comp E.symm (fun a : α => bitSign (integerOrbitRows (middleSliceSeed k) a (e i)))).trans
      (integer_orbit_first _ (middleSliceSeed_sum k) (e i))
  have hpair (i j : Fin d) (hij : i≠j) : (∑ r : Fin N,bitSign (rows r i)*bitSign (rows r j))=0 := by
    change (∑ r,bitSign (integerOrbitRows (middleSliceSeed k) (E.symm r) (e i))*
      bitSign (integerOrbitRows (middleSliceSeed k) (E.symm r) (e j)))=0
    have heij : e i≠e j := fun h => hij (e.injective h)
    exact (Equiv.sum_comp E.symm (fun a : α => bitSign (integerOrbitRows (middleSliceSeed k) a (e i))*
      bitSign (integerOrbitRows (middleSliceSeed k) a (e j)))).trans
      (integer_orbit_pair (by omega) _ (middleSliceSeed_sum k) (e i) (e j) heij)
  refine ⟨N,rows,hN,sign_moments_strength_two rows hfirst hpair,?_,hfirst,hpair⟩
  intro r
  have hb : hammingWeight (middleSliceSeed k)≤k+1 := (middleSliceSeed_weight k).le
  have hh := integer_orbit_weight_bound _ hb (E.symm r)
  have hr := hammingWeight_restrict (integerOrbitRows (middleSliceSeed k) (E.symm r)) e
  have hK : k+1=(d+2)/2 := by dsimp [k]; omega
  rw [← hK]
  exact hr.trans hh

theorem cube_law_of_integer_array {N d : ℕ} (hN : 0<N) (rows : Fin N → Fin d → Bool)
    (hfirst : ∀ i,(∑ r,bitSign (rows r i))=0)
    (hpair : ∀ i j,i≠j → (∑ r,bitSign (rows r i)*bitSign (rows r j))=0) :
    ∃ w : (Fin d → Bool) → ℝ,
      (∀ x,0≤w x) ∧ (∑ x,w x=1) ∧
      (∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0) ∧
      (∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) ∧
      ∀ x,0<w x → ∃ r,rows r=x := by
  classical
  let p : Fin N → ℝ := fun _ => 1/(N : ℝ)
  let w := pushLaw rows p
  have hw : ∀ x,0≤w x := by apply pushLaw_nonneg; intro r; dsimp [p]; positivity
  have hm : ∑ x,w x=1 := by
    rw [pushLaw_mass]
    simp only [p,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    exact mul_one_div_cancel hn
  have hmean (i : Fin d) : (∑ x,w x*(bitSign (x i) : ℝ))=0 := by
    rw [pushLaw_moment]
    change (∑ r : Fin N,(1/(N : ℝ))*(bitSign (rows r i) : ℝ))=0
    rw [← Finset.mul_sum]
    have hh : (∑ r : Fin N,(bitSign (rows r i) : ℝ))=0 := by exact_mod_cast hfirst i
    rw [hh,mul_zero]
  have hp (i j : Fin d) (hij : i≠j) : (∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ))=0 := by
    have hh := pushLaw_moment rows p (fun x => (bitSign (x i) : ℝ)*(bitSign (x j) : ℝ))
    have hz : (∑ r : Fin N,(bitSign (rows r i) : ℝ)*(bitSign (rows r j) : ℝ))=0 := by exact_mod_cast hpair i j hij
    have hs : (∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ))=
        (1/(N : ℝ))*(∑ r : Fin N,(bitSign (rows r i) : ℝ)*(bitSign (rows r j) : ℝ)) := by
      simpa only [w,p,mul_assoc,Finset.mul_sum] using hh
    rw [hs,hz,mul_zero]
  refine ⟨w,hw,hm,hmean,hp,?_⟩
  intro x hx
  by_contra h
  push Not at h
  have hz : w x=0 := by
    unfold w pushLaw
    apply Finset.sum_eq_zero
    intro r _
    rw [if_neg (h r)]
  linarith

theorem sharp_weight_integer_array_attained (d : ℕ) (hd : 2≤d) :
    ∃ (N : ℕ) (rows : Fin N → Fin d → Bool),
      0<N ∧ IsBinaryStrengthTwo rows ∧ (∀ r,hammingWeight (rows r)≤(d+2)/2) ∧
        ∃ r,hammingWeight (rows r)=(d+2)/2 := by
  classical
  obtain ⟨N,rows,hN,hOA,hbound,hfirst,hpair⟩ := sharp_weight_integer_array d hd
  refine ⟨N,rows,hN,hOA,hbound,?_⟩
  by_contra h
  push Not at h
  have hsmaller (r : Fin N) : hammingWeight (rows r)≤(d+2)/2-1 := by
    have hh := hbound r
    have hn := h r
    omega
  obtain ⟨w,hw,hm,hmean,hpair',hsupport⟩ := cube_law_of_integer_array hN rows hfirst hpair
  have hb := pairwise_independent_weight_lower (by omega : 0<d) w hw hm hmean hpair'
    (K := (d+2)/2-1) (fun x hx => by obtain ⟨r,hr⟩ := hsupport x hx; rw [← hr]; exact hsmaller r)
  have hpos : 0<(d+2)/2 := by omega
  omega
end EntropyDesigns
