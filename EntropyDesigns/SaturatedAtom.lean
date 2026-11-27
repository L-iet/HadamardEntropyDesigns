/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.Pushforward
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns
open scoped Matrix

theorem perm_orbit_first_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
    (τ : Equiv.Perm ι) (i : ι) :
    (∑ σ : Equiv.Perm ι,u (σ (τ i)))=∑ σ : Equiv.Perm ι,u (σ i) := by
  classical
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : Equiv.Perm ι => u (σ i))

theorem perm_orbit_pair_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
    (τ : Equiv.Perm ι) (i j : ι) :
    (∑ σ : Equiv.Perm ι,u (σ (τ i))*u (σ (τ j)))=
      ∑ σ : Equiv.Perm ι,u (σ i)*u (σ j) := by
  classical
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : Equiv.Perm ι => u (σ i)*u (σ j))

theorem perm_orbit_first_moment {d : ℕ} (u : Fin d → ℝ) (hu : ∑ i,u i= -1) (i : Fin d) :
    (d : ℝ)*(∑ σ : Equiv.Perm (Fin d),u (σ i))= -(Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
  classical
  have hsame (j : Fin d) : (∑ σ : Equiv.Perm (Fin d),u (σ j))=∑ σ : Equiv.Perm (Fin d),u (σ i) := by
    simpa only [Equiv.swap_apply_left] using perm_orbit_first_reindex u (Equiv.swap i j) i
  have hsum : (∑ j : Fin d,∑ σ : Equiv.Perm (Fin d),u (σ j))= -(Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
    rw [Finset.sum_comm]
    have hp (σ : Equiv.Perm (Fin d)) : (∑ j,u (σ j))= -1 := (Equiv.sum_comp σ u).trans hu
    simp_rw [hp]
    simp
  simpa only [hsame,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hsum

theorem perm_orbit_pair_moment {d : ℕ} (hd : 1<d) (u : Fin d → ℝ)
    (hu : ∑ i,u i= -1) (hsq : ∀ i,u i^2=1) (i j : Fin d) (hij : i≠j) :
    (d : ℝ)*(∑ σ : Equiv.Perm (Fin d),u (σ i)*u (σ j))= -(Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
  classical
  let m : ℝ := Fintype.card (Equiv.Perm (Fin d))
  let a : ℝ := ∑ σ : Equiv.Perm (Fin d),u (σ i)
  let b : ℝ := ∑ σ : Equiv.Perm (Fin d),u (σ i)*u (σ j)
  have hfirst : (d : ℝ)*a= -m := perm_orbit_first_moment u hu i
  have hdiag : (∑ σ : Equiv.Perm (Fin d),u (σ i)*u (σ i))=m := by
    simp only [← pow_two,hsq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,m]
  have hsame (k : Fin d) (hik : i≠k) : (∑ σ : Equiv.Perm (Fin d),u (σ i)*u (σ k))=b := by
    have hh := perm_orbit_pair_reindex u (Equiv.swap j k) i j
    simpa only [Equiv.swap_apply_of_ne_of_ne hij hik,Equiv.swap_apply_left,b] using hh
  have ht (k : Fin d) : (∑ σ : Equiv.Perm (Fin d),u (σ i)*u (σ k))=
      b+(if k=i then m-b else 0) := by
    by_cases h : k=i
    · subst k
      rw [hdiag]
      simp
    · rw [hsame k (Ne.symm h)]
      simp [h]
  have htotal : (d : ℝ)*b+(m-b)= -a := by
    have hh : (∑ k : Fin d,∑ σ : Equiv.Perm (Fin d),u (σ i)*u (σ k))= -a := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      have hp (σ : Equiv.Perm (Fin d)) : (∑ k,u (σ k))= -1 := (Equiv.sum_comp σ u).trans hu
      simp_rw [hp]
      simp [a]
    simpa [ht,Finset.sum_add_distrib] using hh
  have hzero : ((d : ℝ)-1)*((d : ℝ)*b+m)=0 := by
    linear_combination (d : ℝ)*htotal-hfirst
  have hd' : (d : ℝ)-1 ≠ 0 := by exact_mod_cast (show (d : ℤ)-1 ≠ 0 by omega)
  have hh := (mul_eq_zero.mp hzero).resolve_left hd'
  change (d : ℝ)*b= -m
  linarith

def saturatedOrbitMap {d : ℕ} (b : Fin d → Bool) : Option (Equiv.Perm (Fin d)) → (Fin d → Bool)
  | none => fun _ => false
  | some σ => fun i => b (σ i)

noncomputable def saturatedOrbitWeight (d : ℕ) : Option (Equiv.Perm (Fin d)) → ℝ
  | none => 1/((d : ℝ)+1)
  | some _ => (d : ℝ)/(((d : ℝ)+1)*(Fintype.card (Equiv.Perm (Fin d)) : ℝ))

theorem saturated_orbit_law {d : ℕ} (hd : 1<d) (b : Fin d → Bool)
    (hb : (∑ i,(bitSign (b i) : ℝ))= -1) :
    ∃ w : (Fin d → Bool) → ℝ,
      (∀ x,0≤w x) ∧ (∑ x,w x=1) ∧
      (∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0) ∧
      (∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) ∧
      w (fun _ => false)=1/((d : ℝ)+1) := by
  classical
  let u : Fin d → ℝ := fun i => bitSign (b i)
  let m : ℝ := Fintype.card (Equiv.Perm (Fin d))
  have hm : m ≠ 0 := by dsimp [m]; exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin d)) ≠ 0)
  have hn : (d : ℝ)+1 ≠ 0 := by positivity
  have hfalse : (bitSign false : ℝ)=1 := by norm_num [bitSign]
  have hu : ∑ i,u i= -1 := hb
  have husq (i : Fin d) : u i^2=1 := by cases h : b i <;> norm_num [u,h,bitSign]
  let w := pushLaw (saturatedOrbitMap b) (saturatedOrbitWeight d)
  have hw : ∀ x,0≤w x := by
    apply pushLaw_nonneg
    intro a
    cases a <;> dsimp [saturatedOrbitWeight] <;> positivity
  have hmass : ∑ x,w x=1 := by
    rw [pushLaw_mass]
    simp only [Fintype.sum_option,saturatedOrbitWeight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change 1/((d : ℝ)+1)+m*((d : ℝ)/(((d : ℝ)+1)*m))=1
    field_simp
    ring
  have hmean (i : Fin d) : (∑ x,w x*(bitSign (x i) : ℝ))=0 := by
    rw [pushLaw_moment]
    simp only [Fintype.sum_option,saturatedOrbitMap,saturatedOrbitWeight,hfalse,mul_one]
    change 1/((d : ℝ)+1)+(∑ σ : Equiv.Perm (Fin d),((d : ℝ)/(((d : ℝ)+1)*m))*u (σ i))=0
    rw [← Finset.mul_sum]
    have hh := perm_orbit_first_moment u hu i
    change (d : ℝ)*(∑ σ : Equiv.Perm (Fin d),u (σ i))= -m at hh
    field_simp
    nlinarith
  have hpair (i j : Fin d) (hij : i≠j) : (∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ))=0 := by
    have heq := pushLaw_moment (saturatedOrbitMap b) (saturatedOrbitWeight d)
      (fun x => (bitSign (x i) : ℝ)*(bitSign (x j) : ℝ))
    have hh := perm_orbit_pair_moment hd u hu husq i j hij
    change (d : ℝ)*(∑ σ : Equiv.Perm (Fin d),u (σ i)*u (σ j))= -m at hh
    simp only [Fintype.sum_option,saturatedOrbitMap,saturatedOrbitWeight,hfalse,mul_one] at heq
    have hs : (∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ))=
        1/((d : ℝ)+1)+((d : ℝ)/(((d : ℝ)+1)*m))*(∑ σ : Equiv.Perm (Fin d),u (σ i)*u (σ j)) := by
      simpa only [w,m,u,mul_assoc,Finset.mul_sum] using heq
    rw [hs]
    field_simp
    nlinarith
  have hnot (σ : Equiv.Perm (Fin d)) : saturatedOrbitMap b (some σ) ≠ fun _ => false := by
    intro heq
    have hp (i : Fin d) : b (σ i)=false := congrFun heq i
    have hh := (Equiv.sum_comp σ u).trans hu
    simp [u,hp,bitSign] at hh
    have hd' : (0 : ℝ)≤d := Nat.cast_nonneg d
    linarith
  have hspecial : w (fun _ => false)=1/((d : ℝ)+1) := by
    unfold w pushLaw
    have hnot' (σ : Equiv.Perm (Fin d)) : (fun i => b (σ i)) ≠ fun _ => false := hnot σ
    simp [Fintype.sum_option,hnot',saturatedOrbitMap,saturatedOrbitWeight]
  exact ⟨w,hw,hmass,hmean,hpair,hspecial⟩

def middleSliceSeed (k : ℕ) : Fin (2*k+1) → Bool :=
  fun i => Sum.elim (fun _ : Fin (k+1) => true) (fun _ : Fin k => false)
    (((finCongr (show 2*k+1=(k+1)+k by omega)).trans finSumFinEquiv.symm) i)

theorem middleSliceSeed_sum (k : ℕ) :
    (∑ i,(bitSign (middleSliceSeed k i) : ℝ))= -1 := by
  let e : Fin (2*k+1) ≃ Fin (k+1) ⊕ Fin k :=
    (finCongr (show 2*k+1=(k+1)+k by omega)).trans finSumFinEquiv.symm
  let f : (Fin (k+1) ⊕ Fin k) → ℝ :=
    fun i => bitSign (Sum.elim (fun _ : Fin (k+1) => true) (fun _ : Fin k => false) i)
  change (∑ i,f (e i))= -1
  rw [Equiv.sum_comp e f,Fintype.sum_sum_type]
  simp [f,bitSign]

theorem isotropic_cube_atom_bound {d : ℕ}
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    ∀ x,w x≤1/((d+1 : ℕ) : ℝ) := by
  classical
  let A := augmentedSign (fun (x : Fin d → Bool) i => bitSign (x i))
  have hsign := augmentedSign_sign (fun (x : Fin d → Bool) i => bitSign (x i))
    (fun x i => bitSign_sign (x i))
  have hiso := augmentedSign_isotropic (fun (x : Fin d → Bool) i => bitSign (x i))
    w (fun x i => bitSign_sign (x i)) hmass hmean hpair
  let v : (Fin d → Bool) → Fin (d+1) → ℝ := fun x i => A x i
  have hnorm (x : Fin d → Bool) : (∑ i,v x i^2)=((d+1 : ℕ) : ℝ) := by
    have hs (i : Fin (d+1)) : v x i^2=1 := by
      change (A x i : ℝ)^2=1
      rcases hsign x i with h|h <;> norm_num [A,h]
    simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  apply atom_bound_of_moment (d+1) (by omega) w (inner v) hw
  · intro x
    simpa only [inner,← pow_two] using hnorm x
  · intro x
    rw [moment_of_coordinate_isotropy v w hiso x,hnorm x]

noncomputable def cubeMinEntropy {d : ℕ} (w : (Fin d → Bool) → ℝ) : ℝ :=
  -Real.log (Finset.univ.sup' Finset.univ_nonempty w)

theorem middle_slice_saturated_law (k : ℕ) (hk : 1≤k) :
    ∃ w : (Fin (2*k+1) → Bool) → ℝ,
      (∀ x,0≤w x) ∧ (∑ x,w x=1) ∧
      (∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0) ∧
      (∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) ∧
      w (fun _ => false)=1/((2*k+2 : ℕ) : ℝ) ∧ cubeMinEntropy w=Real.log (2*k+2) := by
  classical
  obtain ⟨w,hw,hm,hmean,hpair,hspecial⟩ :=
    saturated_orbit_law (by omega) (middleSliceSeed k) (middleSliceSeed_sum k)
  have hcap := isotropic_cube_atom_bound w hw hm hmean hpair
  have hN : (2*k+1)+1=2*k+2 := by omega
  have hspecial' : w (fun _ => false)=1/((2*k+2 : ℕ) : ℝ) := by
    rw [← hN,Nat.cast_add,Nat.cast_one]
    exact hspecial
  have hmax : Finset.univ.sup' Finset.univ_nonempty w=1/((2*k+2 : ℕ) : ℝ) := by
    apply le_antisymm
    · apply Finset.sup'_le _ w
      intro x _
      simpa only [hN] using hcap x
    · rw [← hspecial']
      exact Finset.le_sup' w (Finset.mem_univ _)
  refine ⟨w,hw,hm,hmean,hpair,hspecial',?_⟩
  unfold cubeMinEntropy
  rw [hmax]
  simp [one_div,Real.log_inv,Nat.cast_add,Nat.cast_mul]

theorem even_dimension_saturated_atom (n : ℕ) (hn : 4≤n) (heven : Even n) :
    ∃ w : (Fin (n-1) → Bool) → ℝ,
      (∀ x,0≤w x) ∧ (∑ x,w x=1) ∧
      (∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0) ∧
      (∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) ∧
      w (fun _ => false)=1/(n : ℝ) ∧ cubeMinEntropy w=Real.log (n : ℝ) := by
  obtain ⟨k,hk⟩ := heven
  have hform : ∃ a : ℕ,n=2*a+2 := ⟨k-1,by omega⟩
  obtain ⟨a,rfl⟩ := hform
  have hd : (2*a+2)-1=2*a+1 := by omega
  rw [hd]
  have hh := middle_slice_saturated_law a (by omega)
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh

theorem no_real_hadamard_order_six :
    ¬ ∃ H : Matrix (Fin 6) (Fin 6) ℝ,Matrix.IsHadamard H := by
  classical
  rintro ⟨H,hH⟩
  let B : Matrix (Fin 6) (Fin 6) ℤ := fun i j => if H i j=1 then 1 else -1
  have hsign (i j : Fin 6) : B i j=1 ∨ B i j= -1 := by
    dsimp [B]
    split_ifs <;> simp
  have hreal : (fun i j => (B i j : ℝ))=H := by
    ext i j
    have hh := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j)
    rcases hh with h|h <;> norm_num [B,h]
  let C : Matrix (Fin 6) (Fin 6) ℝ := fun i j => (B i j : ℝ)
  have hR : Matrix.IsHadamard C := by change Matrix.IsHadamard (fun i j => (B i j : ℝ)); rwa [hreal]
  have hB : Matrix.IsHadamard B := by
    apply Matrix.IsHadamard.of_mul_conjTranspose
    · intro i j
      exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hsign i j)
    · ext i j
      apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
      have hg : C*Cᵀ = (6 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Fintype.card_fin,Nat.cast_ofNat] using hR.mul_conjTranspose
      have hh := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M i j) hg
      simpa [C,Matrix.mul_apply,Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_apply,
        Matrix.smul_apply,Matrix.one_apply,Matrix.ofNat_apply,smul_eq_mul] using hh
    · apply isRegular_iff_ne_zero.mpr
      norm_num
  have hh := hB.four_dvd_card (by decide : 2<Fintype.card (Fin 6))
  norm_num at hh
end EntropyDesigns
