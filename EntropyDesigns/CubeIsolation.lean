/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.HammingWeight
public import EntropyDesigns.WalshCharacters
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.LinearAlgebra.Matrix.DotProduct
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns
open scoped Matrix

theorem binary_pair_table_sum {N d : ℕ} (rows : Fin N → Fin d → Bool)
    (i j : Fin d) (f : Bool → Bool → ℤ) :
    (∑ r,f (rows r i) (rows r j))=
      ((Finset.univ.filter (fun r => rows r i=false ∧ rows r j=false)).card : ℤ)*f false false+
      ((Finset.univ.filter (fun r => rows r i=false ∧ rows r j=true)).card : ℤ)*f false true+
      ((Finset.univ.filter (fun r => rows r i=true ∧ rows r j=false)).card : ℤ)*f true false+
      ((Finset.univ.filter (fun r => rows r i=true ∧ rows r j=true)).card : ℤ)*f true true := by
  classical
  have ht (r : Fin N) : f (rows r i) (rows r j)=
      (if rows r i=false ∧ rows r j=false then f false false else 0)+
      (if rows r i=false ∧ rows r j=true then f false true else 0)+
      (if rows r i=true ∧ rows r j=false then f true false else 0)+
      (if rows r i=true ∧ rows r j=true then f true true else 0) := by
    cases h1 : rows r i <;> cases h2 : rows r j <;> simp [h1,h2]
  simp_rw [ht]
  simp [Finset.sum_add_distrib,Finset.sum_ite,Finset.sum_const]

theorem strength_two_pair_moments {N d : ℕ} (rows : Fin N → Fin d → Bool)
    (hOA : IsBinaryStrengthTwo rows) (i j : Fin d) (hij : i≠j) :
    (∑ r,bitSign (rows r i))=0 ∧ (∑ r,bitSign (rows r i)*bitSign (rows r j))=0 := by
  classical
  have h00 : (4 : ℤ)*((Finset.univ.filter (fun r => rows r i=false ∧ rows r j=false)).card : ℤ)=N := by exact_mod_cast hOA i j hij false false
  have h01 : (4 : ℤ)*((Finset.univ.filter (fun r => rows r i=false ∧ rows r j=true)).card : ℤ)=N := by exact_mod_cast hOA i j hij false true
  have h10 : (4 : ℤ)*((Finset.univ.filter (fun r => rows r i=true ∧ rows r j=false)).card : ℤ)=N := by exact_mod_cast hOA i j hij true false
  have h11 : (4 : ℤ)*((Finset.univ.filter (fun r => rows r i=true ∧ rows r j=true)).card : ℤ)=N := by exact_mod_cast hOA i j hij true true
  have hfirst := binary_pair_table_sum rows i j (fun a _ => bitSign a)
  have hpair := binary_pair_table_sum rows i j (fun a b => bitSign a*bitSign b)
  simp only [show bitSign false=1 by rfl,show bitSign true= -1 by rfl,mul_one,mul_neg_one,one_mul,neg_one_mul,neg_neg] at hfirst hpair
  constructor <;> omega

theorem strength_two_all_moments {N d : ℕ} (hd : 2≤d) (rows : Fin N → Fin d → Bool)
    (hOA : IsBinaryStrengthTwo rows) :
    (∀ i,(∑ r,bitSign (rows r i))=0) ∧
      (∀ i j,i≠j → (∑ r,bitSign (rows r i)*bitSign (rows r j))=0) := by
  classical
  letI : Nontrivial (Fin d) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa only [Fintype.card_fin] using (show 1<d by omega))
  constructor
  · intro i
    obtain ⟨j,hj⟩ := exists_ne i
    exact (strength_two_pair_moments rows hOA i j hj.symm).1
  · intro i j hij
    exact (strength_two_pair_moments rows hOA i j hij).2


def integerAugmentedArray {d : ℕ} (rows : Fin (d+1) → Fin d → Bool) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℤ := fun r => Fin.cases 1 (fun i => bitSign (rows r i))

theorem integerAugmentedArray_sign {d : ℕ} (rows : Fin (d+1) → Fin d → Bool) (r j : Fin (d+1)) :
    integerAugmentedArray rows r j=1 ∨ integerAugmentedArray rows r j= -1 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [integerAugmentedArray]
  · exact bitSign_sign (rows r j)

theorem saturated_array_hadamard {d : ℕ} (rows : Fin (d+1) → Fin d → Bool)
    (hfirst : ∀ i,(∑ r,bitSign (rows r i))=0)
    (hpair : ∀ i j,i≠j → (∑ r,bitSign (rows r i)*bitSign (rows r j))=0) :
    Matrix.IsHadamard (integerAugmentedArray rows) := by
  let A := integerAugmentedArray rows
  have hcol : Aᵀ*A=((d+1 : ℕ) : ℤ) • 1 := by
    ext i j
    refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
    · simp [A,integerAugmentedArray,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]
    · simpa [A,integerAugmentedArray,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,show (0 : Fin (d+1)) ≠ j.succ from (Fin.succ_ne_zero j).symm] using hfirst j
    · simpa [A,integerAugmentedArray,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using hfirst i
    · by_cases h : i=j
      · subst j
        have hs (r : Fin (d+1)) : bitSign (rows r i)*bitSign (rows r i)=1 := by
          rcases bitSign_sign (rows r i) with h|h <;> rw [h] <;> norm_num
        simp [A,integerAugmentedArray,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,hs]
      · simpa [A,integerAugmentedArray,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,h] using hpair i j h
  have hAt : Matrix.IsHadamard Aᵀ := by
    apply Matrix.IsHadamard.of_mul_conjTranspose
    · intro i j
      exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (integerAugmentedArray_sign rows j i)
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose,Fintype.card_fin] using hcol
    · apply isRegular_iff_ne_zero.mpr
      simpa only [Fintype.card_fin] using (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d) : ((d+1 : ℕ) : ℤ) ≠ 0)
  simpa only [Matrix.transpose_transpose] using hAt.transpose

theorem two_flips_inner {d : ℕ} (x : Fin d → Bool) (i j : Fin d) (hij : i≠j) :
    (∑ k,(bitSign (x k))*(bitSign ((flipCoordinate i (flipCoordinate j x)) k)))=(d : ℤ)-4 := by
  classical
  have ht (k : Fin d) : bitSign (x k)*bitSign ((flipCoordinate i (flipCoordinate j x)) k)=
      1-2*(if k=i then 1 else 0)-2*(if k=j then 1 else 0) := by
    by_cases hki : k=i
    · subst k
      cases h : x i <;> simp [flipCoordinate,Function.update_of_ne hij,bitSign,h,hij]
    · by_cases hkj : k=j
      · subst k
        cases h : x j <;> simp [flipCoordinate,Function.update_of_ne hki,bitSign,h,hki]
      · cases h : x k <;> simp [flipCoordinate,Function.update_of_ne hki,Function.update_of_ne hkj,bitSign,h,hki,hkj]
  simp_rw [ht]
  simp [Finset.sum_sub_distrib,← Finset.mul_sum] <;> ring

theorem two_flips_ne {d : ℕ} (x : Fin d → Bool) (i j : Fin d) (hij : i≠j) :
    flipCoordinate i (flipCoordinate j x) ≠ x := by
  intro h
  have hi := congrFun h i
  have hh : !(x i)=x i := by simpa [flipCoordinate,Function.update_of_ne hij] using hi
  cases hxi : x i <;> simp [hxi] at hh

theorem saturated_array_no_two_flips {d : ℕ} (hd : 7≤d) (rows : Fin (d+1) → Fin d → Bool)
    (hfirst : ∀ i,(∑ r,bitSign (rows r i))=0)
    (hpair : ∀ i j,i≠j → (∑ r,bitSign (rows r i)*bitSign (rows r j))=0)
    (x : Fin d → Bool) (i j : Fin d) (hij : i≠j) :
    ¬ ((∃ r,rows r=x) ∧ ∃ s,rows s=flipCoordinate i (flipCoordinate j x)) := by
  rintro ⟨⟨r,hr⟩,s,hs⟩
  have hrs : r≠s := by
    intro h
    subst s
    exact two_flips_ne x i j hij (hs.symm.trans hr)
  have hH := saturated_array_hadamard rows hfirst hpair
  have hh := congrArg (fun M : Matrix (Fin (d+1)) (Fin (d+1)) ℤ => M r s) hH.mul_conjTranspose
  have hzero : (∑ k : Fin (d+1),integerAugmentedArray rows r k*integerAugmentedArray rows s k)=0 := by
    simpa [Matrix.mul_apply,Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,hrs] using hh
  have hi := two_flips_inner x i j hij
  have he : (∑ k : Fin (d+1),integerAugmentedArray rows r k*integerAugmentedArray rows s k)=
      1+(∑ k : Fin d,bitSign (x k)*bitSign ((flipCoordinate i (flipCoordinate j x)) k)) := by
    simp [Fin.sum_univ_succ,integerAugmentedArray,hr,hs]
  rw [he,hi] at hzero
  omega

def cubeOutside {d : ℕ} (T : Finset (Fin d)) (base x : Fin d → Bool) : Prop :=
  ∀ i,i∉T → x i=base i

noncomputable def coordinateCubeMove {d : ℕ} (T : Finset (Fin d)) (base x : Fin d → Bool) : ℤ := by
  classical
  exact if cubeOutside T base x then walshChar T x else 0

def arrayMultiplicity {N d : ℕ} (rows : Fin N → Fin d → Bool) (x : Fin d → Bool) : ℕ :=
  (Finset.univ.filter (fun r => rows r=x)).card

theorem outside_flip_free {d : ℕ} (T : Finset (Fin d)) (base x : Fin d → Bool)
    (i : Fin d) (hi : i∈T) (hx : cubeOutside T base x) :
    cubeOutside T base (flipCoordinate i x) := by
  intro k hk
  have hki : k≠i := by intro h; subst k; exact hk hi
  simpa [flipCoordinate,Function.update_of_ne hki] using hx k hk

theorem cube_parity_choice {d : ℕ} (T : Finset (Fin d)) (base : Fin d → Bool)
    (i : Fin d) (hi : i∈T) (δ : ℤ) (hδ : δ=1 ∨ δ= -1) :
    ∃ x : Fin d → Bool,cubeOutside T base x ∧ walshChar T x=δ := by
  have hbase : cubeOutside T base base := fun _ _ => rfl
  by_cases h : walshChar T base=δ
  · exact ⟨base,hbase,h⟩
  · refine ⟨flipCoordinate i base,outside_flip_free T base base i hi hbase,?_⟩
    rw [walshChar_flip T i hi]
    rcases walshChar_sign T base with hε|hε <;> rcases hδ with hδ|hδ <;> omega

theorem arrayMultiplicity_absent {N d : ℕ} (rows : Fin N → Fin d → Bool) (x : Fin d → Bool)
    (hx : ¬ ∃ r,rows r=x) : arrayMultiplicity rows x=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro r _ hr
  exact hx ⟨r,hr⟩

theorem coordinate_cube_moves_frozen {d : ℕ} (hd : 7≤d)
    (rows : Fin (d+1) → Fin d → Bool)
    (hfirst : ∀ i,(∑ r,bitSign (rows r i))=0)
    (hpair : ∀ i j,i≠j → (∑ r,bitSign (rows r i)*bitSign (rows r j))=0)
    (T : Finset (Fin d)) (hT : 3≤T.card) (base : Fin d → Bool) (z : ℤ) (hz : z≠0) :
    ∃ x : Fin d → Bool,(arrayMultiplicity rows x : ℤ)+z*coordinateCubeMove T base x<0 := by
  classical
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1<T.card)
  let δ : ℤ := if 0<z then -1 else 1
  have hδ : δ=1 ∨ δ= -1 := by dsimp [δ]; split_ifs <;> simp
  have hneg : z*δ<0 := by dsimp [δ]; split_ifs <;> omega
  obtain ⟨u,hout,hpar⟩ := cube_parity_choice T base i hi δ hδ
  let v := flipCoordinate i (flipCoordinate j u)
  have hvout : cubeOutside T base v :=
    outside_flip_free T base _ i hi (outside_flip_free T base u j hj hout)
  have hvpar : walshChar T v=δ := by
    dsimp [v]
    rw [walshChar_flip T i hi,walshChar_flip T j hj,hpar,neg_neg]
  have hno := saturated_array_no_two_flips hd rows hfirst hpair u i j hij
  have hfinish (x : Fin d → Bool) (hx : ¬ ∃ r,rows r=x)
      (hxout : cubeOutside T base x) (hxpar : walshChar T x=δ) :
      (arrayMultiplicity rows x : ℤ)+z*coordinateCubeMove T base x<0 := by
    rw [arrayMultiplicity_absent rows x hx]
    simp only [Nat.cast_zero,zero_add,coordinateCubeMove,if_pos hxout,hxpar]
    exact hneg
  by_cases hu : ∃ r,rows r=u
  · refine ⟨v,hfinish v ?_ hvout hvpar⟩
    intro hv
    exact hno ⟨hu,hv⟩
  · exact ⟨u,hfinish u hu hout hpar⟩

theorem saturated_coordinate_cube_isolation {d : ℕ} (hd : 7≤d)
    (rows : Fin (d+1) → Fin d → Bool) (hOA : IsBinaryStrengthTwo rows)
    (T : Finset (Fin d)) (hT : 3≤T.card) (base : Fin d → Bool) (z : ℤ) (hz : z≠0) :
    ∃ x : Fin d → Bool,(arrayMultiplicity rows x : ℤ)+z*coordinateCubeMove T base x<0 := by
  obtain ⟨hf,hp⟩ := strength_two_all_moments (by omega) rows hOA
  exact coordinate_cube_moves_frozen hd rows hf hp T hT base z hz
end EntropyDesigns
