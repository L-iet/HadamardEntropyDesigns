/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.SupportOverlap
public import EntropyDesigns.BinaryObservables
public import Mathlib.Data.Nat.Bitwise
@[expose] public section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns

def initialMask (r : ℕ) {d : ℕ} (i : Fin d) : Finset (Fin r) :=
  Finset.univ.filter (fun j => (i.val+1).testBit j.val=true)

theorem initialMask_nonempty {r d : ℕ} (hmax : d<2^r) (i : Fin d) :
    (initialMask r i).Nonempty := by
  classical
  by_contra h
  have hempty : initialMask r i=∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hz : i.val+1=0 := Nat.zero_of_testBit_eq_false (fun k => by
    by_cases hk : k<r
    · have hm : (⟨k,hk⟩ : Fin r)∉initialMask r i := by rw [hempty]; simp
      have hne : (i.val+1).testBit k ≠ true := by
        simpa only [initialMask,Finset.mem_filter,Finset.mem_univ,true_and] using hm
      cases hh : (i.val+1).testBit k <;> simp_all
    · apply Nat.testBit_eq_false_of_lt
      have hpow : 2^r≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
      omega)
  omega

theorem initialMask_injective {r d : ℕ} (hmax : d<2^r) : Function.Injective (@initialMask r d) := by
  intro i j h
  have he : i.val+1=j.val+1 := Nat.eq_of_testBit_eq (fun k => by
    by_cases hk : k<r
    · have hm := Finset.ext_iff.mp h (⟨k,hk⟩ : Fin r)
      have hiff : (i.val+1).testBit k=true ↔ (j.val+1).testBit k=true := by
        simpa only [initialMask,Finset.mem_filter,Finset.mem_univ,true_and] using hm
      cases h1 : (i.val+1).testBit k <;> cases h2 : (j.val+1).testBit k <;> simp_all
    · have hpow : 2^r≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
      have h1 : (i.val+1).testBit k=false := Nat.testBit_eq_false_of_lt (by omega)
      have h2 : (j.val+1).testBit k=false := Nat.testBit_eq_false_of_lt (by omega)
      rw [h1,h2])
  apply Fin.ext
  omega

theorem initialMask_singleton {r d : ℕ} (hhalf : 2^(r-1)≤d) (j : Fin r) :
    ∃ i : Fin d,initialMask r i={j} := by
  have hp : 0<2^j.val := Nat.pow_pos (by decide)
  have hle : 2^j.val≤d := (Nat.pow_le_pow_right (by decide) (show j.val≤r-1 by omega)).trans hhalf
  let i : Fin d := ⟨2^j.val-1,by omega⟩
  have hi : i.val+1=2^j.val := by dsimp [i]; omega
  refine ⟨i,?_⟩
  ext k
  simp [initialMask,hi,Nat.testBit_two_pow,Fin.ext_iff,eq_comm]

def initialCharacterCode {r : ℕ} (d : ℕ) (x : Fin r → Bool) : Fin d → Bool :=
  fun i => decide (walshChar (initialMask r i) x= -1)

theorem initialCharacterCode_sign {r : ℕ} (d : ℕ) (x : Fin r → Bool) (i : Fin d) :
    bitSign (initialCharacterCode d x i)=walshChar (initialMask r i) x := by
  rcases walshChar_sign (initialMask r i) x with h|h <;>
    norm_num [initialCharacterCode,bitSign,h]

theorem initialCharacterCode_injective {r d : ℕ} (hhalf : 2^(r-1)≤d) :
    Function.Injective (@initialCharacterCode r d) := by
  intro x y h
  funext j
  obtain ⟨i,hi⟩ := initialMask_singleton hhalf j
  have hh := congrArg bitSign (congrFun h i)
  rw [initialCharacterCode_sign,initialCharacterCode_sign,hi] at hh
  have he : bitSign (x j)=bitSign (y j) := by simpa [walshChar] using hh
  cases hx : x j <;> cases hy : y j <;> simp_all [bitSign]

def initialMaskLinear {r : ℕ} (d : ℕ) : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
  LinearMap.pi (fun i : Fin d => maskFunctional (initialMask r i))

theorem initialCharacterCode_binary {r : ℕ} (d : ℕ) (x : Fin r → Bool) :
    binarySeed (initialCharacterCode d x)=initialMaskLinear d (binarySeed x) := by
  funext i
  rcases binaryField_cases (maskFunctional (initialMask r i) (binarySeed x)) with h|h <;>
    norm_num [binarySeed,initialCharacterCode,initialMaskLinear,walshChar_binaryFunctional,h]

theorem initialCharacterCode_in_range {r : ℕ} (d : ℕ) (x : Fin r → Bool) :
    binarySeed (initialCharacterCode d x)∈LinearMap.range (initialMaskLinear (r := r) d) := by
  exact ⟨binarySeed x,(initialCharacterCode_binary d x).symm⟩

theorem initialMaskLinear_range_dimension {r : ℕ} (d : ℕ) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (initialMaskLinear (r := r) d))≤r := by
  have hh := LinearMap.finrank_range_le (initialMaskLinear (r := r) d)
  simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin,mul_one] using hh

noncomputable def walshSubsetLaw {r : ℕ} (d : ℕ) (A : Finset (Fin r → Bool)) :
    (Fin d → Bool) → ℝ := pushLaw (initialCharacterCode d) (uniformFiniteLaw A)

theorem uniformFiniteLaw_collision {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (hA : 0<A.card) : collision (uniformFiniteLaw A)=1/(A.card : ℝ) := by
  unfold collision
  have ht (x : α) : uniformFiniteLaw A x^2=(1/(A.card : ℝ))*uniformFiniteLaw A x := by
    by_cases hx : x∈A <;> simp [uniformFiniteLaw,hx] <;> ring
  simp_rw [ht]
  rw [← Finset.mul_sum,uniformFiniteLaw_mass A hA,mul_one]

theorem walshSubsetLaw_collision {r d : ℕ} (hhalf : 2^(r-1)≤d)
    (A : Finset (Fin r → Bool)) (hA : 0<A.card) :
    collision (walshSubsetLaw d A)=1/(A.card : ℝ) := by
  rw [walshSubsetLaw,pushLaw_injective_collision _ (initialCharacterCode_injective hhalf)]
  exact uniformFiniteLaw_collision A hA

theorem finite_sign_subset_sum_bound {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (hf : ∀ x,|f x|≤1) (hsum : ∑ x,f x=0) (A : Finset α) :
    |∑ x∈A,f x|≤(Fintype.card α : ℝ)-(A.card : ℝ) := by
  have hh : (∑ x∈A,f x)+(∑ x∈Aᶜ,f x)=0 := by rw [Finset.sum_add_sum_compl,hsum]
  have he : (∑ x∈A,f x)= -(∑ x∈Aᶜ,f x) := by linarith
  have hb : |∑ x∈Aᶜ,f x|≤((Aᶜ).card : ℝ) := by
    calc
      _ ≤ ∑ x∈Aᶜ,|f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x∈Aᶜ,(1 : ℝ) := Finset.sum_le_sum (fun x _ => hf x)
      _ = _ := by simp
  have hc : ((Aᶜ).card : ℝ)=(Fintype.card α : ℝ)-(A.card : ℝ) := by
    rw [Finset.card_compl,Nat.cast_sub (Finset.card_le_univ A)]
  rw [he,abs_neg]
  exact hb.trans_eq hc

theorem uniformFiniteLaw_expectation {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (f : α → ℝ) :
    (∑ x,uniformFiniteLaw A x*f x)=(1/(A.card : ℝ))*(∑ x∈A,f x) := by
  have hfilter : Finset.univ.filter (fun x : α => x∈A)=A := by ext x; simp
  simp [uniformFiniteLaw,ite_mul,Finset.sum_ite,hfilter,Finset.mul_sum]

theorem uniformFiniteLaw_moment_bound {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (f : α → ℝ) (hf : ∀ x,|f x|≤1) (hsum : ∑ x,f x=0) :
    |∑ x,uniformFiniteLaw A x*f x|≤((Fintype.card α : ℝ)-(A.card : ℝ))/(A.card : ℝ) := by
  rw [uniformFiniteLaw_expectation,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤1/(A.card : ℝ))]
  calc
    _ ≤ (1/(A.card : ℝ))*((Fintype.card α : ℝ)-(A.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_sign_subset_sum_bound f hf hsum A) (by positivity)
    _ = _ := by ring

theorem bitSign_real_abs (b : Bool) : |(bitSign b : ℝ)|=1 := by cases b <;> norm_num [bitSign]

theorem walshSubsetLaw_first_error {r d : ℕ} (hmax : d<2^r)
    (A : Finset (Fin r → Bool)) (i : Fin d) :
    |∑ y,walshSubsetLaw d A y*(bitSign (y i) : ℝ)|≤
      ((2 : ℝ)^r-(A.card : ℝ))/(A.card : ℝ) := by
  rw [walshSubsetLaw,pushLaw_moment]
  have hz : (∑ x : Fin r → Bool,(bitSign (initialCharacterCode d x i) : ℝ))=0 := by
    simp_rw [initialCharacterCode_sign]
    exact walshChar_real_sum_zero _ (initialMask_nonempty hmax i)
  have hh := uniformFiniteLaw_moment_bound A (fun x => (bitSign (initialCharacterCode d x i) : ℝ))
    (fun x => (bitSign_real_abs _).le) hz
  simpa using hh

theorem walshSubsetLaw_pair_error {r d : ℕ} (hmax : d<2^r)
    (A : Finset (Fin r → Bool)) (i j : Fin d) (hij : i≠j) :
    |∑ y,walshSubsetLaw d A y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ)|≤
      ((2 : ℝ)^r-(A.card : ℝ))/(A.card : ℝ) := by
  have heq := pushLaw_moment (initialCharacterCode d) (uniformFiniteLaw A)
    (fun y => (bitSign (y i) : ℝ)*(bitSign (y j) : ℝ))
  have hne : initialMask r i≠initialMask r j := fun h => hij (initialMask_injective hmax h)
  have hz : (∑ x : Fin r → Bool,(bitSign (initialCharacterCode d x i) : ℝ)*(bitSign (initialCharacterCode d x j) : ℝ))=0 := by
    simp_rw [initialCharacterCode_sign]
    simpa only [if_neg hne] using walshChar_real_orthogonality (initialMask r i) (initialMask r j)
  have hab (x : Fin r → Bool) : |(bitSign (initialCharacterCode d x i) : ℝ)*(bitSign (initialCharacterCode d x j) : ℝ)|≤1 := by
    rw [abs_mul,bitSign_real_abs,bitSign_real_abs]
    norm_num
  have hh := uniformFiniteLaw_moment_bound A
    (fun x => (bitSign (initialCharacterCode d x i) : ℝ)*(bitSign (initialCharacterCode d x j) : ℝ)) hab hz
  have hr : (∑ y,walshSubsetLaw d A y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ))=
      ∑ x,uniformFiniteLaw A x*((bitSign (initialCharacterCode d x i) : ℝ)*(bitSign (initialCharacterCode d x j) : ℝ)) := by
    simpa only [walshSubsetLaw,mul_assoc] using heq
  rw [hr]
  simpa using hh

theorem push_uniformFiniteLaw_image {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (A : Finset α) :
    pushLaw f (uniformFiniteLaw A)=uniformFiniteLaw (A.image f) := by
  classical
  ext b
  have hc : (A.image f).card=A.card := Finset.card_image_of_injective A hf
  by_cases h : ∃ a∈A,f a=b
  · obtain ⟨a,ha,rfl⟩ := h
    rw [pushLaw_injective_value f hf]
    simp [uniformFiniteLaw,ha,Finset.mem_image_of_mem f ha,hc]
  · have hb : b∉A.image f := by simpa only [Finset.mem_image] using h
    rw [uniformFiniteLaw,if_neg hb]
    unfold pushLaw
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a∈A
    · have hne : f a≠b := fun he => h ⟨a,ha,he⟩
      rw [if_neg hne]
    · simp [uniformFiniteLaw,ha]

theorem activeSupport_uniformFiniteLaw {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (hA : 0<A.card) : activeSupport (uniformFiniteLaw A)=A := by
  have hn : (A.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : A.card ≠ 0)
  ext x
  by_cases hx : x∈A <;> simp [activeSupport,uniformFiniteLaw,hx,hn]

theorem uniformFiniteLaw_subset_variation {α : Type*} [Fintype α] [DecidableEq α]
    (S T : Finset α) (hST : S⊆T) (hS : 0<S.card) :
    totalVariation (uniformFiniteLaw S) (uniformFiniteLaw T)=1-(S.card : ℝ)/(T.card : ℝ) := by
  have hT : 0<T.card := hS.trans_le (Finset.card_le_card hST)
  have hSR : (0 : ℝ)<S.card := by exact_mod_cast hS
  have hTR : (0 : ℝ)<T.card := by exact_mod_cast hT
  have hcard : (S.card : ℝ)≤T.card := by exact_mod_cast Finset.card_le_card hST
  have hone : 1/(T.card : ℝ)≤1/(S.card : ℝ) :=
    (div_le_div_iff₀ hTR hSR).mpr (by simpa using hcard)
  have hdiff : (0 : ℝ)≤1/(S.card : ℝ)-1/(T.card : ℝ) := sub_nonneg.mpr hone
  have hc : (0 : ℝ)≤1/(T.card : ℝ) := by positivity
  have ht (x : α) : |uniformFiniteLaw S x-uniformFiniteLaw T x|=
      uniformFiniteLaw S x+uniformFiniteLaw T x-2*(if x∈S then 1/(T.card : ℝ) else 0) := by
    by_cases hs : x∈S
    · have hxT := hST hs
      simp only [uniformFiniteLaw,if_pos hs,if_pos hxT]
      rw [abs_of_nonneg hdiff]
      ring
    · by_cases hxT : x∈T <;> simp [uniformFiniteLaw,hs,hxT,abs_of_nonneg hc]
  have hfilter : Finset.univ.filter (fun x : α => x∈S)=S := by ext x; simp
  unfold totalVariation
  simp_rw [ht]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,uniformFiniteLaw_mass S hS,
    uniformFiniteLaw_mass T hT,← Finset.mul_sum]
  simp only [Finset.sum_ite,Finset.sum_const,nsmul_eq_mul,hfilter]
  ring

theorem walshSubsetLaw_uniform {r d : ℕ} (hhalf : 2^(r-1)≤d) (A : Finset (Fin r → Bool)) :
    walshSubsetLaw d A=uniformFiniteLaw (A.image (initialCharacterCode d)) :=
  push_uniformFiniteLaw_image _ (initialCharacterCode_injective hhalf) A

theorem walshSubsetLaw_support {r d : ℕ} (hhalf : 2^(r-1)≤d)
    (A : Finset (Fin r → Bool)) (hA : 0<A.card) :
    activeSupport (walshSubsetLaw d A)=A.image (initialCharacterCode d) := by
  rw [walshSubsetLaw_uniform hhalf]
  exact activeSupport_uniformFiniteLaw _ (by rwa [Finset.card_image_of_injective _ (initialCharacterCode_injective hhalf)])

theorem walshSubsetLaw_full_variation {r d : ℕ} (hhalf : 2^(r-1)≤d)
    (A : Finset (Fin r → Bool)) (hA : 0<A.card) :
    totalVariation (walshSubsetLaw d A) (walshSubsetLaw (r := r) d Finset.univ)=
      1-(A.card : ℝ)/(2 : ℝ)^r := by
  rw [walshSubsetLaw_uniform hhalf,walshSubsetLaw_uniform hhalf]
  have hsub : A.image (initialCharacterCode d)⊆Finset.univ.image (initialCharacterCode d) :=
    Finset.image_mono (initialCharacterCode d) (Finset.subset_univ A)
  have hh := uniformFiniteLaw_subset_variation _ _ hsub (by rwa [Finset.card_image_of_injective _ (initialCharacterCode_injective hhalf)])
  rw [Finset.card_image_of_injective A (initialCharacterCode_injective hhalf),
    Finset.card_image_of_injective Finset.univ (initialCharacterCode_injective hhalf)] at hh
  simpa using hh

theorem walsh_subset_candidate_full {r N : ℕ} (hN : 12≤N) (hres : N%8=4)
    (hNL : N≤2^r) (hhalf : 2^r/2≤N-4)
    (A : Finset (Fin r → Bool)) (hA : A.card=N) :
    (∀ y,0≤walshSubsetLaw (N-4) A y) ∧
    (∑ y,walshSubsetLaw (N-4) A y)=1 ∧
    (activeSupport (walshSubsetLaw (N-4) A)).card=N ∧
    collision (walshSubsetLaw (N-4) A)=1/(N : ℝ) ∧
    (∀ i,|∑ y,walshSubsetLaw (N-4) A y*(bitSign (y i) : ℝ)|≤((2 : ℝ)^r-(N : ℝ))/(N : ℝ)) ∧
    (∀ i j,i≠j → |∑ y,walshSubsetLaw (N-4) A y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ)|≤((2 : ℝ)^r-(N : ℝ))/(N : ℝ)) ∧
    totalVariation (walshSubsetLaw (N-4) A) (walshSubsetLaw (r := r) (N-4) Finset.univ)=1-(N : ℝ)/(2 : ℝ)^r ∧
    collision (walshSubsetLaw (r := r) (N-4) Finset.univ)=1/(2 : ℝ)^r ∧
    (∀ y,0≤walshSubsetLaw (r := r) (N-4) Finset.univ y) ∧
    (∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y)=1 ∧
    (∀ i,(∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y*(bitSign (y i) : ℝ))=0) ∧
    (∀ i j,i≠j → (∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ))=0) ∧
    ∀ q : (Fin (N-4) → Bool) → ℝ,(∀ y,0≤q y) → (∑ y,q y=1) →
      (∀ i,∑ y,q y*(bitSign (y i) : ℝ)=0) →
      (∀ i j,i≠j → ∑ y,q y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ)=0) →
      (activeSupport q).card≤N →
      1-((r+4 : ℕ) : ℝ)/(N : ℝ)≤totalVariation (walshSubsetLaw (N-4) A) q := by
  classical
  have hmax : N-4<2^r := by omega
  have hhalf' : 2^(r-1)≤N-4 := by
    cases r with
    | zero => norm_num at hNL; omega
    | succ s => simpa [pow_succ] using hhalf
  have hApos : 0<A.card := by omega
  have hUpos : 0<(Finset.univ : Finset (Fin r → Bool)).card :=
    Finset.card_pos.mpr ⟨fun _ => false,Finset.mem_univ _⟩
  have hPnonneg : ∀ y,0≤walshSubsetLaw (N-4) A y :=
    pushLaw_nonneg _ _ (uniformFiniteLaw_nonneg A)
  have hPmass : (∑ y,walshSubsetLaw (N-4) A y)=1 := by
    rw [walshSubsetLaw,pushLaw_mass]
    exact uniformFiniteLaw_mass A hApos
  have hPcard : (activeSupport (walshSubsetLaw (N-4) A)).card=N := by
    rw [walshSubsetLaw_support hhalf' A hApos,Finset.card_image_of_injective _ (initialCharacterCode_injective hhalf'),hA]
  have hPcollision : collision (walshSubsetLaw (N-4) A)=1/(N : ℝ) := by
    simpa only [hA] using walshSubsetLaw_collision hhalf' A hApos
  have hPfirst (i : Fin (N-4)) := walshSubsetLaw_first_error hmax A i
  have hPpair (i j : Fin (N-4)) (hij : i≠j) := walshSubsetLaw_pair_error hmax A i j hij
  have hPU : totalVariation (walshSubsetLaw (N-4) A) (walshSubsetLaw (r := r) (N-4) Finset.univ)=1-(N : ℝ)/(2 : ℝ)^r := by
    simpa only [hA] using walshSubsetLaw_full_variation hhalf' A hApos
  have hUC : collision (walshSubsetLaw (r := r) (N-4) Finset.univ)=1/(2 : ℝ)^r := by
    simpa using walshSubsetLaw_collision hhalf' Finset.univ hUpos
  have hUnonneg : ∀ y,0≤walshSubsetLaw (r := r) (N-4) Finset.univ y :=
    pushLaw_nonneg _ _ (uniformFiniteLaw_nonneg Finset.univ)
  have hUmass : (∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y)=1 := by
    rw [walshSubsetLaw,pushLaw_mass]
    exact uniformFiniteLaw_mass Finset.univ hUpos
  have hUfirst (i : Fin (N-4)) : (∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y*(bitSign (y i) : ℝ))=0 := by
    have hh := walshSubsetLaw_first_error hmax Finset.univ i
    have hz : |∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y*(bitSign (y i) : ℝ)|≤0 := by simpa using hh
    exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  have hUpair (i j : Fin (N-4)) (hij : i≠j) : (∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ))=0 := by
    have hh := walshSubsetLaw_pair_error hmax Finset.univ i j hij
    have hz : |∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ)|≤0 := by simpa using hh
    exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  refine ⟨hPnonneg,hPmass,hPcard,hPcollision,?_,?_,hPU,hUC,hUnonneg,hUmass,hUfirst,hUpair,?_⟩
  · intro i
    simpa only [hA] using hPfirst i
  · intro i j hij
    simpa only [hA] using hPpair i j hij
  · intro q hq hm hmean hpair hcard
    let C := LinearMap.range (initialMaskLinear (r := r) (N-4))
    let S := A.image (initialCharacterCode (N-4))
    have hC : Module.finrank (ZMod 2) C≤r := initialMaskLinear_range_dimension (N-4)
    have hS : S.card=N := by rw [Finset.card_image_of_injective _ (initialCharacterCode_injective hhalf'),hA]
    have hSC (y : Fin (N-4) → Bool) (hy : y∈S) : binarySeed y∈C := by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact initialCharacterCode_in_range (N-4) x
    have hh := minimal_support_code_rigidity hN hres C hC S hS hSC q hq hm hmean hpair hcard
    rw [walshSubsetLaw_uniform hhalf']
    exact hh.2.1
end EntropyDesigns
