/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.BinaryRank
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators
noncomputable section

/-- Squarefree Boolean monomial, evaluated at the support of a Boolean vector. -/
def squarefreeBooleanMonomial {ι : Type*} [DecidableEq ι]
    (s z : Finset ι) : ZMod 2 := if s ⊆ z then 1 else 0

theorem squarefreeBooleanMonomial_mul {ι : Type*} [DecidableEq ι]
    (s t z : Finset ι) :
    squarefreeBooleanMonomial s z * squarefreeBooleanMonomial t z =
      squarefreeBooleanMonomial (s ∪ t) z := by
  by_cases hs : s ⊆ z <;> by_cases ht : t ⊆ z <;>
    simp [squarefreeBooleanMonomial,Finset.union_subset_iff,hs,ht]

def flipBooleanSupport {ι : Type*} [DecidableEq ι] (j : ι) (z : Finset ι) : Finset ι :=
  if j ∈ z then z.erase j else insert j z

theorem flipBooleanSupport_involutive {ι : Type*} [DecidableEq ι]
    (j : ι) (z : Finset ι) : flipBooleanSupport j (flipBooleanSupport j z)=z := by
  by_cases hj : j ∈ z <;> simp [flipBooleanSupport,hj]

theorem flipBooleanSupport_ne {ι : Type*} [DecidableEq ι]
    (j : ι) (z : Finset ι) : flipBooleanSupport j z ≠ z := by
  intro h
  have hh := congrArg (fun s : Finset ι => j ∈ s) h
  by_cases hj : j ∈ z <;> simp [flipBooleanSupport,hj] at hh

theorem squarefreeBooleanMonomial_flip {ι : Type*} [DecidableEq ι]
    (s z : Finset ι) (j : ι) (hj : j ∉ s) :
    squarefreeBooleanMonomial s (flipBooleanSupport j z)=squarefreeBooleanMonomial s z := by
  have hsub : s ⊆ flipBooleanSupport j z ↔ s ⊆ z := by
    constructor
    · intro h i hi
      have hij : i ≠ j := by intro he; subst i; exact hj hi
      have hh := h hi
      by_cases hz : j ∈ z <;> simpa [flipBooleanSupport,hz,hij] using hh
    · intro h i hi
      have hij : i ≠ j := by intro he; subst i; exact hj hi
      by_cases hz : j ∈ z <;> simp [flipBooleanSupport,hz,hij,h hi]
  simp only [squarefreeBooleanMonomial,hsub]

theorem squarefreeBooleanMonomial_sum_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (j : ι) (hj : j ∉ s) :
    (∑ z : Finset ι, squarefreeBooleanMonomial s z)=0 := by
  classical
  apply Finset.sum_ninvolution (flipBooleanSupport j)
  · intro z
    rw [squarefreeBooleanMonomial_flip s z j hj]
    have hh : ∀ a : ZMod 2, a+a=0 := by decide
    exact hh _
  · intro z _
    exact flipBooleanSupport_ne j z
  · intro z
    exact Finset.mem_univ _
  · exact flipBooleanSupport_involutive j

theorem squarefreeBooleanMonomial_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s t : Finset ι) (j : ι) (hj : j ∉ s ∪ t) :
    (∑ z : Finset ι, squarefreeBooleanMonomial s z * squarefreeBooleanMonomial t z)=0 := by
  simp_rw [squarefreeBooleanMonomial_mul]
  exact squarefreeBooleanMonomial_sum_zero (s ∪ t) j hj


theorem squarefreeBooleanMonomial_coefficients_unique {ι : Type*}
    [Fintype ι] [DecidableEq ι] (c : Finset ι → ZMod 2)
    (hc : ∀ z, (∑ s : Finset ι, c s * squarefreeBooleanMonomial s z)=0) :
    ∀ z, c z=0 := by
  intro z
  induction z using Finset.strongInductionOn with
  | _ z ih =>
    have heq : (∑ s : Finset ι, c s * squarefreeBooleanMonomial s z)=c z := by
      rw [Finset.sum_eq_single z]
      · simp [squarefreeBooleanMonomial]
      · intro t _ htz
        by_cases hsub : t ⊆ z
        · rw [ih t (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,htz⟩),zero_mul]
        · simp [squarefreeBooleanMonomial,hsub]
      · simp
    have hz := hc z
    rw [heq] at hz
    exact hz

theorem squarefreeBooleanMonomial_linearIndependent {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    LinearIndependent (ZMod 2) (fun s : Finset ι => squarefreeBooleanMonomial s) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  apply squarefreeBooleanMonomial_coefficients_unique c
  intro z
  have hz := congrFun hc z
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hz


theorem squarefreeBooleanMonomial_low_degree_orthogonal {r d e : ℕ}
    (hde : d+e<r) (s t : Finset (Fin r)) (hs : s.card≤d) (ht : t.card≤e) :
    (∑ z : Finset (Fin r), squarefreeBooleanMonomial s z * squarefreeBooleanMonomial t z)=0 := by
  have hmissing : ∃ j : Fin r, j ∉ s ∪ t := by
    by_contra! h
    have heq : s ∪ t=Finset.univ := Finset.eq_univ_iff_forall.mpr h
    have hc := Finset.card_union_le s t
    rw [heq,Finset.card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨j,hj⟩ := hmissing
  exact squarefreeBooleanMonomial_orthogonal s t j hj

/-- Concrete Reed--Muller code as the span of low-degree squarefree evaluations. -/
def lowDegreeBooleanCode (r d : ℕ) : Submodule (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun s : {s : Finset (Fin r) // s.card≤d} =>
    squarefreeBooleanMonomial s.val))

theorem lowDegreeBooleanCode_finrank (r d : ℕ) :
    Module.finrank (ZMod 2) (lowDegreeBooleanCode r d)=
      Fintype.card {s : Finset (Fin r) // s.card≤d} := by
  apply finrank_span_eq_card
  exact squarefreeBooleanMonomial_linearIndependent.comp Subtype.val Subtype.val_injective

def booleanCubeDotForm (r : ℕ) :
    LinearMap.BilinForm (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  dotProductBilin (ZMod 2) (ZMod 2)

theorem booleanCubeDotForm_apply (r : ℕ) (f g : Finset (Fin r) → ZMod 2) :
    booleanCubeDotForm r f g=∑ z, f z*g z := rfl

theorem lowDegreeBooleanCode_orthogonal_le {r d e : ℕ} (hde : d+e<r) :
    lowDegreeBooleanCode r e ≤ (booleanCubeDotForm r).orthogonal (lowDegreeBooleanCode r d) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,rfl⟩
  change ∀ f ∈ lowDegreeBooleanCode r d, booleanCubeDotForm r f (squarefreeBooleanMonomial t.val)=0
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,rfl⟩ := hf
    exact squarefreeBooleanMonomial_low_degree_orthogonal hde s.val t.val s.property t.property
  | zero => simp
  | add f g hf hg ihf ihg => simp [map_add,ihf,ihg]
  | smul a f hf ih => simp [map_smul,ih]

theorem booleanCubeDotForm_nondegenerate (r : ℕ) :
    (booleanCubeDotForm r).Nondegenerate := by
  constructor <;> intro f hf <;> funext z <;>
    have hz := hf (Pi.single z 1) <;>
    simpa [booleanCubeDotForm_apply,Pi.single_apply] using hz

def lowDegreeComplementEquiv (r d : ℕ) (hd : d<r) :
    {s : Finset (Fin r) // s.card≤r-d-1} ≃ {s : Finset (Fin r) // ¬s.card≤d} where
  toFun s := ⟨s.valᶜ,by
    have hc := Finset.card_le_univ s.val
    have hs := s.property
    simp only [Finset.card_compl,Fintype.card_fin] at *
    omega⟩
  invFun s := ⟨s.valᶜ,by
    have hc := Finset.card_le_univ s.val
    have hs := s.property
    simp only [Finset.card_compl,Fintype.card_fin] at *
    omega⟩
  left_inv s := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp

theorem lowDegreeBooleanCode_duality {r d : ℕ} (hd : d<r) :
    (booleanCubeDotForm r).orthogonal (lowDegreeBooleanCode r d)=
      lowDegreeBooleanCode r (r-d-1) := by
  have hle := lowDegreeBooleanCode_orthogonal_le (r:=r) (d:=d) (e:=r-d-1) (by omega)
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal (booleanCubeDotForm_nondegenerate r)]
  simp only [lowDegreeBooleanCode_finrank,Module.finrank_fintype_fun_eq_card]
  have hc := Fintype.card_congr (lowDegreeComplementEquiv r d hd)
  rw [Fintype.card_subtype_compl] at hc
  exact le_of_eq hc.symm

end
end EntropyDesigns
