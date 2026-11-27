/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyTranslationOrbits.ClosedQuadruple
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace EntropyDesigns.TranslationOrbits
open scoped BigOperators

 theorem hadamard_rows_injective {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 0<Fintype.card J) :
    Function.Injective A := by
  intro i k he
  by_contra hik
  have ho : (∑ j,A i j*A k j)=0 := by
    simpa [Matrix.mul_apply,hik] using congr($hA.mul_conjTranspose i k)
  have hs (j : J) : A k j*A k j=1 := by
    obtain h | h := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem k j)
    all_goals simp [h]
  rw [he] at ho
  simp only [hs,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at ho
  have hz : Fintype.card J=0 := by exact_mod_cast ho
  omega

 theorem hadamard_closed_quadruple_eight_dvd {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard)
    (a b c d : J) (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (hn : 4<Fintype.card J) (γ : ℤ)
    (hc : ∀ j,A a j*A b j*A c j*A d j=γ) : 8∣Fintype.card J := by
  classical
  have hsize : ({a,b,c,d}:Finset J).card < Finset.univ.card :=
    lt_of_le_of_lt Finset.card_le_four (by simpa using hn)
  obtain ⟨z,_,hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  have hza : z≠a ∧ z≠b ∧ z≠c ∧ z≠d := by simpa using hz
  let f : Fin 5 → J := ![a,b,c,d,z]
  have hf : Function.Injective f := by
    intro i k he
    fin_cases i <;> fin_cases k <;> simp_all [f]
  apply closed_four_rows_force_eight_divisibility (fun i j => A (f i) j)
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem (f i) j)
  · intro i k hik
    have hne : f i≠f k := fun h => hik (hf h)
    simpa [Matrix.mul_apply,hne] using congr($hA.mul_conjTranspose (f i) (f k))
  · exact hc

end EntropyDesigns.TranslationOrbits
