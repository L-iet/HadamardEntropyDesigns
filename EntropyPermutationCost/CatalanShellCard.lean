/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
Catalan-shell constructions are prior work; see the project's paper attribution.
This file gives an original proof of their elementary count identities. -/
module
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace EntropyDesigns.PermutationCost

 theorem middle_shell_card_catalan (k : ℕ) :
    (2*k+1).choose (k+1)=(2*k+1)*catalan k := by
  rw [Nat.choose_symm_half]
  apply Nat.mul_right_cancel (show 0<k+1 by omega)
  have hh := Nat.choose_mul_succ_eq (2*k) k
  have he : 2*k+1-k=k+1 := by omega
  rw [he] at hh
  calc
    _=(2*k).choose k*(2*k+1) := hh.symm
    _=((2*k+1)*catalan k)*(k+1) := by
      rw [←Nat.centralBinom_eq_two_mul_choose,←succ_mul_catalan_eq_centralBinom]
      ring

 theorem catalan_shell_total (k : ℕ) :
    catalan k+(2*k+1).choose (k+1)=2*Nat.centralBinom k := by
  rw [middle_shell_card_catalan,←succ_mul_catalan_eq_centralBinom]
  ring

abbrev CatalanShellIndex (k : ℕ) :=
  Fin (catalan k) ⊕ {s : Finset (Fin (2*k+1)) // s.card=k+1}

 theorem catalan_shell_index_card (k : ℕ) :
    Fintype.card (CatalanShellIndex k)=2*Nat.centralBinom k := by
  simpa only [CatalanShellIndex,Fintype.card_sum,Fintype.card_fin,Fintype.card_finset_len]
    using catalan_shell_total k

 theorem catalan_shell_run_positive (k : ℕ) : 0<Fintype.card (CatalanShellIndex k) := by
  rw [catalan_shell_index_card]
  exact Nat.mul_pos (by decide) (Nat.centralBinom_pos k)

 theorem middle_shell_double_pair_count (k : ℕ) (hk : 1≤k) :
    2*(2*k-1).choose (k-1)=Nat.centralBinom k := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : 2*(1+j)-1=2*j+1 := by omega
  have h2 : 1+j-1=j := by omega
  rw [h1,h2,Nat.centralBinom_eq_two_mul_choose]
  have h3 : 2*(1+j)=2*j+1+1 := by omega
  rw [h3,Nat.add_comm 1 j,Nat.choose_succ_succ',Nat.choose_symm_half]
  ring

end EntropyDesigns.PermutationCost
