/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCompleteSequence.UniformEntropy
public import Mathlib.Data.Finset.Lattice.Fold
@[expose] public section
namespace EntropyDesigns.RelativeSequence
open scoped BigOperators
noncomputable section

def renyiEntropy {A : Type*} [Fintype A] (w : A → ℝ) (α : ℝ) : ℝ :=
  if α = 1 then shannon w else renyiOffOne w α

def maxWeight {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty w

def minEntropy {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ) : ℝ :=
  -Real.log (maxWeight w)

theorem renyi_all_lower {A : Type*} [Fintype A] (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1)
    (N α : ℝ) (hN : 0 < N) (hα : 0 < α) (hcap : ∀ x, w x ≤ 1/N) :
    Real.log N ≤ renyiEntropy w α := by
  by_cases h : α = 1
  · rw [renyiEntropy, if_pos h]
    exact (log_entropy_of_collision_cap w hw hmass hN
      (collision_le_of_atom_bound w (1/N) hw hmass hcap)).2
  · rw [renyiEntropy, if_neg h]
    exact renyi_lower_of_atom_cap w hw hmass N α hN hα h hcap

theorem renyi_all_uniform {A : Type*} [Fintype A] (w : A → ℝ)
    (N α : ℝ) (hN : 0 < N) (hα : 0 < α) (hmass : ∑ x, w x = 1)
    (huniform : ∀ x, w x = 0 ∨ w x = 1/N) : renyiEntropy w α = Real.log N := by
  by_cases h : α = 1
  · rw [renyiEntropy, if_pos h]
    exact uniform_shannon w N hN hmass huniform
  · rw [renyiEntropy, if_neg h]
    exact uniform_renyi w N α hN hα h hmass huniform

theorem maxWeight_pos {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ)
    (hmass : ∑ x, w x = 1) : 0 < maxWeight w := by
  classical
  obtain ⟨x,hx⟩ : ∃ x, 0 < w x := by
    by_contra hn
    push_neg at hn
    have hh := Finset.sum_nonpos (fun x (_ : x ∈ (Finset.univ : Finset A)) => hn x)
    linarith
  exact hx.trans_le (Finset.le_sup' w (Finset.mem_univ x))

theorem minEntropy_lower {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ)
    (hmass : ∑ x, w x = 1) (N : ℝ) (hN : 0 < N)
    (hcap : ∀ x, w x ≤ 1/N) : Real.log N ≤ minEntropy w := by
  have hm : maxWeight w ≤ 1/N := Finset.sup'_le _ _ (fun x _ => hcap x)
  have hh := Real.log_le_log (maxWeight_pos w hmass) hm
  simp only [one_div, Real.log_inv] at hh
  dsimp [minEntropy]
  linarith

theorem maxWeight_uniform {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ)
    (N : ℝ) (hN : 0 < N) (hmass : ∑ x, w x = 1)
    (huniform : ∀ x, w x = 0 ∨ w x = 1/N) : maxWeight w = 1/N := by
  classical
  have hc : 0 ≤ 1/N := (one_div_pos.mpr hN).le
  have hle : maxWeight w ≤ 1/N := Finset.sup'_le _ _ (fun x _ => by
    rcases huniform x with h | h <;> rw [h]
    exact hc)
  obtain ⟨x,hx⟩ : ∃ x, w x ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hz : ∑ x, w x = 0 := Finset.sum_eq_zero (fun x _ => hn x)
    linarith
  have he := (huniform x).resolve_left hx
  have hge : 1/N ≤ maxWeight w := he ▸ Finset.le_sup' w (Finset.mem_univ x)
  exact le_antisymm hle hge

theorem minEntropy_uniform {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ)
    (N : ℝ) (hN : 0 < N) (hmass : ∑ x, w x = 1)
    (huniform : ∀ x, w x = 0 ∨ w x = 1/N) : minEntropy w = Real.log N := by
  rw [minEntropy, maxWeight_uniform w N hN hmass huniform]
  simp only [one_div, Real.log_inv, neg_neg]

end
end EntropyDesigns.RelativeSequence
