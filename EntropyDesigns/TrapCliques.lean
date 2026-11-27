module

public import EntropyDesigns.TrapRows
public import Mathlib.Data.Fintype.EquivFin

/-! # Sharp cardinality and graph structure of orthogonal trap subsets -/

@[expose] public section
namespace EntropyDesigns

def trapOrthogonal {s : ℕ} (e : Finset (Fin s))
    (S : Finset ((Fin s → Bool) × (Fin s → Bool))) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → trapInner e u v = 0

theorem trap_clique_first_injective {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (S : Finset ((Fin s → Bool) × (Fin s → Bool))) (hS : trapOrthogonal e S) :
    Function.Injective (fun u : S => u.val.1) := by
  intro u v huv
  apply Subtype.ext
  by_contra hne
  have hzero := hS u.val u.property v.val v.property hne
  exact ((trapInner_zero_iff hs e _ _).mp hzero).1 huv

theorem trap_clique_second_injective {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (S : Finset ((Fin s → Bool) × (Fin s → Bool))) (hS : trapOrthogonal e S) :
    Function.Injective (fun u : S => u.val.2) := by
  intro u v huv
  apply Subtype.ext
  by_contra hne
  have hzero := hS u.val u.property v.val v.property hne
  exact ((trapInner_zero_iff hs e _ _).mp hzero).2.1 huv

theorem trap_clique_card_le {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (S : Finset ((Fin s → Bool) × (Fin s → Bool))) (hS : trapOrthogonal e S) :
    S.card ≤ 2 ^ s := by
  have h := Fintype.card_le_of_injective _ (trap_clique_first_injective hs e S hS)
  simpa using h

theorem trapMixed_diagonal {s : ℕ} (e : Finset (Fin s)) (a : Fin s → Bool) :
    trapMixed e (a, a) = 1 := by
  simpa [trapMixed, pow_two] using walshChar_sq e a

theorem trap_maximum_clique_exists {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) :
    ∃ S : Finset ((Fin s → Bool) × (Fin s → Bool)), trapOrthogonal e S ∧ S.card = 2 ^ s := by
  classical
  let S := Finset.univ.image (fun a : Fin s → Bool => (a, a))
  refine ⟨S, ?_, ?_⟩
  · intro u hu v hv hne
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
    have hab : a ≠ b := by intro h; exact hne (by rw [h])
    exact (trapInner_zero_iff hs e _ _).mpr
      ⟨hab, hab, by rw [trapMixed_diagonal, trapMixed_diagonal]⟩
  · rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
    simp

theorem maximum_trap_clique_graph {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (S : Finset ((Fin s → Bool) × (Fin s → Bool))) (hS : trapOrthogonal e S)
    (hcard : S.card = 2 ^ s) :
    ∃ (π : (Fin s → Bool) ≃ (Fin s → Bool)) (c : ℤ), (c = 1 ∨ c = -1) ∧
      (∀ u ∈ S, u.2 = π u.1) ∧ (∀ a, (a, π a) ∈ S) ∧
      (∀ u ∈ S, trapMixed e u = c) := by
  classical
  have hcard' : Fintype.card S = Fintype.card (Fin s → Bool) := by simpa using hcard
  let ea : S ≃ (Fin s → Bool) := Equiv.ofBijective (fun u : S => u.val.1)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨trap_clique_first_injective hs e S hS, hcard'⟩)
  let eb : S ≃ (Fin s → Bool) := Equiv.ofBijective (fun u : S => u.val.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨trap_clique_second_injective hs e S hS, hcard'⟩)
  let π := ea.symm.trans eb
  have hpair : ∀ a, (ea.symm a).val = (a, π a) := by
    intro a
    apply Prod.ext
    · exact ea.apply_symm_apply a
    · rfl
  have hmem : ∀ a, (a, π a) ∈ S := by
    intro a
    rw [← hpair a]
    exact (ea.symm a).property
  let u₀ := (ea.symm (fun _ => false)).val
  let c := trapMixed e u₀
  have hu₀ : u₀ ∈ S := (ea.symm (fun _ => false)).property
  refine ⟨π, c, trapMixed_sign e u₀, ?_, hmem, ?_⟩
  · intro u hu
    have h := congrArg Prod.snd (hpair u.1)
    have hea : ea.symm u.1 = (⟨u, hu⟩ : S) := by
      apply ea.injective
      exact ea.apply_symm_apply u.1
    simpa [hea] using h
  · intro u hu
    by_cases h : u = u₀
    · exact congrArg (trapMixed e) h
    · exact ((trapInner_zero_iff hs e _ _).mp (hS u hu u₀ hu₀ h)).2.2

end EntropyDesigns
