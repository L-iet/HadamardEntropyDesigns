/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySeedRepair.BasisSubset
public import EntropySupport.Saturation
public import Mathlib.Basic.Real.Basic
@[expose] public section
namespace EntropyDesigns.SupportRepair
noncomputable section
open scoped BigOperators

def uniformSupportTruthLaw {α δ : Type*} [DecidableEq α] [DecidableEq δ]
    (S : Finset α) (rows : α → δ) (v : δ) : ℝ :=
  ∑ z∈S,if rows z=v then 1/(S.card : ℝ) else 0

theorem truth_law_congr_on_support {α δ : Type*} [DecidableEq α] [DecidableEq δ]
    (S : Finset α) (rows newRows : α → δ) (h : ∀ z∈S,rows z=newRows z) :
    uniformSupportTruthLaw S rows=uniformSupportTruthLaw S newRows := by
  funext v
  apply Finset.sum_congr rfl
  intro z hz
  rw [h z hz]

theorem truth_law_reindex {α δ : Type*} [DecidableEq α] [DecidableEq δ]
    (S : Finset α) (e : α ≃ α) (rows : α → δ) :
    uniformSupportTruthLaw (S.map e.toEmbedding) (fun z => rows (e.symm z))=
      uniformSupportTruthLaw S rows := by
  funext v
  simp [uniformSupportTruthLaw]

theorem swap_support_image {α : Type*} [DecidableEq α]
    (S : Finset α) (a b : α) (ha : a∉S) (hb : b∈S) :
    S.map (Equiv.swap a b).toEmbedding=insert a (S.erase b) := by
  classical
  have hab : a≠b := by intro h; apply ha; simpa [h] using hb
  ext x
  rw [Finset.mem_map_equiv]
  simp only [Equiv.symm_swap]
  by_cases hxa : x=a
  · subst x
    simp [hb]
  · by_cases hxb : x=b
    · subst x
      simp [ha,hab,Ne.symm hab]
    · simp [Equiv.swap_apply_of_ne_of_ne hxa hxb,hxa,hxb]

theorem one_exchange_truth_law_preserved {α δ : Type*} [DecidableEq α] [DecidableEq δ]
    (S : Finset α) (a b : α) (ha : a∉S) (hb : b∈S) (rows : α → δ) :
    uniformSupportTruthLaw (insert a (S.erase b)) (fun z => rows (Equiv.swap a b z))=
      uniformSupportTruthLaw S rows := by
  have h := truth_law_reindex S (Equiv.swap a b) rows
  rw [swap_support_image S a b ha hb] at h
  simpa only [Equiv.symm_swap] using h

theorem one_exchange_truth_values {α δ : Type*} [DecidableEq α]
    (a b : α) (rows : α → δ) :
    rows (Equiv.swap a b a)=rows b ∧
      ∀ z,z≠a → z≠b → rows (Equiv.swap a b z)=rows z := by
  constructor
  · simp
  · intro z hza hzb
    rw [Equiv.swap_apply_of_ne_of_ne hza hzb]

theorem proper_support_truth_extension {r d : ℕ} (hr : 0<r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ)
    (rows : (Finset (Fin r)) → Fin d → Bool) :
    ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
      (∀ i,f i∈lowDegreeBooleanCode r (r-1)) ∧
      (∀ i z,z∈S → f i z=if rows z i then 1 else 0) := by
  classical
  have hext := properBooleanSupport_degree_pred_extension hr S hproper
  choose f hf he using fun i : Fin d => hext (fun z : S => if rows z.val i then 1 else 0)
  refine ⟨f,hf,?_⟩
  intro i z hz
  exact congrFun (he i) ⟨z,hz⟩

theorem spanning_complement_truth_extension {r d : ℕ} (hr : 2≤r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ)
    (hspan : affineSpan (ZMod 2) (Set.range (fun z : {z : Finset (Fin r) // z∉S} =>
      booleanSupportVector z.val))=⊤)
    (rows : (Finset (Fin r)) → Fin d → Bool) :
    ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
      (∀ i,f i∈lowDegreeBooleanCode r (r-2)) ∧
      (∀ i z,z∈S → f i z=if rows z i then 1 else 0) := by
  classical
  have hext := (fixedSupport_degree_sub_two_extension_iff hr S hproper).mpr hspan
  choose f hf he using fun i : Fin d => hext (fun z : S => if rows z.val i then 1 else 0)
  refine ⟨f,hf,?_⟩
  intro i z hz
  exact congrFun (he i) ⟨z,hz⟩

end
end EntropyDesigns.SupportRepair
