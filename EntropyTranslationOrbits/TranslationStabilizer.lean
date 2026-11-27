/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyTranslationOrbits.HadamardClosedQuadruple
@[expose] public section
namespace EntropyDesigns.TranslationOrbits

 theorem hadamard_sign_translation_stabilizer_trivial {J : Type*}
    [Fintype J] [DecidableEq J] (A : Matrix J J ℤ) (hA : A.IsHadamard)
    (hn : 4<Fintype.card J) (hmod : Fintype.card J%8=4)
    (w : J → ℤ) (hw : ∀ j,w j=1 ∨ w j= -1)
    (hstable : ∀ i,∃ k,∀ j,A k j=A i j*w j) : ∀ j,w j=1 := by
  classical
  by_contra hnontrivial
  have hi := hadamard_rows_injective A hA (by omega)
  have hp (i k : J) (hlink : ∀ j,A k j=A i j*w j) : i≠k := by
    intro he
    apply hnontrivial
    intro j
    have heq := hlink j
    rw [he] at heq
    obtain ha | ha := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem k j)
    · simpa [ha] using heq.symm
    · simp only [ha,neg_one_mul] at heq
      omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp (show 0<Fintype.card J by omega)
  obtain ⟨b,hb⟩ := hstable a
  have hab := hp a b hb
  have hsize : ({a,b}:Finset J).card<Finset.univ.card :=
    lt_of_le_of_lt Finset.card_le_two (by simpa using (show 2<Fintype.card J by omega))
  obtain ⟨c,_,hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  have hc' : c≠a ∧ c≠b := by simpa using hc
  obtain ⟨d,hd⟩ := hstable c
  have hcd := hp c d hd
  have hdback (j : J) : A c j=A d j*w j := by
    rw [hd]
    obtain h | h := hw j <;> simp [h]
  have had : a≠d := by
    intro he
    have heq : A c=A b := by
      funext j
      rw [hdback,←he,hb]
    exact hc'.2 (hi heq)
  have hbd : b≠d := by
    intro he
    have heq : A c=A a := by
      funext j
      rw [hdback,←he,hb]
      obtain h | h := hw j <;> simp [h]
    exact hc'.1 (hi heq)
  have hclosed (j : J) : A a j*A b j*A c j*A d j=1 := by
    rw [hb,hd]
    obtain ha | ha := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem a j)
    all_goals obtain hc | hc := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem c j)
    all_goals obtain hw | hw := hw j
    all_goals simp [ha,hc,hw]
  have hdvd := hadamard_closed_quadruple_eight_dvd A hA a b c d hab
    hc'.1.symm had hc'.2.symm hbd hcd hn 1 hclosed
  have hz := Nat.mod_eq_zero_of_dvd hdvd
  omega

end EntropyDesigns.TranslationOrbits
