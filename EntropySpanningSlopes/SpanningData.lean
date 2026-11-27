/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.SpanningSets
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section

theorem spanning_seed_dimension {k s : ℕ} (hk : 2≤k) (hkh : k<2^s) :
    2≤s ∧ s≠0 := by
  have hs2 : 2≤s := by
    by_contra hn
    have hcases : s=0 ∨ s=1 := by omega
    rcases hcases with h0|h1
    · rw [h0] at hkh
      norm_num at hkh
      omega
    · rw [h1] at hkh
      norm_num at hkh
      omega
  exact ⟨hs2,by omega⟩

theorem spanning_slope_data_exists {k s : ℕ} (hs : s≠0)
    (hsu : s≤2^s-k) (hsmall : 2^s-k<2^s/2) (i0 : Fin k) :
    k<2^s ∧ ∃ R : Finset (GaloisField 2 s),∃ t : Fin k → GaloisField 2 s,
      Function.Injective t ∧ t i0=0 ∧ R.card=2^s-k ∧ 0∉R ∧
      Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤ ∧
      (∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a) := by
  classical
  have hspos : 0<s := Nat.pos_of_ne_zero hs
  have hkh : k<2^s := by
    by_contra hn
    have hz : 2^s-k=0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz] at hsu
    omega
  have hu : 2^s-k<2^s := lt_of_lt_of_le hsmall (Nat.div_le_self _ _)
  obtain ⟨R,hRcard,hRzero,hRspan⟩ := exists_nonzero_spanning_finset hs hsu hu
  let K := GaloisField 2 s
  letI : Fintype K := Fintype.ofFinite K
  let P : Finset K := Finset.univ\R
  have hKcard : Fintype.card K=2^s := by
    simpa only [Nat.card_eq_fintype_card] using GaloisField.card (p:=2) (n:=s) hs
  have hPcard : P.card=k := by
    dsimp only [P]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R),Finset.card_univ,hKcard,hRcard]
    omega
  have hzeroP : (0:K)∈P := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hRzero⟩
  obtain ⟨t,ht,hzero,himage⟩ := enumerate_finset_with_anchor P hPcard 0 hzeroP i0
  refine ⟨hkh,R,t,ht,hzero,hRcard,hRzero,hRspan,?_⟩
  intro a
  rw [himage a]
  simp [P]

end
end EntropyDesigns.SpanningSlopes
