/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.RadicalDimension
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

theorem binary_even_gram_rank_bound {ι : Type*} [Fintype ι] {m : ℕ}
    (heven : m%2=0) (W : Submodule (ZMod 2) (ι → ZMod 2))
    (v : Fin m → W)
    (hgram : ∀ i j,binaryFunctionDotForm ι (v i).val (v j).val=
      ((if i=j then 1 else 0) : ZMod 2)+1) :
    m≤binaryBilinearRank W := by
  classical
  let R := Submodule.span (ZMod 2) (Set.range (fun x : W => fun y : W => ∑ i,x.val i*y.val i))
  let F : Fin m → (W → ZMod 2) := fun i y => binaryFunctionDotForm ι (v i).val y.val
  have hi : LinearIndependent (ZMod 2) F := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let S : ZMod 2 := ∑ i,c i
    have hchar : ∀ a : ZMod 2,a+a=0 := by decide
    have hci : ∀ j,c j=S := by
      intro j
      have hz := congrArg (fun L : W → ZMod 2 => L (v j)) hc
      have he : (∑ i,c i*binaryFunctionDotForm ι (v i).val (v j).val)=0 := by
        simpa only [F,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hz
      simp_rw [hgram,mul_add,Finset.sum_add_distrib] at he
      have hs : (∑ i,c i*(if i=j then (1 : ZMod 2) else 0))=c j := by simp
      rw [hs] at he
      simp only [mul_one] at he
      change c j+S=0 at he
      linear_combination he-hchar S
    have hS : S=0 := by
      have hm : (m : ZMod 2)=0 := (ZMod.natCast_eq_natCast_iff' m 0 2).mpr heven
      calc
        S=∑ _ : Fin m,S := by apply Finset.sum_congr rfl; intro i _; exact hci i
        _=0 := by simp [hm]
    intro i
    exact (hci i).trans hS
  let G : Fin m → R := fun i => ⟨F i,Submodule.subset_span ⟨v i,rfl⟩⟩
  have hG : LinearIndependent (ZMod 2) G := by
    apply LinearIndependent.of_comp R.subtype
    exact hi
  have hc := hG.fintype_card_le_finrank
  change m≤Module.finrank (ZMod 2) R
  simpa only [Fintype.card_fin] using hc

end
end EntropyDesigns
