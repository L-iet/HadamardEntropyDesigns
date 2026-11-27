/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Character
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def realSignedCubeCharacter {r : ℕ} (ε : ℤ) (S : Finset (Fin r)) (x : Fin r → Bool) : ℝ :=
  (ε*walshChar S x : ℤ)

theorem signed_cube_character_complement_budget {r : ℕ} {ι : Type*} [Fintype ι]
    (S : Finset (Fin r → Bool)) (hS : S.Nonempty) (hproper : S≠Finset.univ)
    (ε : ι → ℤ) (T : ι → Finset (Fin r)) (hε : ∀ i,ε i=1 ∨ ε i= -1)
    (hortho : ∀ i j,i≠j →
      ∑ x∈S,realSignedCubeCharacter (ε i) (T i) x*realSignedCubeCharacter (ε j) (T j) x=0) :
    Fintype.card ι≤2^r-S.card := by
  classical
  have hdistinct (i j : ι) (hij : i≠j) : T i≠T j := by
    intro heq
    have h := hortho i j hij
    have hp (x : Fin r → Bool) :
        realSignedCubeCharacter (ε i) (T i) x*realSignedCubeCharacter (ε j) (T j) x=
          ((ε i*ε j : ℤ) : ℝ) := by
      rw [←heq]
      unfold realSignedCubeCharacter
      rw [←Int.cast_mul]
      congr 1
      calc
        (ε i*walshChar (T i) x)*(ε j*walshChar (T i) x)=
            (ε i*ε j)*(walshChar (T i) x)^2 := by ring
        _=ε i*ε j := by rw [walshChar_sq,mul_one]
    simp_rw [hp] at h
    rcases hε i with hi|hi <;> rcases hε j with hj|hj <;>
      simp [hi,hj] at h <;> norm_cast at h <;>
      exact (Finset.nonempty_iff_ne_empty.mp hS) h
  have hfull (i j : ι) (hij : i≠j) :
      (∑ x : Fin r → Bool,realSignedCubeCharacter (ε i) (T i) x*
        realSignedCubeCharacter (ε j) (T j) x)=0 := by
    have hw : (∑ x : Fin r → Bool,(walshChar (T i) x : ℝ)*(walshChar (T j) x : ℝ))=0 := by
      exact_mod_cast walshChar_cross_zero (T i) (T j) (hdistinct i j hij)
    calc
      _=(ε i : ℝ)*(ε j : ℝ)*∑ x : Fin r → Bool,
          (walshChar (T i) x : ℝ)*(walshChar (T j) x : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        simp only [realSignedCubeCharacter,Int.cast_mul]
        ring
      _=0 := by rw [hw,mul_zero]
  have hcomp (i j : ι) (hij : i≠j) :
      (∑ x∈Sᶜ,realSignedCubeCharacter (ε i) (T i) x*
        realSignedCubeCharacter (ε j) (T j) x)=0 := by
    have hh := Finset.sum_compl_add_sum S (fun x => realSignedCubeCharacter (ε i) (T i) x*
      realSignedCubeCharacter (ε j) (T j) x)
    rw [hortho i j hij,hfull i j hij,add_zero] at hh
    exact hh
  have hsq (i : ι) (x : Fin r → Bool) :
      realSignedCubeCharacter (ε i) (T i) x*realSignedCubeCharacter (ε i) (T i) x=1 := by
    rcases hε i with hi|hi <;> rcases walshChar_sign (T i) x with hx|hx <;>
      norm_num [realSignedCubeCharacter,hi,hx]
  have hCpos : 0<Sᶜ.card := by
    apply Finset.card_pos.mpr
    have hex : ∃ x,x∉S := by
      by_contra! h
      exact hproper (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨x,hx⟩ := hex
    exact ⟨x,Finset.mem_compl.mpr hx⟩
  let C : Finset (Fin r → Bool) := Sᶜ
  let B : LinearMap.BilinForm ℝ (C → ℝ) := dotProductBilin ℝ ℝ
  let v : ι → (C → ℝ) := fun i x => realSignedCubeCharacter (ε i) (T i) x.val
  have hv1 : B.iIsOrtho v := by
    intro i j hij
    change (∑ x : C,realSignedCubeCharacter (ε i) (T i) x.val*
      realSignedCubeCharacter (ε j) (T j) x.val)=0
    have hsum := Finset.sum_subtype (F := inferInstance) C (fun _ => Iff.rfl)
      (fun x => realSignedCubeCharacter (ε i) (T i) x*realSignedCubeCharacter (ε j) (T j) x)
    exact hsum.symm.trans (hcomp i j hij)
  have hv2 : ∀ i,B (v i) (v i)≠0 := by
    intro i
    have hh : B (v i) (v i)=(Sᶜ.card : ℝ) := by
      change (∑ x : C,realSignedCubeCharacter (ε i) (T i) x.val*
        realSignedCubeCharacter (ε i) (T i) x.val)=(Sᶜ.card : ℝ)
      simp_rw [hsq]
      simp [C]
    rw [hh]
    exact_mod_cast (Nat.ne_of_gt hCpos)
  have hLI := LinearMap.BilinForm.linearIndependent_of_iIsOrtho hv1 hv2
  have hc := hLI.fintype_card_le_finrank
  simpa only [C,Module.finrank_fintype_fun_eq_card,Fintype.card_coe,Finset.card_compl,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hc

end
end EntropyDesigns
