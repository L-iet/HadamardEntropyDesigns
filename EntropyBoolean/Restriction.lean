/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean.Polynomial
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def binaryFunctionDotForm (ι : Type*) [Fintype ι] :
    LinearMap.BilinForm (ZMod 2) (ι → ZMod 2) := dotProductBilin (ZMod 2) (ZMod 2)

theorem binaryFunctionDotForm_nondegenerate (ι : Type*) [Fintype ι] :
    (binaryFunctionDotForm ι).Nondegenerate := by
  classical
  constructor <;> intro f hf <;> funext z <;>
    have hz := hf (Pi.single z 1) <;>
    simpa [binaryFunctionDotForm,dotProduct,Pi.single_apply] using hz

def binaryFunctionRestriction {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (ι → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2) where
  toFun f := fun z => f z.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def binaryFunctionZeroExtend {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : S → ZMod 2) (z : ι) : ZMod 2 :=
  if h : z∈S then f ⟨z,h⟩ else 0

theorem binaryFunctionZeroExtend_on {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : S → ZMod 2) (z : S) : binaryFunctionZeroExtend S f z=f z := by
  simp [binaryFunctionZeroExtend,z.property]

theorem binaryFunctionZeroExtend_dot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : S → ZMod 2) (g : ι → ZMod 2) :
    binaryFunctionDotForm ι g (binaryFunctionZeroExtend S f)=
      binaryFunctionDotForm S (binaryFunctionRestriction S g) f := by
  change (∑ z,g z*binaryFunctionZeroExtend S f z)=∑ z : S,g z.val*f z
  have heq := Finset.sum_subtype (F := inferInstance) S (fun _ => Iff.rfl)
    (fun z => g z*binaryFunctionZeroExtend S f z)
  simp only [binaryFunctionZeroExtend_on] at heq
  rw [←heq]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro z _ hz
  simp [binaryFunctionZeroExtend,hz]

theorem binaryFunctionRestriction_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (C : Submodule (ZMod 2) (ι → ZMod 2)) (f : S → ZMod 2) :
    f ∈ (binaryFunctionDotForm S).orthogonal (C.map (binaryFunctionRestriction S)) ↔
      binaryFunctionZeroExtend S f ∈ (binaryFunctionDotForm ι).orthogonal C := by
  constructor
  · intro h g hg
    rw [binaryFunctionZeroExtend_dot]
    exact h _ (Submodule.mem_map.mpr ⟨g,hg,rfl⟩)
  · intro h g hg
    obtain ⟨g,hg0,rfl⟩ := Submodule.mem_map.mp hg
    rw [←binaryFunctionZeroExtend_dot]
    exact h g hg0

theorem binaryFunctionRestriction_surjective_criterion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    (∀ f : S → ZMod 2, ∃ g∈C, binaryFunctionRestriction S g=f) ↔
      (∀ g∈(binaryFunctionDotForm ι).orthogonal C,
        (∀ z, z∉S → g z=0) → g=0) := by
  let D := C.map (binaryFunctionRestriction S)
  let B := binaryFunctionDotForm S
  have hB := binaryFunctionDotForm_nondegenerate S
  have hrefl : B.IsRefl := by
    intro f g h
    change (∑ z,g z*f z)=0
    change (∑ z,f z*g z)=0 at h
    simpa only [mul_comm] using h
  constructor
  · intro hext g hg hs
    funext z
    by_cases hz : z∈S
    · obtain ⟨f,hf,hfeq⟩ := hext (Pi.single ⟨z,hz⟩ 1)
      have hgz : binaryFunctionZeroExtend S (fun x : S => g x.val)=g := by
        funext x
        by_cases hx : x∈S <;> simp [binaryFunctionZeroExtend,hx,hs x]
      have hgg : binaryFunctionZeroExtend S (fun x : S => g x.val) ∈
          (binaryFunctionDotForm ι).orthogonal C := by rw [hgz]; exact hg
      have horth : (fun x : S => g x.val) ∈ B.orthogonal D :=
        (binaryFunctionRestriction_orthogonal S C _).mpr hgg
      have hh := horth _ (Submodule.mem_map.mpr ⟨f,hf,hfeq⟩)
      simpa [B,binaryFunctionDotForm,dotProduct,Pi.single_apply] using hh
    · exact hs z hz
  · intro hzero f
    have hbot : B.orthogonal D=⊥ := by
      apply le_antisymm
      · intro g hg
        have hz := hzero (binaryFunctionZeroExtend S g)
          ((binaryFunctionRestriction_orthogonal S C g).mp hg)
          (by intro z hz; simp [binaryFunctionZeroExtend,hz])
        change g=0
        funext z
        have hh := congrFun hz z.val
        simpa only [binaryFunctionZeroExtend_on,Pi.zero_apply] using hh
      · exact bot_le
    have htop : D=⊤ := by
      have hh := LinearMap.BilinForm.orthogonal_orthogonal hB hrefl D
      rw [hbot,LinearMap.BilinForm.orthogonal_bot] at hh
      exact hh.symm
    have hf : f∈D := by rw [htop]; trivial
    exact Submodule.mem_map.mp hf

theorem lowDegreeBooleanCode_extension_criterion {r d : ℕ} (hd : d<r)
    (S : Finset (Finset (Fin r))) :
    (∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode r d, binaryFunctionRestriction S g=f) ↔
      (∀ g∈lowDegreeBooleanCode r (r-d-1), (∀ z,z∉S → g z=0) → g=0) := by
  have hh := binaryFunctionRestriction_surjective_criterion S (lowDegreeBooleanCode r d)
  change _ ↔ (∀ g∈(booleanCubeDotForm r).orthogonal (lowDegreeBooleanCode r d),
    (∀ z,z∉S → g z=0) → g=0) at hh
  rwa [lowDegreeBooleanCode_duality hd] at hh

theorem lowDegreeBooleanCode_zero_constant {r : ℕ} (g : Finset (Fin r) → ZMod 2)
    (hg : g∈lowDegreeBooleanCode r 0) : ∃ a : ZMod 2, ∀ z,g z=a := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨s,rfl⟩ := hg
    have hs : s.val=∅ := Finset.card_eq_zero.mp (by have := s.property; omega)
    refine ⟨1,?_⟩
    intro z
    simp [hs,squarefreeBooleanMonomial]
  | zero => exact ⟨0,by intro z; rfl⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨a,ha⟩ := ihf
    obtain ⟨b,hb⟩ := ihg
    exact ⟨a+b,by intro z; simp [ha z,hb z]⟩
  | smul c f hf ih =>
    obtain ⟨a,ha⟩ := ih
    exact ⟨c*a,by intro z; simp [ha z,smul_eq_mul]⟩

theorem properBooleanSupport_degree_pred_extension {r : ℕ} (hr : 0<r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ) :
    ∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode r (r-1), binaryFunctionRestriction S g=f := by
  apply (lowDegreeBooleanCode_extension_criterion (r:=r) (d:=r-1) (by omega) S).mpr
  intro g hg hs
  have hd : r-(r-1)-1=0 := by omega
  rw [hd] at hg
  obtain ⟨a,ha⟩ := lowDegreeBooleanCode_zero_constant g hg
  have hex : ∃ z,z∉S := by
    by_contra! h
    exact hproper (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨z,hz⟩ := hex
  have haz : a=0 := (ha z).symm.trans (hs z hz)
  funext x
  simpa only [Pi.zero_apply,haz] using ha x

theorem four_bit_cubic_extension (S : Finset (Finset (Fin 4))) (hproper : S≠Finset.univ) :
    ∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode 4 3, binaryFunctionRestriction S g=f :=
  properBooleanSupport_degree_pred_extension (by omega) S hproper

end
end EntropyDesigns
