/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupport.AffineSeparation
public import EntropySupport.RestrictionSurjective
public import EntropyCubic.LowerBounds
@[expose] public section
namespace EntropyDesigns
noncomputable section

theorem encoded_degree_sub_two_complement_spans {N r : ℕ}
    (hN : 4≤N) (hr : 4≤r) (hres : N%8=4)
    (labels : Fin N → Finset (Fin r)) (hinj : Function.Injective labels)
    (hproper : Finset.univ.image labels≠Finset.univ)
    (rows : Fin N → Fin (N-2) → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin (N-2) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i) :
    affineSpan (ZMod 2) (Set.range
      (fun z : {z : Finset (Fin r) // z∉Finset.univ.image labels} =>
        booleanSupportVector z.val))=⊤ := by
  classical
  apply (fixedSupport_degree_sub_two_extension_iff (by omega) _ hproper).mp
  intro v
  let w : Fin N → ZMod 2 := fun j => v ⟨labels j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨g,hg,he⟩ := residue_four_encoded_restriction_surjective hN hr hres labels hinj rows hOA f hf hmatch w
  refine ⟨g,hg,?_⟩
  funext z
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp z.property
  have h := congrFun he j
  change g (labels j)=w j at h
  simpa [binaryFunctionRestriction,w,hj] using h


theorem fixed_support_hadamard_degree_criterion {d r : ℕ}
    (hN : 4≤d+1) (hr : 4≤r) (hres : (d+1)%8=4)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1)
    (labels : Fin (d+1) → Finset (Fin r)) (hinj : Function.Injective labels)
    (hproper : Finset.univ.image labels≠Finset.univ) :
    (∃ f : Fin d → (Finset (Fin r) → ZMod 2),
      (∀ i,f i∈lowDegreeBooleanCode r (r-2)) ∧
      (∀ j i,booleanValueSign (f i (labels j))=H j i.succ)) ↔
    affineSpan (ZMod 2) (Set.range
      (fun z : {z : Finset (Fin r) // z∉Finset.univ.image labels} =>
        booleanSupportVector z.val))=⊤ := by
  classical
  let rows := integerHadamardTruthRows H
  have hOA : IsBinaryStrengthTwo rows := integerHadamardTruthRows_strength_two hH hzero
  constructor
  · rintro ⟨f,hf,hm⟩
    let e : Fin ((d+1)-2) ↪ Fin d := ⟨Fin.castLE (by omega),by
      intro i j h
      exact Fin.ext (congrArg (fun k : Fin d => k.val) h)⟩
    apply encoded_degree_sub_two_complement_spans hN hr hres labels hinj hproper
      (fun j i => rows j (e i)) (binary_strength_two_restrict rows hOA e)
      (fun i => f (e i)) (fun i => hf (e i))
    intro i j
    apply booleanValueSign_injective
    exact (hm j (e i)).trans (integerHadamardTruthRows_binary_value hH j (e i)).symm
  · intro hs
    let S := Finset.univ.image labels
    have hext := affineSpanningComplement_degree_sub_two_extension (by omega) S hs
    let v : Fin d → (S → ZMod 2) := fun i z =>
      binaryObservationMatrix rows (Function.invFun labels z.val) i
    choose f hf he using fun i => hext (v i)
    refine ⟨f,hf,?_⟩
    intro j i
    have hz : labels j∈S := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    have hh := congrFun (he i) ⟨labels j,hz⟩
    change f i (labels j)=binaryObservationMatrix rows (Function.invFun labels (labels j)) i at hh
    rw [Function.leftInverse_invFun hinj j] at hh
    rw [hh]
    exact integerHadamardTruthRows_binary_value hH j i


theorem fixed_support_pairwise_observables_criterion {d r : ℕ}
    (hN : 4≤d+1) (hr : 4≤r) (hres : (d+1)%8=4)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1)
    (labels : Fin (d+1) → Finset (Fin r)) (hinj : Function.Injective labels)
    (hproper : Finset.univ.image labels≠Finset.univ) :
    (∃ rows : Fin (d+1) → Fin d → Bool, IsBinaryStrengthTwo rows ∧
      ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
        (∀ i,f i∈lowDegreeBooleanCode r (r-2)) ∧
        (∀ i j,f i (labels j)=binaryObservationMatrix rows j i)) ↔
    affineSpan (ZMod 2) (Set.range
      (fun z : {z : Finset (Fin r) // z∉Finset.univ.image labels} =>
        booleanSupportVector z.val))=⊤ := by
  classical
  constructor
  · rintro ⟨rows,hOA,f,hf,hm⟩
    let e : Fin ((d+1)-2) ↪ Fin d := ⟨Fin.castLE (by omega),by
      intro i j h
      exact Fin.ext (congrArg (fun k : Fin d => k.val) h)⟩
    exact encoded_degree_sub_two_complement_spans hN hr hres labels hinj hproper
      (fun j i => rows j (e i)) (binary_strength_two_restrict rows hOA e)
      (fun i => f (e i)) (fun i => hf (e i)) (fun i j => hm (e i) j)
  · intro hs
    obtain ⟨f,hf,hm⟩ := (fixed_support_hadamard_degree_criterion hN hr hres H hH hzero
      labels hinj hproper).mpr hs
    refine ⟨integerHadamardTruthRows H,integerHadamardTruthRows_strength_two hH hzero,f,hf,?_⟩
    intro i j
    apply booleanValueSign_injective
    exact (hm j i).trans (integerHadamardTruthRows_binary_value hH j i).symm

end
end EntropyDesigns
