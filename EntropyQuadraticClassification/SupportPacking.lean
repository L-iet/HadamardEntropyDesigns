/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Every twelve-coordinate support has a faithful bounded integer encoding. -/
module
public import EntropyQuadraticClassification.EncodedParityGraph
public import Init.Data.BitVec.Lemmas
public import Init.Data.List.OfFn
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

def packedSupport (s : Finset (Fin 12)) : ℕ :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 12 => decide (i∈s)))).toNat

theorem packedSupport_lt (s : Finset (Fin 12)) : packedSupport s<4096 := by
  have h := (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 12 => decide (i∈s)))).isLt
  simpa [packedSupport] using h

theorem encodedSupport_packedSupport (s : Finset (Fin 12)) :
    encodedSupport (packedSupport s)=s := by
  ext i
  simp only [encodedSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    packedSupport,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt,
    Option.getD_some,decide_eq_true_eq]

end EntropyDesigns.QuadraticRefinement
