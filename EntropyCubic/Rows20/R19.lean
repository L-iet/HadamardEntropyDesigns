/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Data
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem benchmarkHadamard20_row19 : ∀ j : Fin 20,
 (∑ k,benchmarkHadamard20 (19 : Fin 20) k*benchmarkHadamard20 j k)=
 if (19 : Fin 20)=j then (20 : ℤ) else 0 := by
 intro j
 fin_cases j <;> norm_num [benchmarkHadamard20,bitHadamardSign,benchmarkRowMask20,Fin.sum_univ_succ,Nat.testBit]

end EntropyDesigns
