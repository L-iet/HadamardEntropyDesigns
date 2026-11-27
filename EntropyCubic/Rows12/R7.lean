/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Data
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem benchmarkHadamard12_row7 : ∀ j : Fin 12,
 (∑ k,benchmarkHadamard12 (7 : Fin 12) k*benchmarkHadamard12 j k)=
 if (7 : Fin 12)=j then (12 : ℤ) else 0 := by
 intro j
 fin_cases j <;> norm_num [benchmarkHadamard12,bitHadamardSign,benchmarkRowMask12,Fin.sum_univ_succ,Nat.testBit]

end EntropyDesigns
