/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Encodings
public import EntropyCubic.LowerBounds
@[expose] public section
namespace EntropyDesigns

theorem sharp_cubic_seed_benchmarks :
    NoQuadraticHadamardSeedEncoding 11 4 ∧ NoQuadraticHadamardSeedEncoding 19 5 ∧
    IsExactCubicSeedBenchmark (d:=11) (r:=4) benchmarkHadamard12 benchmarkLabels12 benchmarkPolynomial12 3 ∧
    IsExactCubicSeedBenchmark (d:=19) (r:=5) benchmarkHadamard20 benchmarkLabels20 benchmarkPolynomial20 5 := by
  exact ⟨order_twelve_no_quadratic_hadamard_seed,order_twenty_no_quadratic_hadamard_seed,
    benchmark_order_12_cubic,benchmark_order_20_cubic⟩

end EntropyDesigns
