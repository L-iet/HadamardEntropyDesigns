/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch108
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6272 : Finset ℕ := ([1594,1628,1642,1678,1708,1720,1738,2650,2668,2716,2730,3132,3150,3162,3192,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6272 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6272 5 (fun x => (if x<2716 then (if x<1708 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 1 else 0)) else (if x<1738 then (if x<1720 then 1 else 2) else (if x<2650 then 2 else (if x<2668 then 1 else 1)))) else (if x<3162 then (if x<3132 then (if x<2730 then 1 else 0) else (if x<3150 then 2 else 2)) else (if x<3228 then (if x<3192 then 3 else 4) else (if x<3242 then 3 else (if x<3276 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6273 : Finset ℕ := ([1594,1642,1678,1708,2650,2716,3132,3150,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6273 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6273 4 (fun x => (if x<2650 then (if x<1678 then (if x<1642 then 0 else 1) else (if x<1708 then 0 else 1)) else (if x<3132 then (if x<2716 then 1 else 1) else (if x<3150 then 2 else (if x<3242 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6274 : Finset ℕ := ([1594,1628,1642,1678,1708,1720,1738,2650,2668,2716,2730,2776,3132,3150,3162,3192,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6274 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6274 2776 4
  · have he : independentCachedBranchMembers6274.erase 2776=independentCachedBranchMembers6272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6272
  · have he : independentCachedBranchMembers6274.filter (independentCachedEdge 2776)=independentCachedBranchMembers6273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6273
def independentCachedBranchMembers6275 : Finset ℕ := ([1594,1708,2650,2668,3132,3150,3192,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6275 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6275 4 (fun x => (if x<3132 then (if x<2650 then (if x<1708 then 0 else 0) else (if x<2668 then 0 else 1)) else (if x<3192 then (if x<3150 then 1 else 1) else (if x<3228 then 2 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6276 : Finset ℕ := ([1594,1628,1642,1678,1708,1720,1738,2638,2650,2668,2716,2730,2776,3132,3150,3162,3192,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6276 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6276 2638 4
  · have he : independentCachedBranchMembers6276.erase 2638=independentCachedBranchMembers6274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6274
  · have he : independentCachedBranchMembers6276.filter (independentCachedEdge 2638)=independentCachedBranchMembers6275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6275
def independentCachedBranchMembers6277 : Finset ℕ := ([1642,1678,2668,2716,3132,3150,3162,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6277 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6277 4 (fun x => (if x<3132 then (if x<2668 then (if x<1678 then 0 else 0) else (if x<2716 then 1 else 0)) else (if x<3162 then (if x<3150 then 1 else 1) else (if x<3242 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6278 : Finset ℕ := ([1594,1628,1642,1678,1708,1720,1738,2620,2638,2650,2668,2716,2730,2776,3132,3150,3162,3192,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6278 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6278 2620 4
  · have he : independentCachedBranchMembers6278.erase 2620=independentCachedBranchMembers6276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6276
  · have he : independentCachedBranchMembers6278.filter (independentCachedEdge 2620)=independentCachedBranchMembers6277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6277
def independentCachedBranchMembers6279 : Finset ℕ := ([1594,1678,1720,1738,2620,2638,3132,3150,3192,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6279 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6279 4 (fun x => (if x<2638 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<1738 then 1 else (if x<2620 then 1 else 1))) else (if x<3150 then (if x<3132 then 1 else 2) else (if x<3192 then 2 else (if x<3276 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6280 : Finset ℕ := ([1594,1628,1642,1678,1690,1708,1720,1738,2620,2638,2650,2668,2716,2730,2776,3132,3150,3162,3192,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6280 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6280 1690 4
  · have he : independentCachedBranchMembers6280.erase 1690=independentCachedBranchMembers6278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6278
  · have he : independentCachedBranchMembers6280.filter (independentCachedEdge 1690)=independentCachedBranchMembers6279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6279
def independentCachedBranchMembers6281 : Finset ℕ := ([1594,1642,1678,1708,2650,2716,3162,3192,3228,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6281 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6281 4 (fun x => (if x<2716 then (if x<1678 then (if x<1642 then 0 else 1) else (if x<1708 then 0 else (if x<2650 then 1 else 1))) else (if x<3192 then (if x<3162 then 1 else 2) else (if x<3228 then 0 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6282 : Finset ℕ := ([1582,1594,1628,1642,1678,1690,1708,1720,1738,2620,2638,2650,2668,2716,2730,2776,3132,3150,3162,3192,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6282 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6282 1582 4
  · have he : independentCachedBranchMembers6282.erase 1582=independentCachedBranchMembers6280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6280
  · have he : independentCachedBranchMembers6282.filter (independentCachedEdge 1582)=independentCachedBranchMembers6281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6281
def independentCachedBranchMembers6283 : Finset ℕ := ([1642,1708,1720,1738,2620,2638,2650,2716,3132,3150,3162,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6283 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6283 4 (fun x => (if x<2650 then (if x<1738 then (if x<1708 then 0 else (if x<1720 then 0 else 1)) else (if x<2620 then 1 else (if x<2638 then 1 else 1))) else (if x<3150 then (if x<2716 then 0 else (if x<3132 then 0 else 2)) else (if x<3162 then 2 else (if x<3228 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6284 : Finset ℕ := ([1582,1594,1628,1642,1678,1690,1708,1720,1738,1768,2620,2638,2650,2668,2716,2730,2776,3132,3150,3162,3192,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6284 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6284 1768 4
  · have he : independentCachedBranchMembers6284.erase 1768=independentCachedBranchMembers6282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6282
  · have he : independentCachedBranchMembers6284.filter (independentCachedEdge 1768)=independentCachedBranchMembers6283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6283
def independentCachedBranchMembers6285 : Finset ℕ := ([1582,1594,1642,1678,1690,1738,2638,2650,2730,3150,3162,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6285 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6285 4 (fun x => (if x<2638 then (if x<1678 then (if x<1594 then 0 else (if x<1642 then 1 else 2)) else (if x<1690 then 1 else (if x<1738 then 0 else 3))) else (if x<3150 then (if x<2650 then 2 else (if x<2730 then 3 else 0)) else (if x<3162 then 3 else (if x<3242 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6286 : Finset ℕ := ([252,1582,1594,1628,1642,1678,1690,1708,1720,1738,1768,2620,2638,2650,2668,2716,2730,2776,3132,3150,3162,3192,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6286 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6286 252 4
  · have he : independentCachedBranchMembers6286.erase 252=independentCachedBranchMembers6284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6284
  · have he : independentCachedBranchMembers6286.filter (independentCachedEdge 252)=independentCachedBranchMembers6285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6285
def independentCachedBranchMembers6287 : Finset ℕ := ([1582,1594,1678,1690,1708,1720,2620,2716,2730,3132,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6287 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6287 4 (fun x => (if x<2620 then (if x<1690 then (if x<1594 then 0 else (if x<1678 then 1 else 1)) else (if x<1708 then 0 else (if x<1720 then 2 else 3))) else (if x<3132 then (if x<2716 then 2 else (if x<2730 then 3 else 0)) else (if x<3228 then 3 else (if x<3242 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6288 : Finset ℕ := ([72,252,1582,1594,1628,1642,1678,1690,1708,1720,1738,1768,2620,2638,2650,2668,2716,2730,2776,3132,3150,3162,3192,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6288 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6288 72 4
  · have he : independentCachedBranchMembers6288.erase 72=independentCachedBranchMembers6286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6286
  · have he : independentCachedBranchMembers6288.filter (independentCachedEdge 72)=independentCachedBranchMembers6287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6287
def independentCachedBranchMembers6289 : Finset ℕ := ([48,72,132,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6289 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6289 246 5
  · have he : independentCachedBranchMembers6289.erase 246=independentCachedBranchMembers6271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6271
  · have he : independentCachedBranchMembers6289.filter (independentCachedEdge 246)=independentCachedBranchMembers6288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6288
def independentCachedBranchMembers6290 : Finset ℕ := ([1594,1622,1628,1652,1702,1708,1738,1762,1768,2614,2620,2650,2674,2730,2758,2788,3126,3132,3162,3192,3242,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6290 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6290 5 (fun x => (if x<2650 then (if x<1708 then (if x<1628 then (if x<1622 then 0 else 0) else (if x<1652 then 1 else (if x<1702 then 2 else 0))) else (if x<1768 then (if x<1738 then 1 else (if x<1762 then 0 else 2)) else (if x<2614 then 3 else (if x<2620 then 0 else 1)))) else (if x<3132 then (if x<2758 then (if x<2674 then 0 else (if x<2730 then 2 else 0)) else (if x<2788 then 0 else (if x<3126 then 2 else 3))) else (if x<3242 then (if x<3162 then 4 else (if x<3192 then 4 else 3)) else (if x<3276 then 3 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6291 : Finset ℕ := ([1652,1702,1708,1738,2614,2620,2650,2788,3126,3132,3162,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6291 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6291 4 (fun x => (if x<2650 then (if x<1738 then (if x<1702 then 0 else (if x<1708 then 0 else 1)) else (if x<2614 then 1 else (if x<2620 then 0 else 1))) else (if x<3132 then (if x<2788 then 1 else (if x<3126 then 0 else 2)) else (if x<3162 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6292 : Finset ℕ := ([1594,1622,1628,1652,1678,1702,1708,1738,1762,1768,2614,2620,2650,2674,2730,2758,2788,3126,3132,3162,3192,3242,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6292 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6292 1678 4
  · have he : independentCachedBranchMembers6292.erase 1678=independentCachedBranchMembers6290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6290
  · have he : independentCachedBranchMembers6292.filter (independentCachedEdge 1678)=independentCachedBranchMembers6291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6291
def independentCachedBranchMembers6293 : Finset ℕ := ([1628,1652,1738,1762,1768,2614,2620,2730,3126,3132,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6293 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6293 4 (fun x => (if x<2614 then (if x<1738 then (if x<1652 then 0 else 1) else (if x<1762 then 0 else (if x<1768 then 1 else 2))) else (if x<3126 then (if x<2620 then 2 else (if x<2730 then 0 else 0)) else (if x<3132 then 3 else (if x<3242 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6294 : Finset ℕ := ([1628,1652,1768,2620,3132] : List ℕ).toFinset
theorem independentCachedBranchBound6294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6294 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6294 3 (fun x => (if x<1768 then (if x<1652 then 0 else 1) else (if x<2620 then 0 else (if x<3132 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6295 : Finset ℕ := ([1622,1628,1652,1738,1762,1768,2614,2620,2730,3126,3132,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6295 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6295 1622 3
  · have he : independentCachedBranchMembers6295.erase 1622=independentCachedBranchMembers6293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6293
  · have he : independentCachedBranchMembers6295.filter (independentCachedEdge 1622)=independentCachedBranchMembers6294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6294
def independentCachedBranchMembers6296 : Finset ℕ := ([132,1594,1622,1628,1652,1678,1702,1708,1738,1762,1768,2614,2620,2650,2674,2730,2758,2788,3126,3132,3162,3192,3242,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6296 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6296 132 4
  · have he : independentCachedBranchMembers6296.erase 132=independentCachedBranchMembers6292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6292
  · have he : independentCachedBranchMembers6296.filter (independentCachedEdge 132)=independentCachedBranchMembers6295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6295
def independentCachedBranchMembers6297 : Finset ℕ := ([1622,1628,1702,1708,1762,1768,2650,2730,2788,3162,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6297 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6297 4 (fun x => (if x<2650 then (if x<1708 then (if x<1628 then 0 else (if x<1702 then 1 else 0)) else (if x<1762 then 1 else (if x<1768 then 2 else 3))) else (if x<3162 then (if x<2730 then 0 else (if x<2788 then 0 else 2)) else (if x<3242 then 1 else (if x<3300 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6298 : Finset ℕ := ([48,132,1594,1622,1628,1652,1678,1702,1708,1738,1762,1768,2614,2620,2650,2674,2730,2758,2788,3126,3132,3162,3192,3242,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6298 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6298 48 4
  · have he : independentCachedBranchMembers6298.erase 48=independentCachedBranchMembers6296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6296
  · have he : independentCachedBranchMembers6298.filter (independentCachedEdge 48)=independentCachedBranchMembers6297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6297
def independentCachedBranchMembers6299 : Finset ℕ := ([48,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6299 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6299 144 5
  · have he : independentCachedBranchMembers6299.erase 144=independentCachedBranchMembers6289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6289
  · have he : independentCachedBranchMembers6299.filter (independentCachedEdge 144)=independentCachedBranchMembers6298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6298
def independentCachedBranchMembers6300 : Finset ℕ := ([1582,1594,1628,1652,1678,1690,1702,1714,1748,1768,2614,2668,2710,2730,2776,2788,2800,3126,3192,3222,3242,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6300 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6300 5 (fun x => (if x<2710 then (if x<1702 then (if x<1652 then (if x<1594 then 0 else (if x<1628 then 1 else 0)) else (if x<1678 then 1 else (if x<1690 then 2 else 0))) else (if x<1768 then (if x<1714 then 1 else (if x<1748 then 2 else 2)) else (if x<2614 then 0 else (if x<2668 then 1 else 0)))) else (if x<3192 then (if x<2788 then (if x<2730 then 2 else (if x<2776 then 0 else 0)) else (if x<2800 then 1 else (if x<3126 then 2 else 3))) else (if x<3276 then (if x<3222 then 3 else (if x<3242 then 4 else 3)) else (if x<3300 then 4 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6301 : Finset ℕ := ([1582,1594,1678,1690,1702,1714,2614,2710,2730,3126,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6301 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6301 4 (fun x => (if x<2614 then (if x<1690 then (if x<1594 then 0 else (if x<1678 then 1 else 1)) else (if x<1702 then 0 else (if x<1714 then 2 else 3))) else (if x<3126 then (if x<2710 then 2 else (if x<2730 then 3 else 0)) else (if x<3222 then 3 else (if x<3242 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6302 : Finset ℕ := ([252,1582,1594,1628,1652,1678,1690,1702,1714,1748,1768,2614,2668,2710,2730,2776,2788,2800,3126,3192,3222,3242,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6302 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6302 252 4
  · have he : independentCachedBranchMembers6302.erase 252=independentCachedBranchMembers6300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6300
  · have he : independentCachedBranchMembers6302.filter (independentCachedEdge 252)=independentCachedBranchMembers6301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6301
def independentCachedBranchMembers6303 : Finset ℕ := ([1594,1652,1678,1690,1748,2730,2788,2800,3242,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6303 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6303 4 (fun x => (if x<2730 then (if x<1678 then (if x<1652 then 0 else 0) else (if x<1690 then 1 else (if x<1748 then 2 else 1))) else (if x<3242 then (if x<2788 then 0 else (if x<2800 then 0 else 1)) else (if x<3300 then 2 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
