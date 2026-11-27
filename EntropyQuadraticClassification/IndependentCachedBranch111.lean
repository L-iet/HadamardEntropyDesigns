/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch110
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6336 : Finset ℕ := ([36,72,144,252,1582,1628,1642,1652,1690,1708,1714,1768,2614,2650,2668,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6336 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6336 36 4
  · have he : independentCachedBranchMembers6336.erase 36=independentCachedBranchMembers6334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6334
  · have he : independentCachedBranchMembers6336.filter (independentCachedEdge 36)=independentCachedBranchMembers6335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6335
def independentCachedBranchMembers6337 : Finset ℕ := ([36,72,144,252,1582,1628,1690,1768,2614,2650,2716,2800,3132,3150,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6337 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6337 4 (fun x => (if x<2614 then (if x<1582 then (if x<144 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1690 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3222 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6338 : Finset ℕ := ([36,72,144,252,1582,1628,1642,1652,1690,1708,1714,1768,2614,2650,2668,2674,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6338 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6338 2674 4
  · have he : independentCachedBranchMembers6338.erase 2674=independentCachedBranchMembers6336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6336
  · have he : independentCachedBranchMembers6338.filter (independentCachedEdge 2674)=independentCachedBranchMembers6337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6337
def independentCachedBranchMembers6339 : Finset ℕ := ([36,48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6339 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6339 3270 5
  · have he : independentCachedBranchMembers6339.erase 3270=independentCachedBranchMembers6327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6327
  · have he : independentCachedBranchMembers6339.filter (independentCachedEdge 3270)=independentCachedBranchMembers6338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6338
def independentCachedBranchMembers6340 : Finset ℕ := ([144,252,1582,1628,1690,1702,1720,1738,1748,1768,2620,2638,2668,2674,2710,2730,2740,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6340 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6340 5 (fun x => (if x<2674 then (if x<1720 then (if x<1628 then (if x<252 then 0 else (if x<1582 then 0 else 1)) else (if x<1690 then 1 else (if x<1702 then 1 else 2))) else (if x<1768 then (if x<1738 then 0 else (if x<1748 then 2 else 0)) else (if x<2638 then (if x<2620 then 1 else 3) else (if x<2668 then 3 else 1)))) else (if x<3162 then (if x<2740 then (if x<2710 then 3 else (if x<2730 then 3 else 1)) else (if x<2788 then (if x<2776 then 0 else 0) else (if x<3126 then 3 else 2))) else (if x<3228 then (if x<3174 then 2 else (if x<3192 then 4 else 4)) else (if x<3282 then (if x<3276 then 0 else 4) else (if x<3312 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6341 : Finset ℕ := ([1582,1690,1720,1748,2620,2674,2730,2788,3174,3228,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6341 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6341 4 (fun x => (if x<2730 then (if x<1748 then (if x<1690 then 0 else (if x<1720 then 0 else 1)) else (if x<2620 then 1 else (if x<2674 then 2 else 2))) else (if x<3228 then (if x<2788 then 0 else (if x<3174 then 2 else 3)) else (if x<3282 then 1 else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6342 : Finset ℕ := ([72,144,252,1582,1628,1690,1702,1720,1738,1748,1768,2620,2638,2668,2674,2710,2730,2740,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6342 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6342 72 4
  · have he : independentCachedBranchMembers6342.erase 72=independentCachedBranchMembers6340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6340
  · have he : independentCachedBranchMembers6342.filter (independentCachedEdge 72)=independentCachedBranchMembers6341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6341
def independentCachedBranchMembers6343 : Finset ℕ := ([1628,1720,1748,1768,2638,2674,2710,2730,3192,3228,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6343 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6343 4 (fun x => (if x<2710 then (if x<1768 then (if x<1720 then 0 else (if x<1748 then 0 else 1)) else (if x<2638 then 1 else (if x<2674 then 0 else 2))) else (if x<3228 then (if x<2730 then 1 else (if x<3192 then 0 else 2)) else (if x<3276 then 2 else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6344 : Finset ℕ := ([36,72,144,252,1582,1628,1690,1702,1720,1738,1748,1768,2620,2638,2668,2674,2710,2730,2740,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6344 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6344 36 4
  · have he : independentCachedBranchMembers6344.erase 36=independentCachedBranchMembers6342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6342
  · have he : independentCachedBranchMembers6344.filter (independentCachedEdge 36)=independentCachedBranchMembers6343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6343
def independentCachedBranchMembers6345 : Finset ℕ := ([36,72,144,252,1582,1628,1690,1768,2620,2638,2710,2788,3126,3162,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6345 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6345 4 (fun x => (if x<2620 then (if x<1582 then (if x<144 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1690 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3228 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6346 : Finset ℕ := ([36,72,144,252,1582,1628,1690,1702,1720,1738,1748,1768,2620,2638,2668,2674,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6346 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6346 2758 4
  · have he : independentCachedBranchMembers6346.erase 2758=independentCachedBranchMembers6344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6344
  · have he : independentCachedBranchMembers6346.filter (independentCachedEdge 2758)=independentCachedBranchMembers6345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6345
def independentCachedBranchMembers6347 : Finset ℕ := ([36,48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6347 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6347 3186 5
  · have he : independentCachedBranchMembers6347.erase 3186=independentCachedBranchMembers6339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6339
  · have he : independentCachedBranchMembers6347.filter (independentCachedEdge 3186)=independentCachedBranchMembers6346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6346
def independentCachedBranchMembers6348 : Finset ℕ := ([132,246,1594,1622,1678,1702,1720,1738,1748,1762,2614,2650,2668,2674,2716,2730,2740,2758,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6348 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6348 5 (fun x => (if x<2674 then (if x<1720 then (if x<1622 then (if x<246 then 0 else (if x<1594 then 0 else 1)) else (if x<1678 then 1 else (if x<1702 then 1 else 0))) else (if x<1762 then (if x<1738 then 2 else (if x<1748 then 2 else 0)) else (if x<2650 then (if x<2614 then 1 else 3) else (if x<2668 then 3 else 3)))) else (if x<3150 then (if x<2740 then (if x<2716 then 1 else (if x<2730 then 3 else 1)) else (if x<2800 then (if x<2758 then 0 else 0) else (if x<3132 then 3 else 2))) else (if x<3222 then (if x<3174 then 2 else (if x<3192 then 4 else 4)) else (if x<3282 then (if x<3276 then 0 else 4) else (if x<3300 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6349 : Finset ℕ := ([1594,1678,1702,1748,2614,2668,2730,2800,3192,3222,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6349 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6349 4 (fun x => (if x<2730 then (if x<1748 then (if x<1678 then 0 else (if x<1702 then 0 else 1)) else (if x<2614 then 1 else (if x<2668 then 2 else 2))) else (if x<3222 then (if x<2800 then 0 else (if x<3192 then 2 else 3)) else (if x<3276 then 1 else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6350 : Finset ℕ := ([66,132,246,1594,1622,1678,1702,1720,1738,1748,1762,2614,2650,2668,2674,2716,2730,2740,2758,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6350 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6350 66 4
  · have he : independentCachedBranchMembers6350.erase 66=independentCachedBranchMembers6348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6348
  · have he : independentCachedBranchMembers6350.filter (independentCachedEdge 66)=independentCachedBranchMembers6349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6349
def independentCachedBranchMembers6351 : Finset ℕ := ([1622,1702,1748,1762,2650,2668,2716,2730,3174,3222,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6351 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6351 4 (fun x => (if x<2716 then (if x<1762 then (if x<1702 then 0 else (if x<1748 then 0 else 1)) else (if x<2650 then 1 else (if x<2668 then 0 else 2))) else (if x<3222 then (if x<2730 then 1 else (if x<3174 then 0 else 2)) else (if x<3282 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6352 : Finset ℕ := ([48,66,132,246,1594,1622,1678,1702,1720,1738,1748,1762,2614,2650,2668,2674,2716,2730,2740,2758,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6352 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6352 48 4
  · have he : independentCachedBranchMembers6352.erase 48=independentCachedBranchMembers6350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6350
  · have he : independentCachedBranchMembers6352.filter (independentCachedEdge 48)=independentCachedBranchMembers6351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6351
def independentCachedBranchMembers6353 : Finset ℕ := ([48,66,132,246,1594,1622,1678,1762,2614,2650,2716,2800,3132,3150,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6353 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6353 4 (fun x => (if x<2614 then (if x<1594 then (if x<132 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1678 then (if x<1622 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3222 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6354 : Finset ℕ := ([48,66,132,246,1594,1622,1678,1702,1720,1738,1748,1762,2614,2650,2668,2674,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6354 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6354 2776 4
  · have he : independentCachedBranchMembers6354.erase 2776=independentCachedBranchMembers6352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6352
  · have he : independentCachedBranchMembers6354.filter (independentCachedEdge 2776)=independentCachedBranchMembers6353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6353
def independentCachedBranchMembers6355 : Finset ℕ := ([36,48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6355 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6355 3180 5
  · have he : independentCachedBranchMembers6355.erase 3180=independentCachedBranchMembers6347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6347
  · have he : independentCachedBranchMembers6355.filter (independentCachedEdge 3180)=independentCachedBranchMembers6354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6354
def independentCachedBranchMembers6356 : Finset ℕ := ([132,252,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2740,2758,2776,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6356 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6356 5 (fun x => (if x<2674 then (if x<1708 then (if x<1642 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1702 then 1 else 1))) else (if x<1738 then (if x<1714 then 0 else (if x<1720 then 2 else 1)) else (if x<1748 then 2 else (if x<2668 then 0 else 3)))) else (if x<3150 then (if x<2776 then (if x<2740 then 3 else (if x<2758 then 0 else 3)) else (if x<3126 then 3 else (if x<3132 then 2 else 4))) else (if x<3228 then (if x<3162 then 2 else (if x<3222 then 4 else 4)) else (if x<3300 then 0 else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6357 : Finset ℕ := ([1652,1708,1720,1748,2674,2758,3132,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6357 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6357 4 (fun x => (if x<2758 then (if x<1720 then (if x<1708 then 0 else 0) else (if x<1748 then 1 else (if x<2674 then 1 else 0))) else (if x<3228 then (if x<3132 then 1 else 2) else (if x<3300 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6358 : Finset ℕ := ([72,132,252,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2740,2758,2776,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6358 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6358 72 4
  · have he : independentCachedBranchMembers6358.erase 72=independentCachedBranchMembers6356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6356
  · have he : independentCachedBranchMembers6358.filter (independentCachedEdge 72)=independentCachedBranchMembers6357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6357
def independentCachedBranchMembers6359 : Finset ℕ := ([1642,1702,1708,1748,2668,2776,3162,3222,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6359 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6359 4 (fun x => (if x<2776 then (if x<1708 then (if x<1702 then 0 else 0) else (if x<1748 then 1 else (if x<2668 then 1 else 2))) else (if x<3222 then (if x<3162 then 2 else 0) else (if x<3228 then 0 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6360 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2740,2758,2776,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6360 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6360 48 4
  · have he : independentCachedBranchMembers6360.erase 48=independentCachedBranchMembers6358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6358
  · have he : independentCachedBranchMembers6360.filter (independentCachedEdge 48)=independentCachedBranchMembers6359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6359
def independentCachedBranchMembers6361 : Finset ℕ := ([72,252,1642,1708,1720,1738,2668,2776,3132,3150,3162,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6361 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6361 4 (fun x => (if x<2668 then (if x<1708 then (if x<252 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then 1 else (if x<1738 then 2 else 2))) else (if x<3150 then (if x<2776 then 0 else (if x<3132 then 0 else 2)) else (if x<3162 then 2 else (if x<3228 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6362 : Finset ℕ := ([48,72,132,246,252,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2740,2758,2776,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6362 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6362 246 4
  · have he : independentCachedBranchMembers6362.erase 246=independentCachedBranchMembers6360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6360
  · have he : independentCachedBranchMembers6362.filter (independentCachedEdge 246)=independentCachedBranchMembers6361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6361
def independentCachedBranchMembers6363 : Finset ℕ := ([48,132,1652,1702,1708,1738,2674,2758,3126,3132,3162,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6363 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6363 4 (fun x => (if x<2674 then (if x<1702 then (if x<132 then 0 else (if x<1652 then 0 else 1)) else (if x<1708 then 1 else (if x<1738 then 2 else 2))) else (if x<3132 then (if x<2758 then 0 else (if x<3126 then 0 else 1)) else (if x<3162 then 2 else (if x<3300 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6364 : Finset ℕ := ([48,72,132,144,246,252,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2740,2758,2776,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6364 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6364 144 4
  · have he : independentCachedBranchMembers6364.erase 144=independentCachedBranchMembers6362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6362
  · have he : independentCachedBranchMembers6364.filter (independentCachedEdge 144)=independentCachedBranchMembers6363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6363
def independentCachedBranchMembers6365 : Finset ℕ := ([72,252,1652,1702,1714,1748,2668,2776,3126,3222,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6365 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6365 4 (fun x => (if x<2668 then (if x<1702 then (if x<252 then 0 else (if x<1652 then 0 else 1)) else (if x<1714 then 1 else (if x<1748 then 2 else 2))) else (if x<3222 then (if x<2776 then 0 else (if x<3126 then 0 else 1)) else (if x<3300 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6366 : Finset ℕ := ([48,66,72,132,144,246,252,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2740,2758,2776,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6366 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6366 66 4
  · have he : independentCachedBranchMembers6366.erase 66=independentCachedBranchMembers6364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6364
  · have he : independentCachedBranchMembers6366.filter (independentCachedEdge 66)=independentCachedBranchMembers6365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6365
def independentCachedBranchMembers6367 : Finset ℕ := ([48,132,1642,1714,1720,1748,2674,2758,3150,3222,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6367 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6367 4 (fun x => (if x<2674 then (if x<1714 then (if x<132 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then 1 else (if x<1748 then 2 else 2))) else (if x<3222 then (if x<2758 then 0 else (if x<3150 then 0 else 1)) else (if x<3228 then 1 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
