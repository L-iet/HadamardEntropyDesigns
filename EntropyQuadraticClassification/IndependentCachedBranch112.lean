/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch111
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6368 : Finset ℕ := ([36,48,66,72,132,144,246,252,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2740,2758,2776,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6368 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6368 36 4
  · have he : independentCachedBranchMembers6368.erase 36=independentCachedBranchMembers6366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6366
  · have he : independentCachedBranchMembers6368.filter (independentCachedEdge 36)=independentCachedBranchMembers6367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6367
def independentCachedBranchMembers6369 : Finset ℕ := ([36,48,66,72,132,144,246,252,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6369 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6369 4 (fun x => (if x<3126 then (if x<132 then (if x<66 then (if x<48 then 0 else 1) else (if x<72 then 0 else 1)) else (if x<246 then (if x<144 then 1 else 0) else (if x<252 then 0 else 1))) else (if x<3222 then (if x<3150 then (if x<3132 then 2 else 3) else (if x<3162 then 2 else 3)) else (if x<3300 then (if x<3228 then 3 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6370 : Finset ℕ := ([36,48,66,72,132,144,246,252,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2730,2740,2758,2776,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6370 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6370 2730 4
  · have he : independentCachedBranchMembers6370.erase 2730=independentCachedBranchMembers6368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6368
  · have he : independentCachedBranchMembers6370.filter (independentCachedEdge 2730)=independentCachedBranchMembers6369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6369
def independentCachedBranchMembers6371 : Finset ℕ := ([36,48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6371 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6371 3102 5
  · have he : independentCachedBranchMembers6371.erase 3102=independentCachedBranchMembers6355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6355
  · have he : independentCachedBranchMembers6371.filter (independentCachedEdge 3102)=independentCachedBranchMembers6370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6370
def independentCachedBranchMembers6372 : Finset ℕ := ([1628,1642,1652,1678,1702,1708,1714,1720,1738,1748,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2758,2776,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6372 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6372 5 (fun x => (if x<2620 then (if x<1714 then (if x<1678 then (if x<1642 then 0 else (if x<1652 then 0 else 1)) else (if x<1702 then 0 else (if x<1708 then 1 else 2))) else (if x<1748 then (if x<1720 then 2 else (if x<1738 then 0 else 2)) else (if x<1768 then 2 else (if x<2614 then 1 else 1)))) else (if x<2716 then (if x<2668 then (if x<2638 then 3 else (if x<2650 then 0 else 3)) else (if x<2674 then 4 else (if x<2710 then 4 else 3))) else (if x<2776 then (if x<2730 then 0 else (if x<2758 then 0 else 4)) else (if x<2788 then 4 else (if x<2800 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6373 : Finset ℕ := ([1642,1714,1720,1748,2638,2668,2710,2716,2776,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6373 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6373 4 (fun x => (if x<2668 then (if x<1720 then (if x<1714 then 0 else 0) else (if x<1748 then 1 else (if x<2638 then 1 else 0))) else (if x<2716 then (if x<2710 then 2 else 0) else (if x<2776 then 1 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6374 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1708,1714,1720,1738,1748,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2758,2776,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6374 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6374 1594 4
  · have he : independentCachedBranchMembers6374.erase 1594=independentCachedBranchMembers6372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6372
  · have he : independentCachedBranchMembers6374.filter (independentCachedEdge 1594)=independentCachedBranchMembers6373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6373
def independentCachedBranchMembers6375 : Finset ℕ := ([1628,1642,1702,1714,1738,1768,2614,2638,2650,2668,2710,2776] : List ℕ).toFinset
theorem independentCachedBranchBound6375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6375 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6375 4 (fun x => (if x<2614 then (if x<1714 then (if x<1642 then 0 else (if x<1702 then 0 else 1)) else (if x<1738 then 2 else (if x<1768 then 1 else 2))) else (if x<2668 then (if x<2638 then 1 else (if x<2650 then 0 else 1)) else (if x<2710 then 2 else (if x<2776 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6376 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2758,2776,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6376 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6376 1762 4
  · have he : independentCachedBranchMembers6376.erase 1762=independentCachedBranchMembers6374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6374
  · have he : independentCachedBranchMembers6376.filter (independentCachedEdge 1762)=independentCachedBranchMembers6375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6375
def independentCachedBranchMembers6377 : Finset ℕ := ([1594,1652,1678,1714,1720,1738,2614,2620,2638,2674,2758,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6377 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6377 4 (fun x => (if x<2614 then (if x<1714 then (if x<1652 then 0 else (if x<1678 then 0 else 1)) else (if x<1720 then 1 else (if x<1738 then 2 else 2))) else (if x<2674 then (if x<2620 then 0 else (if x<2638 then 2 else 1)) else (if x<2758 then 1 else (if x<2800 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6378 : Finset ℕ := ([1594,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2758,2776,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6378 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6378 1690 4
  · have he : independentCachedBranchMembers6378.erase 1690=independentCachedBranchMembers6376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6376
  · have he : independentCachedBranchMembers6378.filter (independentCachedEdge 1690)=independentCachedBranchMembers6377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6377
def independentCachedBranchMembers6379 : Finset ℕ := ([1628,1652,1708,1720,1748,1768,2620,2668,2716,2776,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6379 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6379 4 (fun x => (if x<2620 then (if x<1720 then (if x<1652 then 0 else (if x<1708 then 1 else 0)) else (if x<1748 then 1 else (if x<1768 then 2 else 2))) else (if x<2776 then (if x<2668 then 0 else (if x<2716 then 3 else 3)) else (if x<2788 then 2 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6380 : Finset ℕ := ([1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2758,2776,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6380 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6380 1622 4
  · have he : independentCachedBranchMembers6380.erase 1622=independentCachedBranchMembers6378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6378
  · have he : independentCachedBranchMembers6380.filter (independentCachedEdge 1622)=independentCachedBranchMembers6379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6379
def independentCachedBranchMembers6381 : Finset ℕ := ([1594,1642,1678,1702,1708,1748,2650,2674,2710,2716,2758,2788] : List ℕ).toFinset
theorem independentCachedBranchBound6381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6381 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6381 4 (fun x => (if x<2650 then (if x<1702 then (if x<1642 then 0 else (if x<1678 then 1 else 0)) else (if x<1708 then 1 else (if x<1748 then 2 else 2))) else (if x<2716 then (if x<2674 then 1 else (if x<2710 then 0 else 1)) else (if x<2758 then 2 else (if x<2788 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6382 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2758,2776,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6382 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6382 1582 4
  · have he : independentCachedBranchMembers6382.erase 1582=independentCachedBranchMembers6380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6380
  · have he : independentCachedBranchMembers6382.filter (independentCachedEdge 1582)=independentCachedBranchMembers6381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6381
def independentCachedBranchMembers6383 : Finset ℕ := ([1582,1594,1622,1628,1678,1690,1762,1768,2614,2620,2638,2650,2710,2716,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6383 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6383 4 (fun x => (if x<2614 then (if x<1678 then (if x<1622 then (if x<1594 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1762 then (if x<1690 then 1 else 0) else (if x<1768 then 0 else 1))) else (if x<2710 then (if x<2638 then (if x<2620 then 2 else 3) else (if x<2650 then 2 else 3)) else (if x<2788 then (if x<2716 then 3 else 2) else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6384 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6384 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6384 2740 4
  · have he : independentCachedBranchMembers6384.erase 2740=independentCachedBranchMembers6382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6382
  · have he : independentCachedBranchMembers6384.filter (independentCachedEdge 2740)=independentCachedBranchMembers6383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6383
def independentCachedBranchMembers6385 : Finset ℕ := ([36,48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6385 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6385 3072 5
  · have he : independentCachedBranchMembers6385.erase 3072=independentCachedBranchMembers6371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6371
  · have he : independentCachedBranchMembers6385.filter (independentCachedEdge 3072)=independentCachedBranchMembers6384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6384
def independentCachedBranchMembers6386 : Finset ℕ := ([252,1594,1628,1642,1652,1678,1702,1720,1768,2620,2650,2668,2674,2710,2758,2776,2800,3126,3150,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6386 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6386 5 (fun x => (if x<2710 then (if x<1702 then (if x<1642 then (if x<1594 then 0 else (if x<1628 then 1 else 0)) else (if x<1652 then 2 else (if x<1678 then 1 else 2))) else (if x<2620 then (if x<1720 then 1 else (if x<1768 then 0 else 1)) else (if x<2668 then (if x<2650 then 0 else 3) else (if x<2674 then 3 else 2)))) else (if x<3192 then (if x<2800 then (if x<2758 then 2 else (if x<2776 then 3 else 0)) else (if x<3126 then 3 else (if x<3150 then 1 else 3))) else (if x<3252 then (if x<3228 then 0 else (if x<3242 then 0 else 1)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3300 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6387 : Finset ℕ := ([1628,1652,1720,1768,2620,2668,2776,2800,3126,3150,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6387 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6387 4 (fun x => (if x<2776 then (if x<1768 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<2620 then 1 else (if x<2668 then 0 else 1))) else (if x<3150 then (if x<2800 then 0 else (if x<3126 then 1 else 2)) else (if x<3242 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6388 : Finset ℕ := ([132,252,1594,1628,1642,1652,1678,1702,1720,1768,2620,2650,2668,2674,2710,2758,2776,2800,3126,3150,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6388 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6388 132 4
  · have he : independentCachedBranchMembers6388.erase 132=independentCachedBranchMembers6386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6386
  · have he : independentCachedBranchMembers6388.filter (independentCachedEdge 132)=independentCachedBranchMembers6387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6387
def independentCachedBranchMembers6389 : Finset ℕ := ([1594,1652,1678,1720,2620,2674,2758,2800,3228,3242,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6389 4 (fun x => (if x<2758 then (if x<1720 then (if x<1652 then 0 else (if x<1678 then 0 else 1)) else (if x<2620 then 1 else (if x<2674 then 0 else 0))) else (if x<3242 then (if x<2800 then 1 else (if x<3228 then 1 else 2)) else (if x<3282 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6390 : Finset ℕ := ([72,132,252,1594,1628,1642,1652,1678,1702,1720,1768,2620,2650,2668,2674,2710,2758,2776,2800,3126,3150,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6390 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6390 72 4
  · have he : independentCachedBranchMembers6390.erase 72=independentCachedBranchMembers6388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6388
  · have he : independentCachedBranchMembers6390.filter (independentCachedEdge 72)=independentCachedBranchMembers6389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6389
def independentCachedBranchMembers6391 : Finset ℕ := ([1628,1642,1702,1768,2650,2668,2710,2776,3228,3242,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6391 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6391 4 (fun x => (if x<2710 then (if x<1768 then (if x<1642 then 0 else (if x<1702 then 0 else 1)) else (if x<2650 then 1 else (if x<2668 then 0 else 0))) else (if x<3242 then (if x<2776 then 1 else (if x<3228 then 1 else 2)) else (if x<3282 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6392 : Finset ℕ := ([48,72,132,252,1594,1628,1642,1652,1678,1702,1720,1768,2620,2650,2668,2674,2710,2758,2776,2800,3126,3150,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6392 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6392 48 4
  · have he : independentCachedBranchMembers6392.erase 48=independentCachedBranchMembers6390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6390
  · have he : independentCachedBranchMembers6392.filter (independentCachedEdge 48)=independentCachedBranchMembers6391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6391
def independentCachedBranchMembers6393 : Finset ℕ := ([48,72,132,252,1594,1628,1678,1768,2620,2650,2710,2800,3126,3150,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6393 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6393 4 (fun x => (if x<2620 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6394 : Finset ℕ := ([48,72,132,252,1594,1628,1642,1652,1678,1702,1720,1768,2620,2650,2668,2674,2710,2758,2776,2800,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6394 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6394 3174 4
  · have he : independentCachedBranchMembers6394.erase 3174=independentCachedBranchMembers6392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6392
  · have he : independentCachedBranchMembers6394.filter (independentCachedEdge 3174)=independentCachedBranchMembers6393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6393
def independentCachedBranchMembers6395 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,2668,2674,2758,2776,3126,3150,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6395 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6395 4 (fun x => (if x<2668 then (if x<1642 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3126 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6396 : Finset ℕ := ([48,72,132,252,1594,1628,1642,1652,1678,1702,1720,1768,2620,2650,2668,2674,2710,2758,2776,2800,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6396 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6396 3102 4
  · have he : independentCachedBranchMembers6396.erase 3102=independentCachedBranchMembers6394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6394
  · have he : independentCachedBranchMembers6396.filter (independentCachedEdge 3102)=independentCachedBranchMembers6395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6395
def independentCachedBranchMembers6397 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1768,2620,2650,2668,2674,2710,2758,2776,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6397 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6397 4 (fun x => (if x<2620 then (if x<1678 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<2710 then (if x<2668 then (if x<2650 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2776 then (if x<2758 then 2 else 3) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6398 : Finset ℕ := ([48,72,132,252,1594,1628,1642,1652,1678,1702,1720,1768,2620,2650,2668,2674,2710,2758,2776,2800,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6398 3072 4
  · have he : independentCachedBranchMembers6398.erase 3072=independentCachedBranchMembers6396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6396
  · have he : independentCachedBranchMembers6398.filter (independentCachedEdge 3072)=independentCachedBranchMembers6397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6397
def independentCachedBranchMembers6399 : Finset ℕ := ([36,48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6399 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6399 2770 5
  · have he : independentCachedBranchMembers6399.erase 2770=independentCachedBranchMembers6385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6385
  · have he : independentCachedBranchMembers6399.filter (independentCachedEdge 2770)=independentCachedBranchMembers6398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6398
end EntropyDesigns.QuadraticRefinement
