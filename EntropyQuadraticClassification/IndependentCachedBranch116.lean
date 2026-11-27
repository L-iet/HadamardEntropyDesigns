/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch115
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6496 : Finset ℕ := ([36,72,132,246,1594,1622,1642,1652,1690,1702,1720,1738,1748,1768,2614,2650,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3252,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6496 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6496 1720 4
  · have he : independentCachedBranchMembers6496.erase 1720=independentCachedBranchMembers6494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6494
  · have he : independentCachedBranchMembers6496.filter (independentCachedEdge 1720)=independentCachedBranchMembers6495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6495
def independentCachedBranchMembers6497 : Finset ℕ := ([12,18,36,48,66,72,132,144,192,222,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6497 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6497 12 5
  · have he : independentCachedBranchMembers6497.erase 12=independentCachedBranchMembers6471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6471
  · have he : independentCachedBranchMembers6497.filter (independentCachedEdge 12)=independentCachedBranchMembers6496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6496
def independentCachedBranchMembers6498 : Finset ℕ := ([144,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3126,3150,3174,3192,3228,3242,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6498 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6498 5 (fun x => (if x<2674 then (if x<1714 then (if x<1622 then (if x<246 then 0 else (if x<1582 then 0 else 1)) else (if x<1690 then 1 else (if x<1708 then 1 else 2))) else (if x<1762 then (if x<1738 then 0 else (if x<1748 then 2 else 0)) else (if x<2650 then (if x<2620 then 1 else 2) else (if x<2668 then 2 else 3)))) else (if x<3174 then (if x<2776 then (if x<2710 then 3 else (if x<2758 then 0 else 3)) else (if x<3126 then (if x<2800 then 3 else 0) else (if x<3150 then 4 else 4))) else (if x<3242 then (if x<3192 then 1 else (if x<3228 then 3 else 4)) else (if x<3282 then (if x<3252 then 1 else 0) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6499 : Finset ℕ := ([1582,1690,1714,1748,2668,2710,2776,2800,3126,3192,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6499 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6499 4 (fun x => (if x<2776 then (if x<1748 then (if x<1690 then 0 else (if x<1714 then 0 else 1)) else (if x<2668 then 1 else (if x<2710 then 0 else 1))) else (if x<3192 then (if x<2800 then 0 else (if x<3126 then 1 else 2)) else (if x<3242 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6500 : Finset ℕ := ([66,144,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3126,3150,3174,3192,3228,3242,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6500 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6500 66 4
  · have he : independentCachedBranchMembers6500.erase 66=independentCachedBranchMembers6498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6498
  · have he : independentCachedBranchMembers6500.filter (independentCachedEdge 66)=independentCachedBranchMembers6499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6499
def independentCachedBranchMembers6501 : Finset ℕ := ([1622,1714,1748,1762,2674,2710,2758,2800,3150,3192,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6501 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6501 4 (fun x => (if x<2758 then (if x<1762 then (if x<1714 then 0 else (if x<1748 then 0 else 1)) else (if x<2674 then 1 else (if x<2710 then 0 else 0))) else (if x<3192 then (if x<2800 then 1 else (if x<3150 then 1 else 2)) else (if x<3228 then 2 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6502 : Finset ℕ := ([36,66,144,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3126,3150,3174,3192,3228,3242,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6502 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6502 36 4
  · have he : independentCachedBranchMembers6502.erase 36=independentCachedBranchMembers6500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6500
  · have he : independentCachedBranchMembers6502.filter (independentCachedEdge 36)=independentCachedBranchMembers6501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6501
def independentCachedBranchMembers6503 : Finset ℕ := ([36,66,144,246,1582,1622,1690,1762,2620,2650,2710,2800,3126,3150,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6503 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6503 4 (fun x => (if x<2620 then (if x<1582 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6504 : Finset ℕ := ([36,66,144,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6504 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6504 3276 4
  · have he : independentCachedBranchMembers6504.erase 3276=independentCachedBranchMembers6502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6502
  · have he : independentCachedBranchMembers6504.filter (independentCachedEdge 3276)=independentCachedBranchMembers6503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6503
def independentCachedBranchMembers6505 : Finset ℕ := ([36,66,144,246,1708,1714,1738,1748,2668,2674,2758,2776,3126,3150,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6505 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6505 4 (fun x => (if x<2668 then (if x<1708 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3126 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6506 : Finset ℕ := ([36,66,144,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6506 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6506 3102 4
  · have he : independentCachedBranchMembers6506.erase 3102=independentCachedBranchMembers6504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6504
  · have he : independentCachedBranchMembers6506.filter (independentCachedEdge 3102)=independentCachedBranchMembers6505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6505
def independentCachedBranchMembers6507 : Finset ℕ := ([1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6507 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6507 4 (fun x => (if x<2620 then (if x<1714 then (if x<1690 then (if x<1622 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<2710 then (if x<2668 then (if x<2650 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2776 then (if x<2758 then 2 else 3) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6508 : Finset ℕ := ([36,66,144,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6508 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6508 3072 4
  · have he : independentCachedBranchMembers6508.erase 3072=independentCachedBranchMembers6506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6506
  · have he : independentCachedBranchMembers6508.filter (independentCachedEdge 3072)=independentCachedBranchMembers6507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6507
def independentCachedBranchMembers6509 : Finset ℕ := ([36,246,1582,1708,1714,1762,2620,2668,2674,2800,3126,3174,3192,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6509 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6509 4 (fun x => (if x<2674 then (if x<1714 then (if x<1582 then (if x<246 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3192 then (if x<3126 then (if x<2800 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6510 : Finset ℕ := ([36,66,144,222,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6510 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6510 222 4
  · have he : independentCachedBranchMembers6510.erase 222=independentCachedBranchMembers6508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6508
  · have he : independentCachedBranchMembers6510.filter (independentCachedEdge 222)=independentCachedBranchMembers6509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6509
def independentCachedBranchMembers6511 : Finset ℕ := ([66,144,1622,1690,1708,1714,2650,2668,2674,2710,3150,3174,3192,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6511 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6511 4 (fun x => (if x<2674 then (if x<1708 then (if x<1622 then (if x<144 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3192 then (if x<3150 then (if x<2710 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3228 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6512 : Finset ℕ := ([36,66,144,192,222,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6512 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6512 192 4
  · have he : independentCachedBranchMembers6512.erase 192=independentCachedBranchMembers6510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6510
  · have he : independentCachedBranchMembers6512.filter (independentCachedEdge 192)=independentCachedBranchMembers6511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6511
def independentCachedBranchMembers6513 : Finset ℕ := ([66,144,1582,1738,1748,1762,2620,2758,2776,2800,3150,3174,3192,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6513 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6513 4 (fun x => (if x<2776 then (if x<1748 then (if x<1582 then (if x<144 then 0 else 0) else (if x<1738 then 1 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2758 then 1 else 2))) else (if x<3192 then (if x<3150 then (if x<2800 then 1 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3228 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6514 : Finset ℕ := ([18,36,66,144,192,222,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6514 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6514 18 4
  · have he : independentCachedBranchMembers6514.erase 18=independentCachedBranchMembers6512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6512
  · have he : independentCachedBranchMembers6514.filter (independentCachedEdge 18)=independentCachedBranchMembers6513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6513
def independentCachedBranchMembers6515 : Finset ℕ := ([36,246,1622,1690,1738,1748,2650,2710,2758,2776,3126,3174,3192,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6515 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6515 4 (fun x => (if x<2758 then (if x<1738 then (if x<1622 then (if x<246 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1748 then 2 else 2) else (if x<2710 then 1 else 1))) else (if x<3192 then (if x<3126 then (if x<2776 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6516 : Finset ℕ := ([12,18,36,66,144,192,222,246,1582,1622,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2710,2758,2776,2800,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6516 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6516 12 4
  · have he : independentCachedBranchMembers6516.erase 12=independentCachedBranchMembers6514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6514
  · have he : independentCachedBranchMembers6516.filter (independentCachedEdge 12)=independentCachedBranchMembers6515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6515
def independentCachedBranchMembers6517 : Finset ℕ := ([12,18,36,48,66,72,132,144,192,222,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6517 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6517 2680 5
  · have he : independentCachedBranchMembers6517.erase 2680=independentCachedBranchMembers6497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6497
  · have he : independentCachedBranchMembers6517.filter (independentCachedEdge 2680)=independentCachedBranchMembers6516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6516
def independentCachedBranchMembers6518 : Finset ℕ := ([132,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3132,3162,3174,3192,3222,3242,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6518 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6518 5 (fun x => (if x<2674 then (if x<1714 then (if x<1628 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1678 then 1 else (if x<1708 then 1 else 0))) else (if x<1768 then (if x<1738 then 2 else (if x<1748 then 2 else 0)) else (if x<2638 then (if x<2614 then 1 else 2) else (if x<2668 then 2 else 3)))) else (if x<3174 then (if x<2776 then (if x<2716 then 3 else (if x<2758 then 0 else 3)) else (if x<3132 then (if x<2788 then 3 else 0) else (if x<3162 then 4 else 4))) else (if x<3242 then (if x<3192 then 3 else (if x<3222 then 1 else 4)) else (if x<3276 then (if x<3252 then 1 else 0) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6519 : Finset ℕ := ([1594,1678,1708,1748,2674,2716,2758,2788,3132,3174,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6519 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6519 4 (fun x => (if x<2758 then (if x<1748 then (if x<1678 then 0 else (if x<1708 then 0 else 1)) else (if x<2674 then 1 else (if x<2716 then 0 else 1))) else (if x<3174 then (if x<2788 then 0 else (if x<3132 then 1 else 2)) else (if x<3242 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6520 : Finset ℕ := ([72,132,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3132,3162,3174,3192,3222,3242,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6520 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6520 72 4
  · have he : independentCachedBranchMembers6520.erase 72=independentCachedBranchMembers6518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6518
  · have he : independentCachedBranchMembers6520.filter (independentCachedEdge 72)=independentCachedBranchMembers6519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6519
def independentCachedBranchMembers6521 : Finset ℕ := ([1628,1708,1748,1768,2668,2716,2776,2788,3162,3174,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6521 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6521 4 (fun x => (if x<2776 then (if x<1768 then (if x<1708 then 0 else (if x<1748 then 0 else 1)) else (if x<2668 then 1 else (if x<2716 then 0 else 0))) else (if x<3174 then (if x<2788 then 1 else (if x<3162 then 1 else 2)) else (if x<3222 then 2 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6522 : Finset ℕ := ([48,72,132,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3132,3162,3174,3192,3222,3242,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6522 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6522 48 4
  · have he : independentCachedBranchMembers6522.erase 48=independentCachedBranchMembers6520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6520
  · have he : independentCachedBranchMembers6522.filter (independentCachedEdge 48)=independentCachedBranchMembers6521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6521
def independentCachedBranchMembers6523 : Finset ℕ := ([48,72,132,252,1594,1628,1678,1768,2614,2638,2716,2788,3132,3162,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6523 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6523 4 (fun x => (if x<2614 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6524 : Finset ℕ := ([48,72,132,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6524 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6524 3282 4
  · have he : independentCachedBranchMembers6524.erase 3282=independentCachedBranchMembers6522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6522
  · have he : independentCachedBranchMembers6524.filter (independentCachedEdge 3282)=independentCachedBranchMembers6523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6523
def independentCachedBranchMembers6525 : Finset ℕ := ([48,72,132,252,1708,1714,1738,1748,2668,2674,2758,2776,3132,3162,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6525 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6525 4 (fun x => (if x<2668 then (if x<1708 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3132 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6526 : Finset ℕ := ([48,72,132,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6526 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6526 3102 4
  · have he : independentCachedBranchMembers6526.erase 3102=independentCachedBranchMembers6524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6524
  · have he : independentCachedBranchMembers6526.filter (independentCachedEdge 3102)=independentCachedBranchMembers6525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6525
def independentCachedBranchMembers6527 : Finset ℕ := ([1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788] : List ℕ).toFinset
theorem independentCachedBranchBound6527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6527 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6527 4 (fun x => (if x<2614 then (if x<1714 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<2716 then (if x<2668 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2776 then (if x<2758 then 2 else 3) else (if x<2788 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
