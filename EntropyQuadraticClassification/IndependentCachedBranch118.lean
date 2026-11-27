/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch117
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6560 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1708,1714,1720,1738,1748,1768,3072,3126,3132,3150,3162,3180,3186,3192,3222,3228,3242,3252,3270,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6560 1594 4
  · have he : independentCachedBranchMembers6560.erase 1594=independentCachedBranchMembers6558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6558
  · have he : independentCachedBranchMembers6560.filter (independentCachedEdge 1594)=independentCachedBranchMembers6559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6559
def independentCachedBranchMembers6561 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1768,3132,3162,3180,3186,3222,3270,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6561 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6561 4 (fun x => (if x<3132 then (if x<1678 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3222 then (if x<3180 then (if x<3162 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3288 then (if x<3270 then 2 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6562 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1708,1714,1720,1738,1748,1768,3072,3126,3132,3150,3162,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6562 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6562 3282 4
  · have he : independentCachedBranchMembers6562.erase 3282=independentCachedBranchMembers6560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6560
  · have he : independentCachedBranchMembers6562.filter (independentCachedEdge 3282)=independentCachedBranchMembers6561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6561
def independentCachedBranchMembers6563 : Finset ℕ := ([1594,1628,1678,1708,1714,1738,1748,1768,3126,3150,3180,3186,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6563 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6563 4 (fun x => (if x<3126 then (if x<1714 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3228 then (if x<3180 then (if x<3150 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3288 then (if x<3270 then 2 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6564 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1708,1714,1720,1738,1748,1768,3072,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6564 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6564 3174 4
  · have he : independentCachedBranchMembers6564.erase 3174=independentCachedBranchMembers6562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6562
  · have he : independentCachedBranchMembers6564.filter (independentCachedEdge 3174)=independentCachedBranchMembers6563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6563
def independentCachedBranchMembers6565 : Finset ℕ := ([1642,1652,1702,1708,1714,1720,1738,1748,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6565 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6565 4 (fun x => (if x<3126 then (if x<1714 then (if x<1702 then (if x<1652 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1738 then (if x<1720 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<3222 then (if x<3150 then (if x<3132 then 2 else 3) else (if x<3162 then 2 else 3)) else (if x<3300 then (if x<3228 then 3 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6566 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1708,1714,1720,1738,1748,1768,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6566 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6566 3102 4
  · have he : independentCachedBranchMembers6566.erase 3102=independentCachedBranchMembers6564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6564
  · have he : independentCachedBranchMembers6566.filter (independentCachedEdge 3102)=independentCachedBranchMembers6565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6565
def independentCachedBranchMembers6567 : Finset ℕ := ([1642,1702,1714,1738,1768,3072,3126,3150,3162,3180,3192,3222,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6567 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6567 4 (fun x => (if x<3150 then (if x<1738 then (if x<1702 then 0 else (if x<1714 then 0 else 1)) else (if x<3072 then (if x<1768 then 1 else 2) else (if x<3126 then 3 else 1))) else (if x<3222 then (if x<3180 then (if x<3162 then 1 else 0) else (if x<3192 then 2 else 3)) else (if x<3276 then (if x<3252 then 0 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6568 : Finset ℕ := ([1702,1714,3072,3126,3222,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6568 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6568 3 (fun x => (if x<3126 then (if x<1714 then 0 else (if x<3072 then 1 else 2)) else (if x<3222 then 0 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6569 : Finset ℕ := ([1628,1642,1702,1714,1738,1768,3072,3126,3150,3162,3180,3192,3222,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6569 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6569 1628 3
  · have he : independentCachedBranchMembers6569.erase 1628=independentCachedBranchMembers6567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6567
  · have he : independentCachedBranchMembers6569.filter (independentCachedEdge 1628)=independentCachedBranchMembers6568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6568
def independentCachedBranchMembers6570 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1708,1714,1720,1738,1748,1762,1768,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6570 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6570 1762 4
  · have he : independentCachedBranchMembers6570.erase 1762=independentCachedBranchMembers6566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6566
  · have he : independentCachedBranchMembers6570.filter (independentCachedEdge 1762)=independentCachedBranchMembers6569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6569
def independentCachedBranchMembers6571 : Finset ℕ := ([1652,1678,1714,1720,1738,3072,3126,3132,3150,3186,3192,3252,3270,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6571 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6571 4 (fun x => (if x<3132 then (if x<1720 then (if x<1678 then 0 else (if x<1714 then 1 else 0)) else (if x<3072 then (if x<1738 then 1 else 2) else (if x<3126 then 3 else 0))) else (if x<3252 then (if x<3186 then (if x<3150 then 2 else 1) else (if x<3192 then 3 else 1)) else (if x<3276 then (if x<3270 then 3 else 3) else (if x<3312 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6572 : Finset ℕ := ([1714,1720,3072,3150,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6572 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6572 3 (fun x => (if x<3150 then (if x<1720 then 0 else (if x<3072 then 1 else 2)) else (if x<3252 then 0 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6573 : Finset ℕ := ([1594,1652,1678,1714,1720,1738,3072,3126,3132,3150,3186,3192,3252,3270,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6573 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6573 1594 3
  · have he : independentCachedBranchMembers6573.erase 1594=independentCachedBranchMembers6571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6571
  · have he : independentCachedBranchMembers6573.filter (independentCachedEdge 1594)=independentCachedBranchMembers6572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6572
def independentCachedBranchMembers6574 : Finset ℕ := ([1594,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6574 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6574 1690 4
  · have he : independentCachedBranchMembers6574.erase 1690=independentCachedBranchMembers6570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6570
  · have he : independentCachedBranchMembers6574.filter (independentCachedEdge 1690)=independentCachedBranchMembers6573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6573
def independentCachedBranchMembers6575 : Finset ℕ := ([1628,1652,1708,1720,1748,1768,3072,3132,3180,3192,3228,3252,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6575 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6575 4 (fun x => (if x<3180 then (if x<1748 then (if x<1708 then (if x<1652 then 0 else 1) else (if x<1720 then 0 else 1)) else (if x<3072 then (if x<1768 then 2 else 2) else (if x<3132 then 3 else 0))) else (if x<3276 then (if x<3228 then (if x<3192 then 3 else 1) else (if x<3252 then 3 else 1)) else (if x<3300 then (if x<3288 then 0 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6576 : Finset ℕ := ([1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6576 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6576 1622 4
  · have he : independentCachedBranchMembers6576.erase 1622=independentCachedBranchMembers6574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6574
  · have he : independentCachedBranchMembers6576.filter (independentCachedEdge 1622)=independentCachedBranchMembers6575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6575
def independentCachedBranchMembers6577 : Finset ℕ := ([1594,1642,1678,1702,1708,1748,3072,3162,3186,3192,3222,3228,3252,3270,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6577 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6577 4 (fun x => (if x<3186 then (if x<1708 then (if x<1678 then (if x<1642 then 0 else 1) else (if x<1702 then 0 else 1)) else (if x<3072 then (if x<1748 then 2 else 2) else (if x<3162 then 3 else 1))) else (if x<3252 then (if x<3222 then (if x<3192 then 0 else 3) else (if x<3228 then 1 else 2)) else (if x<3276 then (if x<3270 then 3 else 0) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6578 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6578 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6578 1582 4
  · have he : independentCachedBranchMembers6578.erase 1582=independentCachedBranchMembers6576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6576
  · have he : independentCachedBranchMembers6578.filter (independentCachedEdge 1582)=independentCachedBranchMembers6577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6577
def independentCachedBranchMembers6579 : Finset ℕ := ([12,18,36,48,66,72,132,144,192,222,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2560,2590,2614,2620,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6579 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6579 2560 5
  · have he : independentCachedBranchMembers6579.erase 2560=independentCachedBranchMembers6557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6557
  · have he : independentCachedBranchMembers6579.filter (independentCachedEdge 2560)=independentCachedBranchMembers6578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6578
def independentCachedBranchMembers6580 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6580 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6580 1706 6
  · have he : independentCachedBranchMembers6580.erase 1706=independentCachedBranchMembers6236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6236
  · have he : independentCachedBranchMembers6580.filter (independentCachedEdge 1706)=independentCachedBranchMembers6579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6579
def independentCachedBranchMembers6581 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2652,2674,2762,2772,2776,2792,3150,3158,3192,3274,3276,3282,3284,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6581 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6581 6 (fun x => (if x<2652 then (if x<1642 then (if x<250 then (if x<192 then (if x<80 then 0 else 1) else (if x<222 then 2 else 0)) else (if x<1626 then (if x<252 then 1 else 2) else (if x<1628 then 0 else 3))) else (if x<1746 then (if x<1734 then (if x<1652 then 3 else 4) else (if x<1740 then 3 else 0)) else (if x<1768 then (if x<1752 then 1 else 2) else (if x<1776 then 4 else 3)))) else (if x<3192 then (if x<2776 then (if x<2762 then (if x<2674 then 0 else 1) else (if x<2772 then 0 else 2)) else (if x<3150 then (if x<2792 then 1 else 2) else (if x<3158 then 0 else 4))) else (if x<3284 then (if x<3276 then (if x<3274 then 3 else 4) else (if x<3282 then 2 else 5)) else (if x<3298 then (if x<3288 then 3 else 0) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6582 : Finset ℕ := ([72,222,1626,1628,1642,1734,1740,1776,2674,2772,2776,2792,3158,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6582 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6582 5 (fun x => (if x<1776 then (if x<1628 then (if x<222 then 0 else (if x<1626 then 0 else 0)) else (if x<1734 then (if x<1642 then 1 else 1) else (if x<1740 then 1 else 0))) else (if x<2792 then (if x<2772 then (if x<2674 then 1 else 2) else (if x<2776 then 1 else 0)) else (if x<3274 then (if x<3158 then 2 else 2) else (if x<3276 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6583 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2652,2674,2762,2772,2776,2792,2800,3150,3158,3192,3274,3276,3282,3284,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6583 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6583 2800 5
  · have he : independentCachedBranchMembers6583.erase 2800=independentCachedBranchMembers6581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6581
  · have he : independentCachedBranchMembers6583.filter (independentCachedEdge 2800)=independentCachedBranchMembers6582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6582
def independentCachedBranchMembers6584 : Finset ℕ := ([80,192,222,250,1626,1734,1752,1776,2652,2792,3158,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6584 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6584 5 (fun x => (if x<1776 then (if x<250 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1734 then (if x<1626 then 1 else 0) else (if x<1752 then 2 else 1))) else (if x<3274 then (if x<2792 then (if x<2652 then 2 else 0) else (if x<3158 then 1 else 0)) else (if x<3288 then (if x<3284 then 1 else 2) else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6585 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2652,2668,2674,2762,2772,2776,2792,2800,3150,3158,3192,3274,3276,3282,3284,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6585 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6585 2668 5
  · have he : independentCachedBranchMembers6585.erase 2668=independentCachedBranchMembers6583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6583
  · have he : independentCachedBranchMembers6585.filter (independentCachedEdge 2668)=independentCachedBranchMembers6584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6584
def independentCachedBranchMembers6586 : Finset ℕ := ([192,252,1626,1652,1734,1740,1768,1776,2652,2674,2762,2776,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6586 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6586 5 (fun x => (if x<1776 then (if x<1652 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1740 then (if x<1734 then 1 else 1) else (if x<1768 then 0 else 1))) else (if x<2776 then (if x<2674 then (if x<2652 then 0 else 2) else (if x<2762 then 2 else 1)) else (if x<3284 then (if x<3276 then 0 else 2) else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6587 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2650,2652,2668,2674,2762,2772,2776,2792,2800,3150,3158,3192,3274,3276,3282,3284,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6587 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6587 2650 5
  · have he : independentCachedBranchMembers6587.erase 2650=independentCachedBranchMembers6585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6585
  · have he : independentCachedBranchMembers6587.filter (independentCachedEdge 2650)=independentCachedBranchMembers6586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6586
def independentCachedBranchMembers6588 : Finset ℕ := ([80,222,1626,1628,1652,1734,1746,1768,2650,2652,2674,2772,2792,3158,3192,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6588 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6588 5 (fun x => (if x<2674 then (if x<1734 then (if x<1626 then (if x<222 then 0 else 0) else (if x<1628 then 0 else (if x<1652 then 1 else 2))) else (if x<1768 then (if x<1746 then 1 else 2) else (if x<2650 then 1 else (if x<2652 then 3 else 0)))) else (if x<3274 then (if x<2792 then (if x<2772 then 2 else 2) else (if x<3158 then 3 else (if x<3192 then 0 else 1))) else (if x<3288 then (if x<3276 then 3 else 1) else (if x<3298 then 0 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6589 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2650,2652,2668,2674,2762,2772,2776,2792,2800,3150,3158,3192,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6589 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6589 3304 5
  · have he : independentCachedBranchMembers6589.erase 3304=independentCachedBranchMembers6587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6587
  · have he : independentCachedBranchMembers6589.filter (independentCachedEdge 3304)=independentCachedBranchMembers6588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6588
def independentCachedBranchMembers6590 : Finset ℕ := ([192,252,1626,1652,1734,1740,1768,1776,2650,2668,2772,2792,2800,3150,3158,3192,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6590 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6590 5 (fun x => (if x<2772 then (if x<1740 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1734 then 1 else 1))) else (if x<1776 then (if x<1768 then 0 else 1) else (if x<2650 then 0 else (if x<2668 then 2 else 2)))) else (if x<3192 then (if x<2800 then (if x<2792 then 0 else 0) else (if x<3150 then 2 else (if x<3158 then 2 else 1))) else (if x<3282 then (if x<3274 then 1 else 1) else (if x<3288 then 2 else (if x<3300 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6591 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2650,2652,2668,2674,2762,2772,2776,2792,2800,3150,3158,3162,3192,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6591 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6591 3162 5
  · have he : independentCachedBranchMembers6591.erase 3162=independentCachedBranchMembers6589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6589
  · have he : independentCachedBranchMembers6591.filter (independentCachedEdge 3162)=independentCachedBranchMembers6590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6590
end EntropyDesigns.QuadraticRefinement
