/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch116
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6528 : Finset ℕ := ([48,72,132,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6528 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6528 3072 4
  · have he : independentCachedBranchMembers6528.erase 3072=independentCachedBranchMembers6526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6526
  · have he : independentCachedBranchMembers6528.filter (independentCachedEdge 3072)=independentCachedBranchMembers6527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6527
def independentCachedBranchMembers6529 : Finset ℕ := ([48,252,1594,1708,1714,1768,2614,2668,2674,2788,3132,3174,3192,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6529 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6529 4 (fun x => (if x<2674 then (if x<1714 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1708 then 1 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2668 then 2 else 2))) else (if x<3192 then (if x<3132 then (if x<2788 then 1 else 1) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6530 : Finset ℕ := ([48,72,132,222,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6530 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6530 222 4
  · have he : independentCachedBranchMembers6530.erase 222=independentCachedBranchMembers6528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6528
  · have he : independentCachedBranchMembers6530.filter (independentCachedEdge 222)=independentCachedBranchMembers6529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6529
def independentCachedBranchMembers6531 : Finset ℕ := ([72,132,1628,1678,1708,1714,2638,2668,2674,2716,3162,3174,3192,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6531 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6531 4 (fun x => (if x<2674 then (if x<1708 then (if x<1628 then (if x<132 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3192 then (if x<3162 then (if x<2716 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3222 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6532 : Finset ℕ := ([48,72,132,192,222,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6532 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6532 192 4
  · have he : independentCachedBranchMembers6532.erase 192=independentCachedBranchMembers6530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6530
  · have he : independentCachedBranchMembers6532.filter (independentCachedEdge 192)=independentCachedBranchMembers6531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6531
def independentCachedBranchMembers6533 : Finset ℕ := ([48,252,1628,1678,1738,1748,2638,2716,2758,2776,3132,3174,3192,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6533 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6533 4 (fun x => (if x<2758 then (if x<1738 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1748 then 2 else 2) else (if x<2716 then 1 else 1))) else (if x<3192 then (if x<3132 then (if x<2776 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6534 : Finset ℕ := ([18,48,72,132,192,222,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6534 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6534 18 4
  · have he : independentCachedBranchMembers6534.erase 18=independentCachedBranchMembers6532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6532
  · have he : independentCachedBranchMembers6534.filter (independentCachedEdge 18)=independentCachedBranchMembers6533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6533
def independentCachedBranchMembers6535 : Finset ℕ := ([72,132,1594,1738,1748,1768,2614,2758,2776,2788,3162,3174,3192,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6535 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6535 4 (fun x => (if x<2776 then (if x<1748 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1738 then 1 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2758 then 1 else 1))) else (if x<3192 then (if x<3162 then (if x<2788 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3222 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6536 : Finset ℕ := ([12,18,48,72,132,192,222,252,1594,1628,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2716,2758,2776,2788,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6536 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6536 12 4
  · have he : independentCachedBranchMembers6536.erase 12=independentCachedBranchMembers6534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6534
  · have he : independentCachedBranchMembers6536.filter (independentCachedEdge 12)=independentCachedBranchMembers6535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6535
def independentCachedBranchMembers6537 : Finset ℕ := ([12,18,36,48,66,72,132,144,192,222,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6537 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6537 2662 5
  · have he : independentCachedBranchMembers6537.erase 2662=independentCachedBranchMembers6517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6517
  · have he : independentCachedBranchMembers6537.filter (independentCachedEdge 2662)=independentCachedBranchMembers6536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6536
def independentCachedBranchMembers6538 : Finset ℕ := ([132,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3102,3180,3186,3192,3242,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6538 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6538 5 (fun x => (if x<2650 then (if x<1714 then (if x<1652 then (if x<252 then 0 else (if x<1642 then 0 else 1)) else (if x<1702 then 1 else (if x<1708 then 1 else 0))) else (if x<1748 then (if x<1720 then 2 else (if x<1738 then 1 else 2)) else (if x<2620 then (if x<2614 then 0 else 2) else (if x<2638 then 3 else 2)))) else (if x<3186 then (if x<2788 then (if x<2710 then 3 else (if x<2716 then 3 else 0)) else (if x<3102 then (if x<2800 then 0 else 3) else (if x<3180 then 3 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3242 then 1 else 1)) else (if x<3276 then (if x<3270 then 0 else 4) else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6539 : Finset ℕ := ([1652,1708,1720,1748,2620,2716,2788,2800,3102,3186,3242,3270] : List ℕ).toFinset
theorem independentCachedBranchBound6539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6539 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6539 4 (fun x => (if x<2788 then (if x<1748 then (if x<1708 then 0 else (if x<1720 then 0 else 1)) else (if x<2620 then 1 else (if x<2716 then 0 else 1))) else (if x<3186 then (if x<2800 then 0 else (if x<3102 then 1 else 2)) else (if x<3242 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6540 : Finset ℕ := ([72,132,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3102,3180,3186,3192,3242,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6540 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6540 72 4
  · have he : independentCachedBranchMembers6540.erase 72=independentCachedBranchMembers6538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6538
  · have he : independentCachedBranchMembers6540.filter (independentCachedEdge 72)=independentCachedBranchMembers6539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6539
def independentCachedBranchMembers6541 : Finset ℕ := ([1642,1702,1708,1748,2650,2710,2716,2788,3102,3180,3242,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6541 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6541 4 (fun x => (if x<2716 then (if x<1748 then (if x<1702 then 0 else (if x<1708 then 0 else 1)) else (if x<2650 then 1 else (if x<2710 then 0 else 0))) else (if x<3180 then (if x<2788 then 1 else (if x<3102 then 1 else 2)) else (if x<3242 then 2 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6542 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3102,3180,3186,3192,3242,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6542 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6542 48 4
  · have he : independentCachedBranchMembers6542.erase 48=independentCachedBranchMembers6540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6540
  · have he : independentCachedBranchMembers6542.filter (independentCachedEdge 48)=independentCachedBranchMembers6541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6541
def independentCachedBranchMembers6543 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,2614,2638,2716,2788,3180,3186,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6543 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6543 4 (fun x => (if x<2614 then (if x<1642 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3180 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6544 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3102,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6544 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6544 3282 4
  · have he : independentCachedBranchMembers6544.erase 3282=independentCachedBranchMembers6542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6542
  · have he : independentCachedBranchMembers6544.filter (independentCachedEdge 3282)=independentCachedBranchMembers6543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6543
def independentCachedBranchMembers6545 : Finset ℕ := ([48,72,132,252,1708,1714,1738,1748,2620,2650,2710,2800,3180,3186,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6545 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6545 4 (fun x => (if x<2620 then (if x<1708 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3180 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6546 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6546 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6546 3174 4
  · have he : independentCachedBranchMembers6546.erase 3174=independentCachedBranchMembers6544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6544
  · have he : independentCachedBranchMembers6546.filter (independentCachedEdge 3174)=independentCachedBranchMembers6545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6545
def independentCachedBranchMembers6547 : Finset ℕ := ([1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound6547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6547 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6547 4 (fun x => (if x<2614 then (if x<1714 then (if x<1702 then (if x<1652 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1738 then (if x<1720 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<2710 then (if x<2638 then (if x<2620 then 2 else 3) else (if x<2650 then 2 else 3)) else (if x<2788 then (if x<2716 then 3 else 2) else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6548 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6548 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6548 3072 4
  · have he : independentCachedBranchMembers6548.erase 3072=independentCachedBranchMembers6546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6546
  · have he : independentCachedBranchMembers6548.filter (independentCachedEdge 3072)=independentCachedBranchMembers6547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6547
def independentCachedBranchMembers6549 : Finset ℕ := ([72,252,1642,1708,1720,1738,2620,2638,2650,2716,3102,3180,3192,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6549 4 (fun x => (if x<2650 then (if x<1720 then (if x<1642 then (if x<252 then 0 else 0) else (if x<1708 then 1 else 1)) else (if x<2620 then (if x<1738 then 2 else 2) else (if x<2638 then 2 else 2))) else (if x<3192 then (if x<3102 then (if x<2716 then 1 else 1) else (if x<3180 then 3 else 0)) else (if x<3276 then (if x<3242 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6550 : Finset ℕ := ([48,72,132,246,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6550 246 4
  · have he : independentCachedBranchMembers6550.erase 246=independentCachedBranchMembers6548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6548
  · have he : independentCachedBranchMembers6550.filter (independentCachedEdge 246)=independentCachedBranchMembers6549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6549
def independentCachedBranchMembers6551 : Finset ℕ := ([48,132,1652,1702,1708,1738,2614,2620,2650,2788,3102,3186,3192,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6551 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6551 4 (fun x => (if x<2650 then (if x<1708 then (if x<1652 then (if x<132 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2614 then (if x<1738 then 2 else 2) else (if x<2620 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2788 then 2 else 1) else (if x<3186 then 3 else 0)) else (if x<3270 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6552 : Finset ℕ := ([48,72,132,144,246,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6552 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6552 144 4
  · have he : independentCachedBranchMembers6552.erase 144=independentCachedBranchMembers6550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6550
  · have he : independentCachedBranchMembers6552.filter (independentCachedEdge 144)=independentCachedBranchMembers6551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6551
def independentCachedBranchMembers6553 : Finset ℕ := ([72,252,1652,1702,1714,1748,2614,2710,2788,2800,3102,3180,3192,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6553 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6553 4 (fun x => (if x<2788 then (if x<1714 then (if x<1652 then (if x<252 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2614 then (if x<1748 then 2 else 2) else (if x<2710 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2800 then 1 else 2) else (if x<3180 then 3 else 0)) else (if x<3276 then (if x<3242 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6554 : Finset ℕ := ([48,66,72,132,144,246,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6554 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6554 66 4
  · have he : independentCachedBranchMembers6554.erase 66=independentCachedBranchMembers6552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6552
  · have he : independentCachedBranchMembers6554.filter (independentCachedEdge 66)=independentCachedBranchMembers6553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6553
def independentCachedBranchMembers6555 : Finset ℕ := ([48,132,1642,1714,1720,1748,2638,2710,2716,2800,3102,3186,3192,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6555 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6555 4 (fun x => (if x<2716 then (if x<1720 then (if x<1642 then (if x<132 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<2638 then (if x<1748 then 2 else 2) else (if x<2710 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2800 then 2 else 2) else (if x<3186 then 3 else 0)) else (if x<3270 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6556 : Finset ℕ := ([36,48,66,72,132,144,246,252,1642,1652,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2710,2716,2788,2800,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6556 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6556 36 4
  · have he : independentCachedBranchMembers6556.erase 36=independentCachedBranchMembers6554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6554
  · have he : independentCachedBranchMembers6556.filter (independentCachedEdge 36)=independentCachedBranchMembers6555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6555
def independentCachedBranchMembers6557 : Finset ℕ := ([12,18,36,48,66,72,132,144,192,222,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2590,2614,2620,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6557 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6557 2590 5
  · have he : independentCachedBranchMembers6557.erase 2590=independentCachedBranchMembers6537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6537
  · have he : independentCachedBranchMembers6557.filter (independentCachedEdge 2590)=independentCachedBranchMembers6556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6556
def independentCachedBranchMembers6558 : Finset ℕ := ([1628,1642,1652,1678,1702,1708,1714,1720,1738,1748,1768,3072,3126,3132,3150,3162,3180,3186,3192,3222,3228,3242,3252,3270,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6558 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6558 5 (fun x => (if x<3150 then (if x<1720 then (if x<1678 then (if x<1642 then 0 else (if x<1652 then 0 else 1)) else (if x<1708 then (if x<1702 then 0 else 1) else (if x<1714 then 2 else 2))) else (if x<1768 then (if x<1738 then 0 else (if x<1748 then 2 else 2)) else (if x<3126 then (if x<3072 then 1 else 3) else (if x<3132 then 1 else 3)))) else (if x<3242 then (if x<3186 then (if x<3162 then 0 else (if x<3180 then 3 else 4)) else (if x<3222 then (if x<3192 then 4 else 0) else (if x<3228 then 3 else 0))) else (if x<3276 then (if x<3252 then 0 else (if x<3270 then 2 else 4)) else (if x<3300 then (if x<3288 then 2 else 4) else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6559 : Finset ℕ := ([1642,1714,1720,1748,3072,3150,3180,3222,3228,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6559 4 (fun x => (if x<3180 then (if x<1748 then (if x<1714 then 0 else (if x<1720 then 0 else 1)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3252 then (if x<3222 then 2 else (if x<3228 then 0 else 1)) else (if x<3288 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
