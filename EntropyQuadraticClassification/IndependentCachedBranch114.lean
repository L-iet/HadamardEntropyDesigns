/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch113
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6432 : Finset ℕ := ([72,132,144,1622,1628,1642,1678,1690,1702,1708,1714,1720,2638,2650,2668,2674,2710,2716,2730,2740,3150,3162,3174,3192,3222,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6432 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6432 5 (fun x => (if x<2668 then (if x<1690 then (if x<1622 then (if x<132 then 0 else (if x<144 then 0 else 1)) else (if x<1642 then (if x<1628 then 2 else 3) else (if x<1678 then 0 else 2))) else (if x<1714 then (if x<1702 then 1 else (if x<1708 then 0 else 3)) else (if x<2638 then (if x<1720 then 2 else 4) else (if x<2650 then 2 else 0)))) else (if x<3162 then (if x<2716 then (if x<2674 then 1 else (if x<2710 then 2 else 0)) else (if x<2740 then (if x<2730 then 1 else 2) else (if x<3150 then 4 else 4))) else (if x<3222 then (if x<3174 then 3 else (if x<3192 then 1 else 0)) else (if x<3242 then (if x<3228 then 1 else 3) else (if x<3252 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6433 : Finset ℕ := ([72,1628,1678,1690,1702,1714,2668,2710,2730,3192,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6433 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6433 4 (fun x => (if x<2668 then (if x<1690 then (if x<1628 then 0 else (if x<1678 then 0 else 1)) else (if x<1702 then 2 else (if x<1714 then 2 else 1))) else (if x<3192 then (if x<2710 then 0 else (if x<2730 then 1 else 1)) else (if x<3222 then 0 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6434 : Finset ℕ := ([66,72,132,144,1622,1628,1642,1678,1690,1702,1708,1714,1720,2638,2650,2668,2674,2710,2716,2730,2740,3150,3162,3174,3192,3222,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6434 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6434 66 4
  · have he : independentCachedBranchMembers6434.erase 66=independentCachedBranchMembers6432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6432
  · have he : independentCachedBranchMembers6434.filter (independentCachedEdge 66)=independentCachedBranchMembers6433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6433
def independentCachedBranchMembers6435 : Finset ℕ := ([144,1628,1690,1702,1720,2638,2668,2674,2710,2730,2740,3162,3174,3192,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6435 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6435 4 (fun x => (if x<2674 then (if x<1702 then (if x<1628 then 0 else (if x<1690 then 1 else 0)) else (if x<2638 then (if x<1720 then 2 else 1) else (if x<2668 then 1 else 0))) else (if x<3162 then (if x<2730 then (if x<2710 then 3 else 2) else (if x<2740 then 1 else 3)) else (if x<3192 then (if x<3174 then 3 else 0) else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6436 : Finset ℕ := ([1690,1720,2674,2730,3174,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6436 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6436 3 (fun x => (if x<2730 then (if x<1720 then 0 else (if x<2674 then 1 else 2)) else (if x<3174 then 0 else (if x<3228 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6437 : Finset ℕ := ([72,144,1628,1690,1702,1720,2638,2668,2674,2710,2730,2740,3162,3174,3192,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6437 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6437 72 3
  · have he : independentCachedBranchMembers6437.erase 72=independentCachedBranchMembers6435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6435
  · have he : independentCachedBranchMembers6437.filter (independentCachedEdge 72)=independentCachedBranchMembers6436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6436
def independentCachedBranchMembers6438 : Finset ℕ := ([66,72,132,144,1622,1628,1642,1678,1690,1702,1708,1714,1720,2638,2650,2668,2674,2710,2716,2730,2740,3150,3162,3174,3186,3192,3222,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6438 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6438 3186 4
  · have he : independentCachedBranchMembers6438.erase 3186=independentCachedBranchMembers6434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6434
  · have he : independentCachedBranchMembers6438.filter (independentCachedEdge 3186)=independentCachedBranchMembers6437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6437
def independentCachedBranchMembers6439 : Finset ℕ := ([132,1622,1678,1702,1720,2650,2668,2674,2716,2730,2740,3150,3174,3192,3222] : List ℕ).toFinset
theorem independentCachedBranchBound6439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6439 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6439 4 (fun x => (if x<2674 then (if x<1702 then (if x<1622 then 0 else (if x<1678 then 1 else 0)) else (if x<2650 then (if x<1720 then 1 else 2) else (if x<2668 then 1 else 3))) else (if x<3150 then (if x<2730 then (if x<2716 then 0 else 2) else (if x<2740 then 1 else 3)) else (if x<3192 then (if x<3174 then 3 else 2) else (if x<3222 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6440 : Finset ℕ := ([1678,1702,2668,2730,3192,3222] : List ℕ).toFinset
theorem independentCachedBranchBound6440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6440 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6440 3 (fun x => (if x<2730 then (if x<1702 then 0 else (if x<2668 then 1 else 2)) else (if x<3192 then 0 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6441 : Finset ℕ := ([66,132,1622,1678,1702,1720,2650,2668,2674,2716,2730,2740,3150,3174,3192,3222] : List ℕ).toFinset
theorem independentCachedBranchBound6441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6441 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6441 66 3
  · have he : independentCachedBranchMembers6441.erase 66=independentCachedBranchMembers6439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6439
  · have he : independentCachedBranchMembers6441.filter (independentCachedEdge 66)=independentCachedBranchMembers6440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6440
def independentCachedBranchMembers6442 : Finset ℕ := ([66,72,132,144,1622,1628,1642,1678,1690,1702,1708,1714,1720,2638,2650,2668,2674,2710,2716,2730,2740,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6442 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6442 3180 4
  · have he : independentCachedBranchMembers6442.erase 3180=independentCachedBranchMembers6438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6438
  · have he : independentCachedBranchMembers6442.filter (independentCachedEdge 3180)=independentCachedBranchMembers6441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6441
def independentCachedBranchMembers6443 : Finset ℕ := ([66,72,132,144,1622,1628,1678,1690,2638,2650,2710,2716,3150,3162,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6443 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6443 4 (fun x => (if x<2638 then (if x<1622 then (if x<132 then (if x<72 then 0 else 1) else (if x<144 then 0 else 1)) else (if x<1678 then (if x<1628 then 2 else 3) else (if x<1690 then 2 else 3))) else (if x<3150 then (if x<2710 then (if x<2650 then 1 else 0) else (if x<2716 then 1 else 0)) else (if x<3222 then (if x<3162 then 2 else 3) else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6444 : Finset ℕ := ([66,72,132,144,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,2638,2650,2668,2674,2710,2716,2730,2740,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6444 1652 4
  · have he : independentCachedBranchMembers6444.erase 1652=independentCachedBranchMembers6442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6442
  · have he : independentCachedBranchMembers6444.filter (independentCachedEdge 1652)=independentCachedBranchMembers6443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6443
def independentCachedBranchMembers6445 : Finset ℕ := ([36,48,66,72,132,144,192,222,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6445 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6445 192 5
  · have he : independentCachedBranchMembers6445.erase 192=independentCachedBranchMembers6431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6431
  · have he : independentCachedBranchMembers6445.filter (independentCachedEdge 192)=independentCachedBranchMembers6444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6444
def independentCachedBranchMembers6446 : Finset ℕ := ([252,1582,1628,1642,1652,1678,1720,1748,1762,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6446 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6446 5 (fun x => (if x<2740 then (if x<1678 then (if x<1628 then (if x<1582 then 0 else 1) else (if x<1642 then 0 else (if x<1652 then 2 else 1))) else (if x<1762 then (if x<1720 then 2 else (if x<1748 then 0 else 3)) else (if x<2716 then 1 else (if x<2730 then 0 else 1)))) else (if x<3150 then (if x<2776 then (if x<2758 then 3 else 3) else (if x<2800 then 3 else (if x<3132 then 1 else 0))) else (if x<3228 then (if x<3174 then 2 else (if x<3192 then 4 else 2)) else (if x<3242 then 2 else (if x<3312 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6447 : Finset ℕ := ([1628,1652,1678,1762,2730,2758,3132,3192,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6447 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6447 4 (fun x => (if x<2730 then (if x<1678 then (if x<1652 then 0 else 1) else (if x<1762 then 0 else 1)) else (if x<3132 then (if x<2758 then 0 else 2) else (if x<3192 then 1 else (if x<3242 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6448 : Finset ℕ := ([144,252,1582,1628,1642,1652,1678,1720,1748,1762,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6448 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6448 144 4
  · have he : independentCachedBranchMembers6448.erase 144=independentCachedBranchMembers6446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6446
  · have he : independentCachedBranchMembers6448.filter (independentCachedEdge 144)=independentCachedBranchMembers6447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6447
def independentCachedBranchMembers6449 : Finset ℕ := ([1582,1628,1678,1762,2730,2740,2758,2776,3132,3150,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6449 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6449 4 (fun x => (if x<2758 then (if x<1762 then (if x<1628 then 0 else (if x<1678 then 0 else 1)) else (if x<2730 then 1 else (if x<2740 then 0 else 2))) else (if x<3150 then (if x<2776 then 1 else (if x<3132 then 0 else 2)) else (if x<3228 then 2 else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6450 : Finset ℕ := ([144,252,1582,1628,1642,1652,1678,1720,1748,1762,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6450 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6450 3252 4
  · have he : independentCachedBranchMembers6450.erase 3252=independentCachedBranchMembers6448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6448
  · have he : independentCachedBranchMembers6450.filter (independentCachedEdge 3252)=independentCachedBranchMembers6449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6449
def independentCachedBranchMembers6451 : Finset ℕ := ([252,1652,1748,1762,2740,2758,2800,3132,3150,3192,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6451 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6451 4 (fun x => (if x<2800 then (if x<1762 then (if x<1652 then 0 else (if x<1748 then 0 else 1)) else (if x<2740 then 1 else (if x<2758 then 0 else 1))) else (if x<3192 then (if x<3132 then 1 else (if x<3150 then 0 else 2)) else (if x<3228 then 2 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6452 : Finset ℕ := ([144,252,1582,1628,1642,1652,1678,1720,1748,1762,2638,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6452 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6452 2638 4
  · have he : independentCachedBranchMembers6452.erase 2638=independentCachedBranchMembers6450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6450
  · have he : independentCachedBranchMembers6452.filter (independentCachedEdge 2638)=independentCachedBranchMembers6451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6451
def independentCachedBranchMembers6453 : Finset ℕ := ([144,1642,1678,1748,2716,2740,2758,3132,3150,3174,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6453 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6453 4 (fun x => (if x<2758 then (if x<1748 then (if x<1642 then 0 else (if x<1678 then 0 else 1)) else (if x<2716 then 1 else (if x<2740 then 0 else 2))) else (if x<3174 then (if x<3132 then 1 else (if x<3150 then 2 else 2)) else (if x<3242 then 0 else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6454 : Finset ℕ := ([144,252,1582,1628,1642,1652,1678,1720,1748,1762,2620,2638,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6454 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6454 2620 4
  · have he : independentCachedBranchMembers6454.erase 2620=independentCachedBranchMembers6452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6452
  · have he : independentCachedBranchMembers6454.filter (independentCachedEdge 2620)=independentCachedBranchMembers6453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6453
def independentCachedBranchMembers6455 : Finset ℕ := ([144,252,1642,1652,1678,1762,2716,2800,3174,3192,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6455 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6455 4 (fun x => (if x<2716 then (if x<1652 then (if x<252 then 0 else (if x<1642 then 0 else 1)) else (if x<1678 then 1 else (if x<1762 then 2 else 2))) else (if x<3192 then (if x<2800 then 0 else (if x<3174 then 0 else 1)) else (if x<3228 then 1 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6456 : Finset ℕ := ([144,252,1582,1628,1642,1652,1678,1720,1738,1748,1762,2620,2638,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6456 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6456 1738 4
  · have he : independentCachedBranchMembers6456.erase 1738=independentCachedBranchMembers6454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6454
  · have he : independentCachedBranchMembers6456.filter (independentCachedEdge 1738)=independentCachedBranchMembers6455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6455
def independentCachedBranchMembers6457 : Finset ℕ := ([252,1582,1628,1652,1678,1748,2730,2776,2800,3192,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6457 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6457 4 (fun x => (if x<2730 then (if x<1652 then (if x<1582 then 0 else (if x<1628 then 1 else 0)) else (if x<1678 then 1 else (if x<1748 then 2 else 2))) else (if x<3192 then (if x<2776 then 1 else (if x<2800 then 0 else 1)) else (if x<3242 then 0 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6458 : Finset ℕ := ([66,144,252,1582,1628,1642,1652,1678,1720,1738,1748,1762,2620,2638,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6458 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6458 66 4
  · have he : independentCachedBranchMembers6458.erase 66=independentCachedBranchMembers6456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6456
  · have he : independentCachedBranchMembers6458.filter (independentCachedEdge 66)=independentCachedBranchMembers6457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6457
def independentCachedBranchMembers6459 : Finset ℕ := ([144,1582,1628,1642,1748,1762,2716,2730,2776,3174,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6459 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6459 4 (fun x => (if x<2716 then (if x<1642 then (if x<1582 then 0 else (if x<1628 then 0 else 1)) else (if x<1748 then 1 else (if x<1762 then 2 else 2))) else (if x<3174 then (if x<2730 then 1 else (if x<2776 then 1 else 0)) else (if x<3228 then 0 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6460 : Finset ℕ := ([48,66,144,252,1582,1628,1642,1652,1678,1720,1738,1748,1762,2620,2638,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6460 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6460 48 4
  · have he : independentCachedBranchMembers6460.erase 48=independentCachedBranchMembers6458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6458
  · have he : independentCachedBranchMembers6460.filter (independentCachedEdge 48)=independentCachedBranchMembers6459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6459
def independentCachedBranchMembers6461 : Finset ℕ := ([66,1642,1652,1678,1762,2620,2638,2730,2740,2758,2776,3174,3192,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6461 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6461 4 (fun x => (if x<2730 then (if x<1678 then (if x<1642 then 0 else (if x<1652 then 0 else 1)) else (if x<2620 then (if x<1762 then 2 else 1) else (if x<2638 then 1 else 0))) else (if x<3174 then (if x<2758 then (if x<2740 then 1 else 3) else (if x<2776 then 2 else 3)) else (if x<3228 then (if x<3192 then 0 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6462 : Finset ℕ := ([1642,1762,2730,2776,3174,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6462 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6462 3 (fun x => (if x<2776 then (if x<1762 then 0 else (if x<2730 then 1 else 0)) else (if x<3174 then 2 else (if x<3228 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6463 : Finset ℕ := ([48,66,1642,1652,1678,1762,2620,2638,2730,2740,2758,2776,3174,3192,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6463 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6463 48 3
  · have he : independentCachedBranchMembers6463.erase 48=independentCachedBranchMembers6461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6461
  · have he : independentCachedBranchMembers6463.filter (independentCachedEdge 48)=independentCachedBranchMembers6462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6462
end EntropyDesigns.QuadraticRefinement
