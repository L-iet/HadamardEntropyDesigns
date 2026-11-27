/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch87
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5600 : Finset ℕ := ([48,72,1650,1652,1702,1714,1738,1752,2614,2638,2650,2652,2702,2714,2786,2788,2800,3102,3174,3186,3188,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5600 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5600 2788 4
  · have he : independentCachedBranchMembers5600.erase 2788=independentCachedBranchMembers5598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5598
  · have he : independentCachedBranchMembers5600.filter (independentCachedEdge 2788)=independentCachedBranchMembers5599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5599
def independentCachedBranchMembers5601 : Finset ℕ := ([48,72,1652,1702,1714,1738,2652,2702,2714,2786,3188,3238,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5601 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5601 4 (fun x => (if x<2702 then (if x<1702 then (if x<72 then 0 else (if x<1652 then 0 else 1)) else (if x<1738 then (if x<1714 then 1 else 0) else (if x<2652 then 0 else 1))) else (if x<3188 then (if x<2714 then 1 else (if x<2786 then 2 else 2)) else (if x<3250 then (if x<3238 then 3 else 3) else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5602 : Finset ℕ := ([48,72,1650,1652,1702,1714,1738,1752,2614,2638,2650,2652,2702,2714,2716,2786,2788,2800,3102,3174,3186,3188,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5602 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5602 2716 4
  · have he : independentCachedBranchMembers5602.erase 2716=independentCachedBranchMembers5600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5600
  · have he : independentCachedBranchMembers5602.filter (independentCachedEdge 2716)=independentCachedBranchMembers5601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5601
def independentCachedBranchMembers5603 : Finset ℕ := ([40,48,72,80,130,132,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5603 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5603 40 5
  · have he : independentCachedBranchMembers5603.erase 40=independentCachedBranchMembers5593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5593
  · have he : independentCachedBranchMembers5603.filter (independentCachedEdge 40)=independentCachedBranchMembers5602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5602
def independentCachedBranchMembers5604 : Finset ℕ := ([40,72,250,252,1642,1644,1720,1738,1752,2606,2618,2620,2638,2650,2652,2714,2716,2792,3102,3178,3180,3192,3242,3244,3256,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5604 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5604 5 (fun x => (if x<2652 then (if x<1738 then (if x<252 then (if x<72 then 0 else (if x<250 then 1 else 0)) else (if x<1644 then (if x<1642 then 1 else 0) else (if x<1720 then 1 else 0))) else (if x<2618 then (if x<1752 then 2 else (if x<2606 then 1 else 3)) else (if x<2638 then (if x<2620 then 0 else 2) else (if x<2650 then 2 else 3)))) else (if x<3192 then (if x<2792 then (if x<2714 then 1 else (if x<2716 then 2 else 3)) else (if x<3178 then (if x<3102 then 0 else 3) else (if x<3180 then 3 else 4))) else (if x<3256 then (if x<3242 then 0 else (if x<3244 then 0 else 3)) else (if x<3276 then (if x<3274 then 4 else 4) else (if x<3288 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5605 : Finset ℕ := ([72,250,1644,1720,2618,2638,2652,2714,3102,3178,3192,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5605 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5605 4 (fun x => (if x<2714 then (if x<1720 then (if x<250 then 0 else (if x<1644 then 0 else 1)) else (if x<2638 then (if x<2618 then 1 else 2) else (if x<2652 then 1 else 2))) else (if x<3192 then (if x<3102 then 1 else (if x<3178 then 2 else 0)) else (if x<3274 then (if x<3244 then 2 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5606 : Finset ℕ := ([40,72,250,252,1642,1644,1708,1720,1738,1752,2606,2618,2620,2638,2650,2652,2714,2716,2792,3102,3178,3180,3192,3242,3244,3256,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5606 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5606 1708 4
  · have he : independentCachedBranchMembers5606.erase 1708=independentCachedBranchMembers5604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5604
  · have he : independentCachedBranchMembers5606.filter (independentCachedEdge 1708)=independentCachedBranchMembers5605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5605
def independentCachedBranchMembers5607 : Finset ℕ := ([40,72,250,252,1642,1644,1720,1752,2606,2638,2714,2716,3178,3180,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5607 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5607 4 (fun x => (if x<2606 then (if x<1642 then (if x<250 then (if x<72 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1720 then (if x<1644 then 0 else 1) else (if x<1752 then 0 else 1))) else (if x<3178 then (if x<2714 then (if x<2638 then 2 else 3) else (if x<2716 then 2 else 3)) else (if x<3256 then (if x<3180 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5608 : Finset ℕ := ([40,72,250,252,1642,1644,1708,1720,1738,1752,2606,2618,2620,2638,2650,2652,2702,2714,2716,2792,3102,3178,3180,3192,3242,3244,3256,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5608 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5608 2702 4
  · have he : independentCachedBranchMembers5608.erase 2702=independentCachedBranchMembers5606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5606
  · have he : independentCachedBranchMembers5608.filter (independentCachedEdge 2702)=independentCachedBranchMembers5607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5607
def independentCachedBranchMembers5609 : Finset ℕ := ([40,48,72,80,130,132,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5609 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5609 246 5
  · have he : independentCachedBranchMembers5609.erase 246=independentCachedBranchMembers5603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5603
  · have he : independentCachedBranchMembers5609.filter (independentCachedEdge 246)=independentCachedBranchMembers5608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5608
def independentCachedBranchMembers5610 : Finset ℕ := ([48,80,130,132,1650,1652,1702,1708,1734,1738,2614,2618,2620,2646,2650,2652,2702,2786,2788,2792,3102,3186,3188,3192,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5610 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5610 5 (fun x => (if x<2652 then (if x<1708 then (if x<132 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1652 then (if x<1650 then 1 else 1) else (if x<1702 then 0 else 1))) else (if x<2618 then (if x<1738 then (if x<1734 then 2 else 0) else (if x<2614 then 2 else 3)) else (if x<2646 then (if x<2620 then 4 else 0) else (if x<2650 then 4 else 1)))) else (if x<3188 then (if x<2788 then (if x<2702 then 3 else (if x<2786 then 0 else 4)) else (if x<3102 then (if x<2792 then 3 else 2) else (if x<3186 then 3 else 4))) else (if x<3244 then (if x<3238 then (if x<3192 then 3 else 0) else (if x<3242 then 3 else 2)) else (if x<3274 then (if x<3270 then 1 else 4) else (if x<3276 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5611 : Finset ℕ := ([40,48,72,80,130,132,144,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5611 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5611 144 5
  · have he : independentCachedBranchMembers5611.erase 144=independentCachedBranchMembers5609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5609
  · have he : independentCachedBranchMembers5611.filter (independentCachedEdge 144)=independentCachedBranchMembers5610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5610
def independentCachedBranchMembers5612 : Finset ℕ := ([72,80,130,252,1644,1652,1702,1714,1748,1752,2606,2614,2618,2652,2702,2710,2714,2788,2792,2800,3102,3180,3188,3192,3238,3242,3250,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5612 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5612 5 (fun x => (if x<2710 then (if x<1714 then (if x<252 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1652 then (if x<1644 then 1 else 0) else (if x<1702 then 1 else 0))) else (if x<2614 then (if x<1752 then (if x<1748 then 2 else 2) else (if x<2606 then 1 else 3)) else (if x<2652 then (if x<2618 then 4 else 2) else (if x<2702 then 0 else 4)))) else (if x<3188 then (if x<2792 then (if x<2714 then 0 else (if x<2788 then 3 else 4)) else (if x<3102 then (if x<2800 then 3 else 1) else (if x<3180 then 3 else 3))) else (if x<3250 then (if x<3238 then (if x<3192 then 4 else 0) else (if x<3242 then 4 else 2)) else (if x<3284 then (if x<3276 then 0 else 2) else (if x<3288 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5613 : Finset ℕ := ([40,48,66,72,80,130,132,144,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5613 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5613 66 5
  · have he : independentCachedBranchMembers5613.erase 66=independentCachedBranchMembers5611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5611
  · have he : independentCachedBranchMembers5613.filter (independentCachedEdge 66)=independentCachedBranchMembers5612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5612
def independentCachedBranchMembers5614 : Finset ℕ := ([40,48,132,250,1642,1650,1714,1720,1734,1748,2618,2638,2646,2652,2702,2710,2716,2786,2792,2800,3102,3178,3186,3192,3242,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5614 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5614 5 (fun x => (if x<2710 then (if x<1720 then (if x<250 then (if x<48 then 0 else (if x<132 then 1 else 0)) else (if x<1650 then (if x<1642 then 1 else 0) else (if x<1714 then 1 else 2))) else (if x<2638 then (if x<1748 then (if x<1734 then 1 else 0) else (if x<2618 then 2 else 0)) else (if x<2652 then (if x<2646 then 3 else 4) else (if x<2702 then 2 else 4)))) else (if x<3186 then (if x<2792 then (if x<2716 then 0 else (if x<2786 then 3 else 4)) else (if x<3102 then (if x<2800 then 3 else 1) else (if x<3178 then 3 else 3))) else (if x<3256 then (if x<3242 then (if x<3192 then 4 else 0) else (if x<3250 then 2 else 1)) else (if x<3276 then (if x<3270 then 3 else 4) else (if x<3284 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5615 : Finset ℕ := ([36,40,48,66,72,80,130,132,144,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5615 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5615 36 5
  · have he : independentCachedBranchMembers5615.erase 36=independentCachedBranchMembers5613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5613
  · have he : independentCachedBranchMembers5615.filter (independentCachedEdge 36)=independentCachedBranchMembers5614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5614
def independentCachedBranchMembers5616 : Finset ℕ := ([48,80,144,246,250,252,1650,1652,1714,1720,1748,1752,2614,2618,2646,2652,2714,2716,2800,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5616 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5616 5 (fun x => (if x<2646 then (if x<1652 then (if x<246 then (if x<80 then 0 else (if x<144 then 1 else 2)) else (if x<252 then (if x<250 then 0 else 1) else (if x<1650 then 2 else 0))) else (if x<1748 then (if x<1714 then 3 else (if x<1720 then 3 else 2)) else (if x<2614 then (if x<1752 then 2 else 1) else (if x<2618 then 0 else 4)))) else (if x<3188 then (if x<2716 then (if x<2652 then 4 else (if x<2714 then 3 else 3)) else (if x<3102 then (if x<2800 then 2 else 0) else (if x<3186 then 4 else 4))) else (if x<3256 then (if x<3250 then (if x<3192 then 0 else 1) else (if x<3252 then 0 else 2)) else (if x<3284 then (if x<3282 then 4 else 1) else (if x<3288 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5617 : Finset ℕ := ([48,80,250,252,1650,1652,1720,1752,2614,2646,2714,2716,3186,3188,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5617 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5617 4 (fun x => (if x<2614 then (if x<1650 then (if x<250 then (if x<80 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1720 then (if x<1652 then 0 else 1) else (if x<1752 then 0 else 1))) else (if x<3186 then (if x<2714 then (if x<2646 then 2 else 3) else (if x<2716 then 2 else 3)) else (if x<3256 then (if x<3188 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5618 : Finset ℕ := ([48,80,144,246,250,252,1650,1652,1714,1720,1748,1752,2614,2618,2646,2652,2710,2714,2716,2800,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5618 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5618 2710 4
  · have he : independentCachedBranchMembers5618.erase 2710=independentCachedBranchMembers5616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5616
  · have he : independentCachedBranchMembers5618.filter (independentCachedEdge 2710)=independentCachedBranchMembers5617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5617
def independentCachedBranchMembers5619 : Finset ℕ := ([48,144,246,252,1652,1714,1720,1748,2618,2646,2652,2714,3188,3250,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5619 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5619 4 (fun x => (if x<2618 then (if x<1652 then (if x<246 then (if x<144 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1720 then (if x<1714 then 0 else 0) else (if x<1748 then 1 else 1))) else (if x<3188 then (if x<2652 then (if x<2646 then 2 else 2) else (if x<2714 then 3 else 3)) else (if x<3256 then (if x<3250 then 3 else 3) else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5620 : Finset ℕ := ([48,80,144,246,250,252,1650,1652,1714,1720,1748,1752,2614,2618,2646,2650,2652,2710,2714,2716,2800,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5620 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5620 2650 4
  · have he : independentCachedBranchMembers5620.erase 2650=independentCachedBranchMembers5618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5618
  · have he : independentCachedBranchMembers5620.filter (independentCachedEdge 2650)=independentCachedBranchMembers5619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5619
def independentCachedBranchMembers5621 : Finset ℕ := ([80,144,246,250,1650,1714,1748,1752,2614,2618,2652,2716,3186,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5621 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5621 4 (fun x => (if x<2614 then (if x<1650 then (if x<246 then (if x<144 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1748 then (if x<1714 then 0 else 1) else (if x<1752 then 0 else 1))) else (if x<3186 then (if x<2652 then (if x<2618 then 2 else 3) else (if x<2716 then 2 else 3)) else (if x<3284 then (if x<3250 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5622 : Finset ℕ := ([48,80,144,246,250,252,1650,1652,1714,1720,1748,1752,2614,2618,2620,2646,2650,2652,2710,2714,2716,2800,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5622 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5622 2620 4
  · have he : independentCachedBranchMembers5622.erase 2620=independentCachedBranchMembers5620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5620
  · have he : independentCachedBranchMembers5622.filter (independentCachedEdge 2620)=independentCachedBranchMembers5621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5621
def independentCachedBranchMembers5623 : Finset ℕ := ([36,40,48,66,72,80,130,132,144,238,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5623 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5623 238 5
  · have he : independentCachedBranchMembers5623.erase 238=independentCachedBranchMembers5615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5615
  · have he : independentCachedBranchMembers5623.filter (independentCachedEdge 238)=independentCachedBranchMembers5622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5622
def independentCachedBranchMembers5624 : Finset ℕ := ([40,72,130,132,144,246,1642,1644,1702,1714,1734,1748,2606,2618,2620,2638,2650,2652,2710,2786,2788,2800,3102,3178,3180,3192,3238,3250,3252,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5624 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5624 5 (fun x => (if x<2650 then (if x<1702 then (if x<144 then (if x<130 then (if x<72 then 0 else 1) else (if x<132 then 0 else 1)) else (if x<1642 then (if x<246 then 2 else 2) else (if x<1644 then 1 else 0))) else (if x<2606 then (if x<1734 then (if x<1714 then 1 else 2) else (if x<1748 then 0 else 2)) else (if x<2620 then (if x<2618 then 3 else 4) else (if x<2638 then 0 else 4)))) else (if x<3180 then (if x<2788 then (if x<2710 then (if x<2652 then 1 else 3) else (if x<2786 then 0 else 4)) else (if x<3102 then (if x<2800 then 3 else 2) else (if x<3178 then 3 else 4))) else (if x<3252 then (if x<3238 then (if x<3192 then 3 else 0) else (if x<3250 then 3 else 4)) else (if x<3282 then (if x<3270 then 1 else 4) else (if x<3284 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5625 : Finset ℕ := ([36,40,48,66,72,80,130,132,136,144,238,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5625 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5625 136 5
  · have he : independentCachedBranchMembers5625.erase 136=independentCachedBranchMembers5623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5623
  · have he : independentCachedBranchMembers5625.filter (independentCachedEdge 136)=independentCachedBranchMembers5624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5624
def independentCachedBranchMembers5626 : Finset ℕ := ([36,66,72,80,132,250,1642,1650,1702,1708,1738,1752,2606,2614,2620,2650,2702,2710,2716,2786,2792,2800,3102,3178,3186,3192,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5626 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5626 5 (fun x => (if x<2702 then (if x<1702 then (if x<132 then (if x<72 then (if x<66 then 0 else 0) else (if x<80 then 1 else 2)) else (if x<1642 then (if x<250 then 1 else 2) else (if x<1650 then 1 else 2))) else (if x<2606 then (if x<1738 then (if x<1708 then 1 else 0) else (if x<1752 then 0 else 2)) else (if x<2620 then (if x<2614 then 3 else 4) else (if x<2650 then 0 else 0)))) else (if x<3186 then (if x<2792 then (if x<2716 then (if x<2710 then 4 else 1) else (if x<2786 then 3 else 4)) else (if x<3102 then (if x<2800 then 3 else 2) else (if x<3178 then 3 else 3))) else (if x<3252 then (if x<3238 then (if x<3192 then 4 else 1) else (if x<3244 then 4 else 3)) else (if x<3282 then (if x<3274 then 0 else 4) else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5627 : Finset ℕ := ([36,40,48,66,68,72,80,130,132,136,144,238,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5627 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5627 68 5
  · have he : independentCachedBranchMembers5627.erase 68=independentCachedBranchMembers5625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5625
  · have he : independentCachedBranchMembers5627.filter (independentCachedEdge 68)=independentCachedBranchMembers5626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5626
def independentCachedBranchMembers5628 : Finset ℕ := ([36,40,48,66,130,252,1644,1652,1708,1720,1734,1738,2620,2638,2646,2650,2702,2710,2714,2788,2792,2800,3102,3180,3188,3192,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5628 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5628 5 (fun x => (if x<2702 then (if x<1708 then (if x<130 then (if x<48 then (if x<40 then 0 else 1) else (if x<66 then 2 else 0)) else (if x<1644 then (if x<252 then 1 else 2) else (if x<1652 then 1 else 2))) else (if x<2620 then (if x<1734 then (if x<1720 then 0 else 2) else (if x<1738 then 1 else 0)) else (if x<2646 then (if x<2638 then 0 else 3) else (if x<2650 then 4 else 0)))) else (if x<3188 then (if x<2792 then (if x<2714 then (if x<2710 then 4 else 1) else (if x<2788 then 3 else 4)) else (if x<3102 then (if x<2800 then 3 else 2) else (if x<3180 then 3 else 3))) else (if x<3256 then (if x<3244 then (if x<3192 then 4 else 1) else (if x<3252 then 4 else 0)) else (if x<3274 then (if x<3270 then 3 else 4) else (if x<3282 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5629 : Finset ℕ := ([34,36,40,48,66,68,72,80,130,132,136,144,238,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5629 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5629 34 5
  · have he : independentCachedBranchMembers5629.erase 34=independentCachedBranchMembers5627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5627
  · have he : independentCachedBranchMembers5629.filter (independentCachedEdge 34)=independentCachedBranchMembers5628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5628
def independentCachedBranchMembers5630 : Finset ℕ := ([132,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3102,3178,3188,3192,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5630 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5630 5 (fun x => (if x<2652 then (if x<1734 then (if x<1650 then (if x<252 then 0 else (if x<1644 then 0 else 1)) else (if x<1708 then 1 else (if x<1714 then 0 else 2))) else (if x<1752 then (if x<1738 then 1 else (if x<1748 then 2 else 0)) else (if x<2618 then (if x<2614 then 1 else 2) else (if x<2638 then 3 else 2)))) else (if x<3188 then (if x<2788 then (if x<2702 then 3 else (if x<2716 then 3 else 0)) else (if x<3102 then (if x<2792 then 0 else 3) else (if x<3178 then 3 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3238 then 1 else 4)) else (if x<3276 then (if x<3256 then 0 else 4) else (if x<3282 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5631 : Finset ℕ := ([1650,1708,1734,1748,2618,2702,2716,2788,3102,3188,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5631 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5631 4 (fun x => (if x<2716 then (if x<1748 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<2618 then 1 else (if x<2702 then 0 else 0))) else (if x<3188 then (if x<2788 then 1 else (if x<3102 then 1 else 2)) else (if x<3256 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
