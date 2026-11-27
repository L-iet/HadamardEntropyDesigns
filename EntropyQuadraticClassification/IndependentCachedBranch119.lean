/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch118
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6592 : Finset ℕ := ([72,80,222,250,1628,1642,1746,1752,2650,2668,2772,2792,2800,3150,3158,3192,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6592 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6592 5 (fun x => (if x<2772 then (if x<1642 then (if x<222 then (if x<80 then 0 else 1) else (if x<250 then 0 else (if x<1628 then 1 else 0))) else (if x<1752 then (if x<1746 then 2 else 1) else (if x<2650 then 2 else (if x<2668 then 0 else 3)))) else (if x<3192 then (if x<2800 then (if x<2792 then 2 else 2) else (if x<3150 then 1 else (if x<3158 then 0 else 4))) else (if x<3282 then (if x<3274 then 3 else 4) else (if x<3288 then 3 else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6593 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2650,2652,2668,2674,2762,2772,2776,2788,2792,2800,3150,3158,3162,3192,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6593 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6593 2788 5
  · have he : independentCachedBranchMembers6593.erase 2788=independentCachedBranchMembers6591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6591
  · have he : independentCachedBranchMembers6593.filter (independentCachedEdge 2788)=independentCachedBranchMembers6592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6592
def independentCachedBranchMembers6594 : Finset ℕ := ([192,222,1740,1746,2650,2652,2668,2674,2776,2792,2800,3150,3158,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6594 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6594 5 (fun x => (if x<2800 then (if x<2652 then (if x<1740 then (if x<222 then 0 else 0) else (if x<1746 then 0 else (if x<2650 then 0 else 1))) else (if x<2674 then (if x<2668 then 2 else 1) else (if x<2776 then 2 else (if x<2792 then 0 else 2)))) else (if x<3276 then (if x<3158 then (if x<3150 then 1 else 1) else (if x<3192 then 2 else (if x<3274 then 1 else 0))) else (if x<3284 then (if x<3282 then 2 else 1) else (if x<3298 then 0 else (if x<3300 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6595 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2650,2652,2668,2674,2680,2762,2772,2776,2788,2792,2800,3150,3158,3162,3192,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6595 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6595 2680 5
  · have he : independentCachedBranchMembers6595.erase 2680=independentCachedBranchMembers6593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6593
  · have he : independentCachedBranchMembers6595.filter (independentCachedEdge 2680)=independentCachedBranchMembers6594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6594
def independentCachedBranchMembers6596 : Finset ℕ := ([72,192,250,252,1642,1740,1752,1776,2650,2652,2674,2772,2792,3158,3192,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6596 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6596 5 (fun x => (if x<2674 then (if x<1740 then (if x<250 then (if x<192 then 0 else 1) else (if x<252 then 0 else (if x<1642 then 1 else 0))) else (if x<1776 then (if x<1752 then 1 else 0) else (if x<2650 then 1 else (if x<2652 then 0 else 2)))) else (if x<3274 then (if x<2792 then (if x<2772 then 2 else 1) else (if x<3158 then 0 else (if x<3192 then 2 else 0))) else (if x<3288 then (if x<3276 then 0 else 2) else (if x<3298 then 1 else (if x<3300 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6597 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2646,2650,2652,2668,2674,2680,2762,2772,2776,2788,2792,2800,3150,3158,3162,3192,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6597 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6597 2646 5
  · have he : independentCachedBranchMembers6597.erase 2646=independentCachedBranchMembers6595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6595
  · have he : independentCachedBranchMembers6597.filter (independentCachedEdge 2646)=independentCachedBranchMembers6596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6596
def independentCachedBranchMembers6598 : Finset ℕ := ([72,222,1626,1628,1642,1734,1740,1776,2646,2650,2652,2668,2762,2800,3150,3192,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6598 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6598 5 (fun x => (if x<2668 then (if x<1734 then (if x<1626 then (if x<222 then 0 else 0) else (if x<1628 then 0 else (if x<1642 then 1 else 1))) else (if x<2646 then (if x<1740 then 1 else (if x<1776 then 0 else 1)) else (if x<2650 then 2 else (if x<2652 then 3 else 0)))) else (if x<3282 then (if x<2800 then (if x<2762 then 2 else 0) else (if x<3150 then 2 else (if x<3192 then 0 else 1))) else (if x<3298 then (if x<3284 then 2 else (if x<3288 then 1 else 0)) else (if x<3300 then 1 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6599 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2646,2650,2652,2668,2674,2680,2762,2772,2776,2788,2792,2800,3150,3158,3162,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6599 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6599 3312 5
  · have he : independentCachedBranchMembers6599.erase 3312=independentCachedBranchMembers6597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6597
  · have he : independentCachedBranchMembers6599.filter (independentCachedEdge 3312)=independentCachedBranchMembers6598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6598
def independentCachedBranchMembers6600 : Finset ℕ := ([192,250,1628,1642,1734,1746,1768,1776,2652,2674,2762,2788,2792,2800,3150,3158,3162,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6600 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6600 5 (fun x => (if x<2788 then (if x<1746 then (if x<1628 then (if x<250 then 0 else 0) else (if x<1642 then 1 else (if x<1734 then 1 else 1))) else (if x<2652 then (if x<1768 then 0 else (if x<1776 then 0 else 1)) else (if x<2674 then 2 else (if x<2762 then 2 else 0)))) else (if x<3162 then (if x<2800 then (if x<2792 then 2 else 3) else (if x<3150 then 0 else (if x<3158 then 1 else 3))) else (if x<3284 then (if x<3192 then 2 else (if x<3276 then 1 else 2)) else (if x<3288 then 1 else (if x<3298 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6601 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2646,2650,2652,2668,2674,2680,2762,2772,2776,2788,2792,2800,3150,3158,3162,3164,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6601 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6601 3164 5
  · have he : independentCachedBranchMembers6601.erase 3164=independentCachedBranchMembers6599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6599
  · have he : independentCachedBranchMembers6601.filter (independentCachedEdge 3164)=independentCachedBranchMembers6600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6600
def independentCachedBranchMembers6602 : Finset ℕ := ([72,80,222,252,1626,1652,1740,1752,2652,2674,2762,2788,2792,2800,3150,3158,3162,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6602 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6602 5 (fun x => (if x<2788 then (if x<1652 then (if x<222 then (if x<80 then 0 else 1) else (if x<252 then 0 else (if x<1626 then 1 else 0))) else (if x<2652 then (if x<1740 then 1 else (if x<1752 then 0 else 1)) else (if x<2674 then 0 else (if x<2762 then 2 else 0)))) else (if x<3162 then (if x<2800 then (if x<2792 then 2 else 3) else (if x<3150 then 1 else (if x<3158 then 0 else 3))) else (if x<3284 then (if x<3192 then 2 else (if x<3276 then 1 else 2)) else (if x<3288 then 1 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6603 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2646,2650,2652,2668,2674,2680,2762,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6603 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6603 2786 5
  · have he : independentCachedBranchMembers6603.erase 2786=independentCachedBranchMembers6601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6601
  · have he : independentCachedBranchMembers6603.filter (independentCachedEdge 2786)=independentCachedBranchMembers6602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6602
def independentCachedBranchMembers6604 : Finset ℕ := ([80,192,250,252,1652,1746,1752,1768,2646,2650,2652,2668,2762,2800,3150,3192,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6604 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6604 5 (fun x => (if x<2668 then (if x<1746 then (if x<250 then (if x<192 then 0 else 1) else (if x<252 then 0 else (if x<1652 then 1 else 2))) else (if x<2646 then (if x<1752 then 0 else (if x<1768 then 1 else 2)) else (if x<2650 then 2 else (if x<2652 then 0 else 3)))) else (if x<3282 then (if x<2800 then (if x<2762 then 2 else 2) else (if x<3150 then 0 else (if x<3192 then 3 else 3))) else (if x<3298 then (if x<3284 then 4 else (if x<3288 then 1 else 0)) else (if x<3300 then 3 else (if x<3304 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6605 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2762,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6605 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6605 2638 5
  · have he : independentCachedBranchMembers6605.erase 2638=independentCachedBranchMembers6603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6603
  · have he : independentCachedBranchMembers6605.filter (independentCachedEdge 2638)=independentCachedBranchMembers6604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6604
def independentCachedBranchMembers6606 : Finset ℕ := ([72,252,1628,1642,1652,1740,1746,1768,2646,2650,2668,2674,2762,2772,2776,2786,2800,3150,3164,3192,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6606 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6606 5 (fun x => (if x<2762 then (if x<1746 then (if x<1642 then (if x<252 then 0 else (if x<1628 then 0 else 0)) else (if x<1652 then 1 else (if x<1740 then 1 else 1))) else (if x<2650 then (if x<1768 then 1 else (if x<2646 then 0 else 2)) else (if x<2668 then 3 else (if x<2674 then 0 else 1)))) else (if x<3164 then (if x<2786 then (if x<2772 then 1 else (if x<2776 then 1 else 0)) else (if x<2800 then 2 else (if x<3150 then 3 else 3))) else (if x<3282 then (if x<3192 then 2 else (if x<3276 then 0 else 0)) else (if x<3300 then 2 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6607 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2762,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6607 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6607 2770 5
  · have he : independentCachedBranchMembers6607.erase 2770=independentCachedBranchMembers6605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6605
  · have he : independentCachedBranchMembers6607.filter (independentCachedEdge 2770)=independentCachedBranchMembers6606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6606
def independentCachedBranchMembers6608 : Finset ℕ := ([80,250,1626,1642,1652,1740,1746,1776,2638,2652,2668,2674,2762,2772,2776,2788,2792,3158,3162,3192,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6608 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6608 5 (fun x => (if x<2762 then (if x<1746 then (if x<1642 then (if x<250 then 0 else (if x<1626 then 0 else 0)) else (if x<1652 then 1 else (if x<1740 then 1 else 1))) else (if x<2652 then (if x<1776 then 1 else (if x<2638 then 0 else 2)) else (if x<2668 then 3 else (if x<2674 then 1 else 0)))) else (if x<3162 then (if x<2788 then (if x<2772 then 1 else (if x<2776 then 1 else 0)) else (if x<2792 then 2 else (if x<3158 then 3 else 3))) else (if x<3282 then (if x<3192 then 2 else (if x<3276 then 0 else 2)) else (if x<3298 then 0 else (if x<3312 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6609 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6609 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6609 2764 5
  · have he : independentCachedBranchMembers6609.erase 2764=independentCachedBranchMembers6607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6607
  · have he : independentCachedBranchMembers6609.filter (independentCachedEdge 2764)=independentCachedBranchMembers6608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6608
def independentCachedBranchMembers6610 : Finset ℕ := ([72,192,222,250,1626,1642,1652,1734,1740,1746,1752,1768,2638,2650,2764,2770,2776,2786,2792,3158,3164,3192,3274,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6610 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6610 5 (fun x => (if x<2650 then (if x<1652 then (if x<250 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1626 then 1 else (if x<1642 then 0 else 2))) else (if x<1746 then (if x<1734 then 2 else (if x<1740 then 2 else 0)) else (if x<1768 then (if x<1752 then 1 else 2) else (if x<2638 then 1 else 0)))) else (if x<3158 then (if x<2776 then (if x<2764 then 3 else (if x<2770 then 3 else 4)) else (if x<2786 then 0 else (if x<2792 then 1 else 4))) else (if x<3274 then (if x<3164 then 4 else (if x<3192 then 0 else 2)) else (if x<3300 then (if x<3284 then 0 else 2) else (if x<3312 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6611 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6611 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6611 3188 5
  · have he : independentCachedBranchMembers6611.erase 3188=independentCachedBranchMembers6609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6609
  · have he : independentCachedBranchMembers6611.filter (independentCachedEdge 3188)=independentCachedBranchMembers6610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6610
def independentCachedBranchMembers6612 : Finset ℕ := ([72,250,1628,1642,1652,1734,1740,1746,1752,1776,2638,2650,2668,2674,2680,2762,2772,2786,2792,3150,3162,3192,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6612 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6612 5 (fun x => (if x<2674 then (if x<1740 then (if x<1642 then (if x<250 then 0 else (if x<1628 then 0 else 1)) else (if x<1652 then 0 else (if x<1734 then 2 else 1))) else (if x<1776 then (if x<1746 then 2 else (if x<1752 then 2 else 0)) else (if x<2650 then (if x<2638 then 1 else 1) else (if x<2668 then 0 else 2)))) else (if x<3150 then (if x<2772 then (if x<2680 then 2 else (if x<2762 then 1 else 2)) else (if x<2786 then 1 else (if x<2792 then 1 else 0))) else (if x<3274 then (if x<3162 then 3 else (if x<3192 then 4 else 0)) else (if x<3298 then (if x<3284 then 0 else 3) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6613 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1740,1746,1748,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6613 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6613 1748 5
  · have he : independentCachedBranchMembers6613.erase 1748=independentCachedBranchMembers6611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6611
  · have he : independentCachedBranchMembers6613.filter (independentCachedEdge 1748)=independentCachedBranchMembers6612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6612
def independentCachedBranchMembers6614 : Finset ℕ := ([80,252,1626,1642,1652,1734,1740,1746,1752,1768,2646,2652,2668,2674,2680,2762,2772,2788,2800,3158,3164,3192,3274,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6614 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6614 5 (fun x => (if x<2674 then (if x<1740 then (if x<1642 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1652 then 2 else (if x<1734 then 0 else 1))) else (if x<1768 then (if x<1746 then 2 else (if x<1752 then 2 else 0)) else (if x<2652 then (if x<2646 then 1 else 1) else (if x<2668 then 0 else 2)))) else (if x<3158 then (if x<2772 then (if x<2680 then 2 else (if x<2762 then 1 else 1)) else (if x<2788 then 2 else (if x<2800 then 1 else 0))) else (if x<3274 then (if x<3164 then 3 else (if x<3192 then 4 else 0)) else (if x<3300 then (if x<3284 then 3 else 0) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6615 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1652,1734,1738,1740,1746,1748,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6615 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6615 1738 5
  · have he : independentCachedBranchMembers6615.erase 1738=independentCachedBranchMembers6613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6613
  · have he : independentCachedBranchMembers6615.filter (independentCachedEdge 1738)=independentCachedBranchMembers6614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6614
def independentCachedBranchMembers6616 : Finset ℕ := ([72,192,222,252,1626,1642,1652,1740,1746,1776,2638,2652,2668,2674,2762,2772,2776,2788,2792,3150,3164,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6616 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6616 5 (fun x => (if x<2674 then (if x<1652 then (if x<252 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1626 then 1 else (if x<1642 then 0 else 2))) else (if x<1776 then (if x<1740 then 2 else (if x<1746 then 0 else 2)) else (if x<2652 then (if x<2638 then 1 else 0) else (if x<2668 then 3 else 2)))) else (if x<3150 then (if x<2776 then (if x<2762 then 2 else (if x<2772 then 2 else 1)) else (if x<2788 then 0 else (if x<2792 then 3 else 1))) else (if x<3284 then (if x<3164 then 4 else (if x<3274 then 0 else 0)) else (if x<3300 then (if x<3288 then 3 else 1) else (if x<3304 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6617 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1650,1652,1734,1738,1740,1746,1748,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6617 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6617 1650 5
  · have he : independentCachedBranchMembers6617.erase 1650=independentCachedBranchMembers6615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6615
  · have he : independentCachedBranchMembers6617.filter (independentCachedEdge 1650)=independentCachedBranchMembers6616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6616
def independentCachedBranchMembers6618 : Finset ℕ := ([80,192,222,250,1628,1642,1652,1740,1746,1768,2646,2650,2668,2674,2762,2772,2776,2786,2800,3158,3162,3274,3284,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6618 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6618 5 (fun x => (if x<2674 then (if x<1652 then (if x<250 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1628 then 1 else (if x<1642 then 0 else 2))) else (if x<1768 then (if x<1740 then 2 else (if x<1746 then 2 else 0)) else (if x<2650 then (if x<2646 then 1 else 0) else (if x<2668 then 3 else 2)))) else (if x<3158 then (if x<2776 then (if x<2762 then 2 else (if x<2772 then 1 else 2)) else (if x<2786 then 0 else (if x<2800 then 3 else 1))) else (if x<3284 then (if x<3162 then 4 else (if x<3274 then 0 else 3)) else (if x<3298 then (if x<3288 then 0 else 1) else (if x<3312 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6619 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6619 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6619 1644 5
  · have he : independentCachedBranchMembers6619.erase 1644=independentCachedBranchMembers6617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6617
  · have he : independentCachedBranchMembers6619.filter (independentCachedEdge 1644)=independentCachedBranchMembers6618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6618
def independentCachedBranchMembers6620 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1738,1748,1768,1776,2652,2680,2762,2764,2770,2772,2792,2800,3150,3158,3188,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6620 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6620 5 (fun x => (if x<2680 then (if x<1626 then (if x<222 then (if x<80 then 0 else (if x<192 then 1 else 2)) else (if x<250 then 0 else (if x<252 then 1 else 2))) else (if x<1748 then (if x<1628 then 0 else (if x<1738 then 3 else 3)) else (if x<1776 then (if x<1768 then 2 else 2) else (if x<2652 then 1 else 0)))) else (if x<2800 then (if x<2770 then (if x<2762 then 1 else (if x<2764 then 0 else 2)) else (if x<2772 then 1 else (if x<2792 then 4 else 4))) else (if x<3188 then (if x<3150 then 2 else (if x<3158 then 0 else 4)) else (if x<3298 then (if x<3288 then 3 else 0) else (if x<3300 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6621 : Finset ℕ := ([192,252,1626,1748,1768,1776,2652,2680,2762,2770,3188,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6621 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6621 4 (fun x => (if x<2652 then (if x<1748 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1768 then 0 else (if x<1776 then 0 else 1))) else (if x<2770 then (if x<2680 then 2 else (if x<2762 then 1 else 2)) else (if x<3188 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6622 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1738,1748,1768,1776,2650,2652,2680,2762,2764,2770,2772,2792,2800,3150,3158,3188,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6622 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6622 2650 4
  · have he : independentCachedBranchMembers6622.erase 2650=independentCachedBranchMembers6620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6620
  · have he : independentCachedBranchMembers6622.filter (independentCachedEdge 2650)=independentCachedBranchMembers6621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6621
def independentCachedBranchMembers6623 : Finset ℕ := ([72,252,1626,1738,1748,1776,2652,2764,2770,2792,3150,3188,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6623 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6623 4 (fun x => (if x<2652 then (if x<1738 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1748 then 2 else (if x<1776 then 1 else 2))) else (if x<2792 then (if x<2764 then 0 else (if x<2770 then 3 else 1)) else (if x<3188 then (if x<3150 then 0 else 2) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
