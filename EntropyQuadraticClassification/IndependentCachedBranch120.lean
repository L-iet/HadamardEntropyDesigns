/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch119
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6624 : Finset ℕ := ([1738,1748,2652,2792,3150,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6624 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6624 3 (fun x => (if x<2792 then (if x<1748 then 0 else (if x<2652 then 0 else 1)) else (if x<3150 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6625 : Finset ℕ := ([72,252,1626,1738,1748,1776,2652,2680,2764,2770,2792,3150,3188,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6625 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6625 2680 3
  · have he : independentCachedBranchMembers6625.erase 2680=independentCachedBranchMembers6623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6623
  · have he : independentCachedBranchMembers6625.filter (independentCachedEdge 2680)=independentCachedBranchMembers6624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6624
def independentCachedBranchMembers6626 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1738,1746,1748,1768,1776,2650,2652,2680,2762,2764,2770,2772,2792,2800,3150,3158,3188,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6626 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6626 1746 4
  · have he : independentCachedBranchMembers6626.erase 1746=independentCachedBranchMembers6622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6622
  · have he : independentCachedBranchMembers6626.filter (independentCachedEdge 1746)=independentCachedBranchMembers6625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6625
def independentCachedBranchMembers6627 : Finset ℕ := ([80,250,1628,1738,1748,1768,2680,2764,2770,2800,3188,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6627 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6627 4 (fun x => (if x<2680 then (if x<1738 then (if x<250 then 0 else (if x<1628 then 0 else 1)) else (if x<1748 then 1 else (if x<1768 then 2 else 2))) else (if x<2800 then (if x<2764 then 0 else (if x<2770 then 1 else 0)) else (if x<3188 then 2 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6628 : Finset ℕ := ([250,1738,2680,2764,2800,3188] : List ℕ).toFinset
theorem independentCachedBranchBound6628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6628 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6628 3 (fun x => (if x<2764 then (if x<1738 then 0 else (if x<2680 then 0 else 1)) else (if x<2800 then 1 else (if x<3188 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6629 : Finset ℕ := ([80,250,1628,1738,1748,1768,2680,2764,2770,2800,3158,3188,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6629 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6629 3158 3
  · have he : independentCachedBranchMembers6629.erase 3158=independentCachedBranchMembers6627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6627
  · have he : independentCachedBranchMembers6629.filter (independentCachedEdge 3158)=independentCachedBranchMembers6628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6628
def independentCachedBranchMembers6630 : Finset ℕ := ([1748,1768,2680,2770,3188,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6630 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6630 3 (fun x => (if x<2770 then (if x<1768 then 0 else (if x<2680 then 0 else 1)) else (if x<3188 then 1 else (if x<3298 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6631 : Finset ℕ := ([80,250,1628,1738,1748,1768,2650,2680,2764,2770,2800,3158,3188,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6631 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6631 2650 3
  · have he : independentCachedBranchMembers6631.erase 2650=independentCachedBranchMembers6629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6629
  · have he : independentCachedBranchMembers6631.filter (independentCachedEdge 2650)=independentCachedBranchMembers6630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6630
def independentCachedBranchMembers6632 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1738,1740,1746,1748,1768,1776,2650,2652,2680,2762,2764,2770,2772,2792,2800,3150,3158,3188,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6632 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6632 1740 4
  · have he : independentCachedBranchMembers6632.erase 1740=independentCachedBranchMembers6626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6626
  · have he : independentCachedBranchMembers6632.filter (independentCachedEdge 1740)=independentCachedBranchMembers6631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6631
def independentCachedBranchMembers6633 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6633 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6633 3174 5
  · have he : independentCachedBranchMembers6633.erase 3174=independentCachedBranchMembers6619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6619
  · have he : independentCachedBranchMembers6633.filter (independentCachedEdge 3174)=independentCachedBranchMembers6632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6632
def independentCachedBranchMembers6634 : Finset ℕ := ([72,80,250,252,1626,1628,1644,1650,1734,1752,1768,1776,2638,2646,2680,2762,2764,2770,2772,2786,2788,3162,3164,3188,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6634 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6634 5 (fun x => (if x<2646 then (if x<1644 then (if x<252 then (if x<80 then 0 else (if x<250 then 1 else 0)) else (if x<1626 then 1 else (if x<1628 then 0 else 1))) else (if x<1752 then (if x<1650 then 2 else (if x<1734 then 2 else 2)) else (if x<1776 then (if x<1768 then 2 else 0) else (if x<2638 then 1 else 3)))) else (if x<2788 then (if x<2764 then (if x<2680 then 4 else (if x<2762 then 0 else 0)) else (if x<2772 then (if x<2770 then 2 else 2) else (if x<2786 then 1 else 3))) else (if x<3188 then (if x<3162 then 4 else (if x<3164 then 4 else 3)) else (if x<3304 then (if x<3288 then 1 else 0) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6635 : Finset ℕ := ([72,250,1628,1644,1650,1776,2638,2764,2770,2786,3162,3188,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6635 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6635 4 (fun x => (if x<2764 then (if x<1644 then (if x<250 then 0 else (if x<1628 then 0 else 1)) else (if x<1776 then (if x<1650 then 2 else 1) else (if x<2638 then 2 else 2))) else (if x<3162 then (if x<2770 then 1 else (if x<2786 then 2 else 1)) else (if x<3288 then (if x<3188 then 0 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6636 : Finset ℕ := ([72,80,250,252,1626,1628,1644,1650,1652,1734,1752,1768,1776,2638,2646,2680,2762,2764,2770,2772,2786,2788,3162,3164,3188,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6636 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6636 1652 4
  · have he : independentCachedBranchMembers6636.erase 1652=independentCachedBranchMembers6634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6634
  · have he : independentCachedBranchMembers6636.filter (independentCachedEdge 1652)=independentCachedBranchMembers6635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6635
def independentCachedBranchMembers6637 : Finset ℕ := ([80,252,1626,1644,1650,1768,2646,2764,2770,2788,3164,3188,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6637 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6637 4 (fun x => (if x<2764 then (if x<1644 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1768 then (if x<1650 then 1 else 2) else (if x<2646 then 2 else 2))) else (if x<3164 then (if x<2770 then 2 else (if x<2788 then 1 else 1)) else (if x<3288 then (if x<3188 then 0 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6638 : Finset ℕ := ([72,80,250,252,1626,1628,1642,1644,1650,1652,1734,1752,1768,1776,2638,2646,2680,2762,2764,2770,2772,2786,2788,3162,3164,3188,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6638 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6638 1642 4
  · have he : independentCachedBranchMembers6638.erase 1642=independentCachedBranchMembers6636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6636
  · have he : independentCachedBranchMembers6638.filter (independentCachedEdge 1642)=independentCachedBranchMembers6637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6637
def independentCachedBranchMembers6639 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1768,1776,2638,2646,2650,2652,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6639 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6639 2758 5
  · have he : independentCachedBranchMembers6639.erase 2758=independentCachedBranchMembers6633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6633
  · have he : independentCachedBranchMembers6639.filter (independentCachedEdge 2758)=independentCachedBranchMembers6638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6638
def independentCachedBranchMembers6640 : Finset ℕ := ([72,80,222,1626,1644,1652,1734,1740,1748,1768,1776,2646,2652,2680,2762,2776,2788,3150,3164,3192,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6640 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6640 5 (fun x => (if x<2646 then (if x<1652 then (if x<222 then (if x<80 then 0 else 1) else (if x<1626 then 0 else (if x<1644 then 0 else 2))) else (if x<1748 then (if x<1734 then 1 else (if x<1740 then 2 else 0)) else (if x<1768 then 3 else (if x<1776 then 3 else 2)))) else (if x<3150 then (if x<2762 then (if x<2652 then 1 else (if x<2680 then 0 else 1)) else (if x<2776 then 0 else (if x<2788 then 3 else 2))) else (if x<3282 then (if x<3164 then 0 else (if x<3192 then 1 else 4)) else (if x<3288 then 4 else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6641 : Finset ℕ := ([80,1644,1748,1776,2646,2652,2680,2762,2788,3150,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6641 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6641 4 (fun x => (if x<2680 then (if x<1776 then (if x<1644 then 0 else (if x<1748 then 1 else 0)) else (if x<2646 then 1 else (if x<2652 then 0 else 2))) else (if x<3150 then (if x<2762 then 1 else (if x<2788 then 2 else 1)) else (if x<3282 then 2 else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6642 : Finset ℕ := ([72,80,222,1626,1644,1652,1734,1740,1748,1768,1776,2646,2652,2680,2762,2776,2788,3150,3164,3192,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6642 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6642 3274 4
  · have he : independentCachedBranchMembers6642.erase 3274=independentCachedBranchMembers6640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6640
  · have he : independentCachedBranchMembers6642.filter (independentCachedEdge 3274)=independentCachedBranchMembers6641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6641
def independentCachedBranchMembers6643 : Finset ℕ := ([72,1644,1740,1776,2646,2680,2762,2776,2788,3150,3164,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6643 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6643 4 (fun x => (if x<2762 then (if x<1776 then (if x<1644 then 0 else (if x<1740 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 2 else 0))) else (if x<3150 then (if x<2776 then 2 else (if x<2788 then 1 else 1)) else (if x<3164 then 2 else (if x<3282 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6644 : Finset ℕ := ([72,80,222,1626,1644,1652,1734,1740,1748,1768,1776,2646,2652,2680,2762,2776,2788,3150,3158,3164,3192,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6644 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6644 3158 4
  · have he : independentCachedBranchMembers6644.erase 3158=independentCachedBranchMembers6642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6642
  · have he : independentCachedBranchMembers6644.filter (independentCachedEdge 3158)=independentCachedBranchMembers6643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6643
def independentCachedBranchMembers6645 : Finset ℕ := ([72,1652,1740,1768,2646,2762,2776,3150,3164,3192,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6645 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6645 4 (fun x => (if x<2776 then (if x<1768 then (if x<1652 then 0 else (if x<1740 then 1 else 0)) else (if x<2646 then 1 else (if x<2762 then 1 else 0))) else (if x<3192 then (if x<3150 then 2 else (if x<3164 then 0 else 2)) else (if x<3282 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6646 : Finset ℕ := ([72,80,222,1626,1644,1652,1734,1740,1748,1768,1776,2646,2652,2680,2762,2770,2776,2788,3150,3158,3164,3192,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6646 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6646 2770 4
  · have he : independentCachedBranchMembers6646.erase 2770=independentCachedBranchMembers6644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6644
  · have he : independentCachedBranchMembers6646.filter (independentCachedEdge 2770)=independentCachedBranchMembers6645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6645
def independentCachedBranchMembers6647 : Finset ℕ := ([80,1652,1748,1768,2646,2652,2762,3150,3192,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6647 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6647 4 (fun x => (if x<2762 then (if x<1768 then (if x<1652 then 0 else (if x<1748 then 0 else 1)) else (if x<2646 then 1 else (if x<2652 then 0 else 2))) else (if x<3282 then (if x<3150 then 2 else (if x<3192 then 2 else 3)) else (if x<3288 then 3 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6648 : Finset ℕ := ([72,80,222,1626,1644,1652,1734,1740,1748,1768,1776,2638,2646,2652,2680,2762,2770,2776,2788,3150,3158,3164,3192,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6648 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6648 2638 4
  · have he : independentCachedBranchMembers6648.erase 2638=independentCachedBranchMembers6646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6646
  · have he : independentCachedBranchMembers6648.filter (independentCachedEdge 2638)=independentCachedBranchMembers6647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6647
def independentCachedBranchMembers6649 : Finset ℕ := ([72,222,1644,1734,1748,1768,2646,2680,2770,3150,3164,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6649 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6649 4 (fun x => (if x<2680 then (if x<1734 then (if x<222 then 0 else (if x<1644 then 0 else 1)) else (if x<1768 then (if x<1748 then 1 else 2) else (if x<2646 then 2 else 2))) else (if x<3164 then (if x<2770 then 1 else (if x<3150 then 1 else 0)) else (if x<3288 then (if x<3274 then 3 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6650 : Finset ℕ := ([72,80,222,1626,1644,1652,1734,1740,1748,1768,1776,2638,2646,2652,2674,2680,2762,2770,2776,2788,3150,3158,3164,3192,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6650 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6650 2674 4
  · have he : independentCachedBranchMembers6650.erase 2674=independentCachedBranchMembers6648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6648
  · have he : independentCachedBranchMembers6650.filter (independentCachedEdge 2674)=independentCachedBranchMembers6649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6649
def independentCachedBranchMembers6651 : Finset ℕ := ([222,1644,1652,1734,1740,1748,2638,2646,2652,2788,3150,3158,3164,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6651 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6651 4 (fun x => (if x<2646 then (if x<1734 then (if x<1644 then 0 else (if x<1652 then 1 else 2)) else (if x<1748 then (if x<1740 then 0 else 2) else (if x<2638 then 1 else 0))) else (if x<3150 then (if x<2652 then 3 else (if x<2788 then 1 else 1)) else (if x<3164 then (if x<3158 then 3 else 0) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6652 : Finset ℕ := ([72,80,222,250,1626,1644,1652,1734,1740,1748,1768,1776,2638,2646,2652,2674,2680,2762,2770,2776,2788,3150,3158,3164,3192,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6652 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6652 250 4
  · have he : independentCachedBranchMembers6652.erase 250=independentCachedBranchMembers6650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6650
  · have he : independentCachedBranchMembers6652.filter (independentCachedEdge 250)=independentCachedBranchMembers6651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6651
def independentCachedBranchMembers6653 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1764,1768,1776,2638,2646,2650,2652,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6653 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6653 1764 5
  · have he : independentCachedBranchMembers6653.erase 1764=independentCachedBranchMembers6639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6639
  · have he : independentCachedBranchMembers6653.filter (independentCachedEdge 1764)=independentCachedBranchMembers6652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6652
def independentCachedBranchMembers6654 : Finset ℕ := ([192,250,252,1626,1628,1650,1652,1734,1746,1748,1768,2646,2680,2764,2776,2786,2800,3158,3192,3274,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6654 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6654 5 (fun x => (if x<2646 then (if x<1650 then (if x<252 then (if x<250 then 0 else 0) else (if x<1626 then 1 else (if x<1628 then 2 else 1))) else (if x<1746 then (if x<1652 then 3 else (if x<1734 then 2 else 2)) else (if x<1748 then 0 else (if x<1768 then 3 else 0)))) else (if x<3158 then (if x<2776 then (if x<2680 then 2 else (if x<2764 then 1 else 1)) else (if x<2786 then 0 else (if x<2800 then 0 else 3))) else (if x<3288 then (if x<3192 then 4 else (if x<3274 then 4 else 0)) else (if x<3300 then 1 else (if x<3312 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6655 : Finset ℕ := ([252,1626,1652,1748,2646,2680,2764,2776,2786,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6655 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6655 4 (fun x => (if x<2764 then (if x<1748 then (if x<1626 then 0 else (if x<1652 then 1 else 0)) else (if x<2646 then 1 else (if x<2680 then 1 else 0))) else (if x<3274 then (if x<2776 then 2 else (if x<2786 then 1 else 2)) else (if x<3300 then 2 else (if x<3312 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
