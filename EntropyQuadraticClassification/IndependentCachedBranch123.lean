/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch122
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6720 : Finset ℕ := ([80,252,1628,1642,1650,1734,1746,1764,1768,1776,2646,2668,2680,2764,2772,2776,2786,3150,3162,3188,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6720 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6720 2764 4
  · have he : independentCachedBranchMembers6720.erase 2764=independentCachedBranchMembers6718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6718
  · have he : independentCachedBranchMembers6720.filter (independentCachedEdge 2764)=independentCachedBranchMembers6719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6719
def independentCachedBranchMembers6721 : Finset ℕ := ([252,1734,1768,1776,2646,2680,2776,3162,3188,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6721 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6721 4 (fun x => (if x<2776 then (if x<1776 then (if x<1734 then 0 else (if x<1768 then 1 else 0)) else (if x<2646 then 1 else (if x<2680 then 2 else 0))) else (if x<3276 then (if x<3162 then 2 else (if x<3188 then 2 else 3)) else (if x<3284 then 3 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6722 : Finset ℕ := ([80,252,1628,1642,1650,1734,1746,1764,1768,1776,2646,2650,2668,2680,2764,2772,2776,2786,3150,3162,3188,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6722 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6722 2650 4
  · have he : independentCachedBranchMembers6722.erase 2650=independentCachedBranchMembers6720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6720
  · have he : independentCachedBranchMembers6722.filter (independentCachedEdge 2650)=independentCachedBranchMembers6721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6721
def independentCachedBranchMembers6723 : Finset ℕ := ([80,252,1642,1734,1746,1768,2646,2668,2680,2772,3192,3284] : List ℕ).toFinset
theorem independentCachedBranchBound6723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6723 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6723 4 (fun x => (if x<2646 then (if x<1734 then (if x<252 then 0 else (if x<1642 then 0 else 1)) else (if x<1746 then 1 else (if x<1768 then 2 else 2))) else (if x<2772 then (if x<2668 then 2 else (if x<2680 then 2 else 0)) else (if x<3192 then 0 else (if x<3284 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6724 : Finset ℕ := ([80,252,1628,1642,1650,1734,1738,1746,1764,1768,1776,2646,2650,2668,2680,2764,2772,2776,2786,3150,3162,3188,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6724 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6724 1738 4
  · have he : independentCachedBranchMembers6724.erase 1738=independentCachedBranchMembers6722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6722
  · have he : independentCachedBranchMembers6724.filter (independentCachedEdge 1738)=independentCachedBranchMembers6723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6723
def independentCachedBranchMembers6725 : Finset ℕ := ([252,1642,1650,1764,1768,1776,2668,2680,2786,3188,3192,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6725 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6725 4 (fun x => (if x<2668 then (if x<1764 then (if x<1642 then 0 else (if x<1650 then 1 else 2)) else (if x<1768 then 0 else (if x<1776 then 2 else 1))) else (if x<3188 then (if x<2680 then 0 else (if x<2786 then 1 else 1)) else (if x<3192 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6726 : Finset ℕ := ([80,222,252,1628,1642,1650,1734,1738,1746,1764,1768,1776,2646,2650,2668,2680,2764,2772,2776,2786,3150,3162,3188,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6726 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6726 222 4
  · have he : independentCachedBranchMembers6726.erase 222=independentCachedBranchMembers6724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6724
  · have he : independentCachedBranchMembers6726.filter (independentCachedEdge 222)=independentCachedBranchMembers6725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6725
def independentCachedBranchMembers6727 : Finset ℕ := ([80,1650,1734,1746,1764,1776,2646,2772,2786,3188,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6727 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6727 4 (fun x => (if x<2646 then (if x<1746 then (if x<1650 then 0 else (if x<1734 then 0 else 1)) else (if x<1764 then 2 else (if x<1776 then 2 else 1))) else (if x<3188 then (if x<2772 then 0 else (if x<2786 then 1 else 1)) else (if x<3284 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6728 : Finset ℕ := ([72,80,222,252,1628,1642,1650,1734,1738,1746,1764,1768,1776,2646,2650,2668,2680,2764,2772,2776,2786,3150,3162,3188,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6728 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6728 72 4
  · have he : independentCachedBranchMembers6728.erase 72=independentCachedBranchMembers6726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6726
  · have he : independentCachedBranchMembers6728.filter (independentCachedEdge 72)=independentCachedBranchMembers6727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6727
def independentCachedBranchMembers6729 : Finset ℕ := ([252,1642,1738,1764,1776,2646,2668,2680,2764,2776,2786,3150,3162,3188,3284] : List ℕ).toFinset
theorem independentCachedBranchBound6729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6729 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6729 4 (fun x => (if x<2680 then (if x<1764 then (if x<1642 then 0 else (if x<1738 then 1 else 2)) else (if x<2646 then (if x<1776 then 0 else 1) else (if x<2668 then 3 else 0))) else (if x<3150 then (if x<2776 then (if x<2764 then 1 else 2) else (if x<2786 then 3 else 1)) else (if x<3188 then (if x<3162 then 2 else 3) else (if x<3284 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6730 : Finset ℕ := ([1764,1776,2646,2786,3188,3284] : List ℕ).toFinset
theorem independentCachedBranchBound6730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6730 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6730 3 (fun x => (if x<2786 then (if x<1776 then 0 else (if x<2646 then 1 else 2)) else (if x<3188 then 0 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6731 : Finset ℕ := ([72,252,1642,1738,1764,1776,2646,2668,2680,2764,2776,2786,3150,3162,3188,3284] : List ℕ).toFinset
theorem independentCachedBranchBound6731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6731 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6731 72 3
  · have he : independentCachedBranchMembers6731.erase 72=independentCachedBranchMembers6729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6729
  · have he : independentCachedBranchMembers6731.filter (independentCachedEdge 72)=independentCachedBranchMembers6730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6730
def independentCachedBranchMembers6732 : Finset ℕ := ([72,80,222,252,1628,1642,1650,1734,1738,1746,1764,1768,1776,2646,2650,2668,2680,2764,2772,2776,2786,3150,3158,3162,3188,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6732 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6732 3158 4
  · have he : independentCachedBranchMembers6732.erase 3158=independentCachedBranchMembers6728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6728
  · have he : independentCachedBranchMembers6732.filter (independentCachedEdge 3158)=independentCachedBranchMembers6731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6731
def independentCachedBranchMembers6733 : Finset ℕ := ([80,252,1650,1746,1764,1768,2646,2650,2668,2764,3150,3188,3192,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6733 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6733 4 (fun x => (if x<2668 then (if x<1764 then (if x<1650 then (if x<252 then 0 else 0) else (if x<1746 then 1 else 2)) else (if x<2646 then (if x<1768 then 1 else 2) else (if x<2650 then 2 else 1))) else (if x<3192 then (if x<3150 then (if x<2764 then 2 else 1) else (if x<3188 then 3 else 0)) else (if x<3288 then (if x<3284 then 3 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6734 : Finset ℕ := ([72,80,222,252,1628,1642,1650,1734,1738,1746,1764,1768,1776,2638,2646,2650,2668,2680,2764,2772,2776,2786,3150,3158,3162,3188,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6734 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6734 2638 4
  · have he : independentCachedBranchMembers6734.erase 2638=independentCachedBranchMembers6732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6732
  · have he : independentCachedBranchMembers6734.filter (independentCachedEdge 2638)=independentCachedBranchMembers6733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6733
def independentCachedBranchMembers6735 : Finset ℕ := ([72,80,1642,1650,1738,1746,1768,1776,2650,2680,2776,2786,3162,3192,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6735 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6735 4 (fun x => (if x<2650 then (if x<1738 then (if x<1642 then (if x<80 then 0 else 1) else (if x<1650 then 0 else 1)) else (if x<1768 then (if x<1746 then 2 else 3) else (if x<1776 then 3 else 2))) else (if x<3162 then (if x<2776 then (if x<2680 then 0 else 1) else (if x<2786 then 2 else 2)) else (if x<3288 then (if x<3192 then 1 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6736 : Finset ℕ := ([68,72,80,222,252,1628,1642,1650,1734,1738,1746,1764,1768,1776,2638,2646,2650,2668,2680,2764,2772,2776,2786,3150,3158,3162,3188,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6736 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6736 68 4
  · have he : independentCachedBranchMembers6736.erase 68=independentCachedBranchMembers6734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6734
  · have he : independentCachedBranchMembers6736.filter (independentCachedEdge 68)=independentCachedBranchMembers6735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6735
def independentCachedBranchMembers6737 : Finset ℕ := ([68,72,80,192,222,246,250,252,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2638,2646,2650,2652,2662,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6737 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6737 1762 5
  · have he : independentCachedBranchMembers6737.erase 1762=independentCachedBranchMembers6717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6717
  · have he : independentCachedBranchMembers6737.filter (independentCachedEdge 1762)=independentCachedBranchMembers6736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6736
def independentCachedBranchMembers6738 : Finset ℕ := ([252,1622,1628,1642,1644,1734,1738,1740,1776,2638,2680,2770,2772,2788,2792,3150,3188,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6738 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6738 5 (fun x => (if x<2680 then (if x<1734 then (if x<1628 then (if x<1622 then 0 else 1) else (if x<1642 then 0 else (if x<1644 then 1 else 2))) else (if x<1740 then (if x<1738 then 2 else 3) else (if x<1776 then 1 else (if x<2638 then 0 else 1)))) else (if x<3150 then (if x<2772 then (if x<2770 then 0 else 2) else (if x<2788 then 0 else (if x<2792 then 2 else 1))) else (if x<3288 then (if x<3188 then 3 else (if x<3284 then 0 else 4)) else (if x<3298 then 0 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6739 : Finset ℕ := ([1622,1628,1642,1644,2638,2680,3150,3188] : List ℕ).toFinset
theorem independentCachedBranchBound6739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6739 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6739 4 (fun x => (if x<2638 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1644 then 0 else 2)) else (if x<3150 then (if x<2680 then 0 else 1) else (if x<3188 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6740 : Finset ℕ := ([192,252,1622,1628,1642,1644,1734,1738,1740,1776,2638,2680,2770,2772,2788,2792,3150,3188,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6740 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6740 192 4
  · have he : independentCachedBranchMembers6740.erase 192=independentCachedBranchMembers6738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6738
  · have he : independentCachedBranchMembers6740.filter (independentCachedEdge 192)=independentCachedBranchMembers6739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6739
def independentCachedBranchMembers6741 : Finset ℕ := ([252,1628,1642,1740,2638,2680,2770,2788,2792,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6741 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6741 4 (fun x => (if x<2770 then (if x<1740 then (if x<1628 then 0 else (if x<1642 then 0 else 1)) else (if x<2638 then 1 else (if x<2680 then 1 else 0))) else (if x<3284 then (if x<2788 then 2 else (if x<2792 then 2 else 1)) else (if x<3288 then 2 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6742 : Finset ℕ := ([192,252,1622,1628,1642,1644,1734,1738,1740,1776,2638,2680,2770,2772,2788,2792,3150,3188,3282,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6742 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6742 3282 4
  · have he : independentCachedBranchMembers6742.erase 3282=independentCachedBranchMembers6740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6740
  · have he : independentCachedBranchMembers6742.filter (independentCachedEdge 3282)=independentCachedBranchMembers6741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6741
def independentCachedBranchMembers6743 : Finset ℕ := ([192,1622,1738,1740,2638,2680,2770,2772,2788,3188,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6743 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6743 4 (fun x => (if x<2770 then (if x<1740 then (if x<1622 then 0 else (if x<1738 then 1 else 0)) else (if x<2638 then 1 else (if x<2680 then 1 else 2))) else (if x<3188 then (if x<2772 then 0 else (if x<2788 then 1 else 2)) else (if x<3288 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6744 : Finset ℕ := ([192,252,1622,1628,1642,1644,1734,1738,1740,1776,2638,2680,2770,2772,2788,2792,3150,3188,3192,3282,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6744 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6744 3192 4
  · have he : independentCachedBranchMembers6744.erase 3192=independentCachedBranchMembers6742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6742
  · have he : independentCachedBranchMembers6744.filter (independentCachedEdge 3192)=independentCachedBranchMembers6743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6743
def independentCachedBranchMembers6745 : Finset ℕ := ([1622,1642,1644,1734,2680,2770,2772,2792,3150,3188,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6745 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6745 4 (fun x => (if x<2772 then (if x<1734 then (if x<1642 then 0 else (if x<1644 then 0 else 1)) else (if x<2680 then 1 else (if x<2770 then 1 else 1))) else (if x<3188 then (if x<2792 then 0 else (if x<3150 then 0 else 2)) else (if x<3288 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6746 : Finset ℕ := ([192,252,1622,1628,1642,1644,1734,1738,1740,1776,2638,2680,2770,2772,2776,2788,2792,3150,3188,3192,3282,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6746 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6746 2776 4
  · have he : independentCachedBranchMembers6746.erase 2776=independentCachedBranchMembers6744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6744
  · have he : independentCachedBranchMembers6746.filter (independentCachedEdge 2776)=independentCachedBranchMembers6745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6745
def independentCachedBranchMembers6747 : Finset ℕ := ([192,252,1628,1644,1734,1738,2680,2770,3150,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6747 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6747 4 (fun x => (if x<2680 then (if x<1644 then (if x<252 then 0 else (if x<1628 then 0 else 1)) else (if x<1734 then 2 else (if x<1738 then 1 else 2))) else (if x<3284 then (if x<2770 then 1 else (if x<3150 then 2 else 3)) else (if x<3288 then 0 else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6748 : Finset ℕ := ([192,252,1622,1628,1642,1644,1734,1738,1740,1776,2638,2674,2680,2770,2772,2776,2788,2792,3150,3188,3192,3282,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6748 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6748 2674 4
  · have he : independentCachedBranchMembers6748.erase 2674=independentCachedBranchMembers6746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6746
  · have he : independentCachedBranchMembers6748.filter (independentCachedEdge 2674)=independentCachedBranchMembers6747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6747
def independentCachedBranchMembers6749 : Finset ℕ := ([192,252,1622,1628,1642,1738,2772,2792,3188,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6749 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6749 4 (fun x => (if x<2772 then (if x<1628 then (if x<252 then 0 else (if x<1622 then 0 else 1)) else (if x<1642 then 2 else (if x<1738 then 1 else 2))) else (if x<3284 then (if x<2792 then 0 else (if x<3188 then 0 else 2)) else (if x<3298 then 1 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6750 : Finset ℕ := ([192,252,1622,1626,1628,1642,1644,1734,1738,1740,1776,2638,2674,2680,2770,2772,2776,2788,2792,3150,3188,3192,3282,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6750 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6750 1626 4
  · have he : independentCachedBranchMembers6750.erase 1626=independentCachedBranchMembers6748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6748
  · have he : independentCachedBranchMembers6750.filter (independentCachedEdge 1626)=independentCachedBranchMembers6749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6749
def independentCachedBranchMembers6751 : Finset ℕ := ([252,1622,1628,1644,1734,1740,2638,2772,2788,3150,3188,3284] : List ℕ).toFinset
theorem independentCachedBranchBound6751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6751 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6751 4 (fun x => (if x<2638 then (if x<1644 then (if x<1622 then 0 else (if x<1628 then 1 else 0)) else (if x<1734 then 1 else (if x<1740 then 2 else 3))) else (if x<3150 then (if x<2772 then 1 else (if x<2788 then 0 else 2)) else (if x<3188 then 3 else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
