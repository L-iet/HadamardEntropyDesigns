/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch120
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6656 : Finset ℕ := ([192,250,252,1626,1628,1650,1652,1734,1746,1748,1768,2646,2680,2764,2776,2786,2800,3158,3192,3274,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6656 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6656 3298 4
  · have he : independentCachedBranchMembers6656.erase 3298=independentCachedBranchMembers6654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6654
  · have he : independentCachedBranchMembers6656.filter (independentCachedEdge 3298)=independentCachedBranchMembers6655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6655
def independentCachedBranchMembers6657 : Finset ℕ := ([250,1626,1652,1746,2646,2680,2764,2786,2800,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6657 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6657 4 (fun x => (if x<2764 then (if x<1746 then (if x<1626 then 0 else (if x<1652 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 1 else 0))) else (if x<3274 then (if x<2786 then 2 else (if x<2800 then 2 else 1)) else (if x<3288 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6658 : Finset ℕ := ([192,250,252,1626,1628,1650,1652,1734,1746,1748,1768,2646,2680,2764,2776,2786,2800,3158,3192,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6658 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6658 3276 4
  · have he : independentCachedBranchMembers6658.erase 3276=independentCachedBranchMembers6656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6656
  · have he : independentCachedBranchMembers6658.filter (independentCachedEdge 3276)=independentCachedBranchMembers6657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6657
def independentCachedBranchMembers6659 : Finset ℕ := ([250,1628,1650,1746,2764,2786,2800,3158,3192,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6659 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6659 4 (fun x => (if x<2800 then (if x<1746 then (if x<1628 then 0 else (if x<1650 then 1 else 0)) else (if x<2764 then 1 else (if x<2786 then 2 else 0))) else (if x<3274 then (if x<3158 then 2 else (if x<3192 then 1 else 3)) else (if x<3288 then 3 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6660 : Finset ℕ := ([192,250,252,1626,1628,1650,1652,1734,1746,1748,1768,2646,2680,2764,2776,2786,2788,2800,3158,3192,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6660 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6660 2788 4
  · have he : independentCachedBranchMembers6660.erase 2788=independentCachedBranchMembers6658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6658
  · have he : independentCachedBranchMembers6660.filter (independentCachedEdge 2788)=independentCachedBranchMembers6659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6659
def independentCachedBranchMembers6661 : Finset ℕ := ([252,1628,1650,1748,2764,2776,2786,3158,3192,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6661 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6661 4 (fun x => (if x<2786 then (if x<1748 then (if x<1628 then 0 else (if x<1650 then 0 else 1)) else (if x<2764 then 1 else (if x<2776 then 0 else 2))) else (if x<3274 then (if x<3158 then 2 else (if x<3192 then 1 else 3)) else (if x<3300 then 2 else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6662 : Finset ℕ := ([192,250,252,1626,1628,1650,1652,1734,1746,1748,1768,2646,2680,2762,2764,2776,2786,2788,2800,3158,3192,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6662 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6662 2762 4
  · have he : independentCachedBranchMembers6662.erase 2762=independentCachedBranchMembers6660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6660
  · have he : independentCachedBranchMembers6662.filter (independentCachedEdge 2762)=independentCachedBranchMembers6661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6661
def independentCachedBranchMembers6663 : Finset ℕ := ([192,250,1626,1650,1734,1748,2680,2764,2788,3158,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6663 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6663 4 (fun x => (if x<2764 then (if x<1650 then (if x<250 then 0 else (if x<1626 then 0 else 1)) else (if x<1748 then (if x<1734 then 2 else 1) else (if x<2680 then 2 else 1))) else (if x<3274 then (if x<2788 then 2 else (if x<3158 then 1 else 3)) else (if x<3298 then (if x<3288 then 0 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6664 : Finset ℕ := ([192,250,252,1626,1628,1650,1652,1734,1746,1748,1768,2646,2668,2680,2762,2764,2776,2786,2788,2800,3158,3192,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6664 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6664 2668 4
  · have he : independentCachedBranchMembers6664.erase 2668=independentCachedBranchMembers6662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6662
  · have he : independentCachedBranchMembers6664.filter (independentCachedEdge 2668)=independentCachedBranchMembers6663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6663
def independentCachedBranchMembers6665 : Finset ℕ := ([192,1650,1652,1734,1746,1748,2646,2786,2788,2800,3158,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6665 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6665 4 (fun x => (if x<2786 then (if x<1734 then (if x<1650 then 0 else (if x<1652 then 1 else 2)) else (if x<1748 then (if x<1746 then 0 else 2) else (if x<2646 then 1 else 1))) else (if x<3158 then (if x<2788 then 0 else (if x<2800 then 3 else 1)) else (if x<3300 then (if x<3298 then 2 else 3) else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6666 : Finset ℕ := ([72,192,250,252,1626,1628,1650,1652,1734,1746,1748,1768,2646,2668,2680,2762,2764,2776,2786,2788,2800,3158,3192,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6666 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6666 72 4
  · have he : independentCachedBranchMembers6666.erase 72=independentCachedBranchMembers6664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6664
  · have he : independentCachedBranchMembers6666.filter (independentCachedEdge 72)=independentCachedBranchMembers6665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6665
def independentCachedBranchMembers6667 : Finset ℕ := ([72,80,192,222,250,252,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1764,1768,1776,2638,2646,2650,2652,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6667 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6667 1622 5
  · have he : independentCachedBranchMembers6667.erase 1622=independentCachedBranchMembers6653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6653
  · have he : independentCachedBranchMembers6667.filter (independentCachedEdge 1622)=independentCachedBranchMembers6666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6666
def independentCachedBranchMembers6668 : Finset ℕ := ([72,222,250,252,1626,1628,1642,1644,1738,1740,1752,2638,2650,2652,2680,2762,2764,2776,2792,3150,3162,3164,3192,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6668 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6668 5 (fun x => (if x<2652 then (if x<1642 then (if x<252 then (if x<222 then 0 else (if x<250 then 0 else 1)) else (if x<1626 then 2 else (if x<1628 then 0 else 2))) else (if x<1740 then (if x<1644 then 1 else (if x<1738 then 3 else 3)) else (if x<2638 then (if x<1752 then 0 else 1) else (if x<2650 then 0 else 1)))) else (if x<3162 then (if x<2764 then (if x<2680 then 4 else (if x<2762 then 2 else 4)) else (if x<2792 then (if x<2776 then 2 else 0) else (if x<3150 then 1 else 3))) else (if x<3274 then (if x<3164 then 4 else (if x<3192 then 0 else 1)) else (if x<3288 then (if x<3276 then 0 else 4) else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6669 : Finset ℕ := ([222,250,1626,1644,1738,1752,2638,2680,2764,2792,3162,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6669 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6669 4 (fun x => (if x<2638 then (if x<1644 then (if x<250 then 0 else (if x<1626 then 1 else 0)) else (if x<1738 then 2 else (if x<1752 then 1 else 2))) else (if x<2792 then (if x<2680 then 0 else (if x<2764 then 2 else 2)) else (if x<3274 then (if x<3162 then 1 else 3) else (if x<3288 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6670 : Finset ℕ := ([250,1738,2638,2680,2764,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6670 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6670 3 (fun x => (if x<2680 then (if x<1738 then 0 else (if x<2638 then 0 else 1)) else (if x<2764 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6671 : Finset ℕ := ([222,250,1626,1644,1738,1752,2638,2652,2680,2764,2792,3162,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6671 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6671 2652 3
  · have he : independentCachedBranchMembers6671.erase 2652=independentCachedBranchMembers6669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6669
  · have he : independentCachedBranchMembers6671.filter (independentCachedEdge 2652)=independentCachedBranchMembers6670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6670
def independentCachedBranchMembers6672 : Finset ℕ := ([72,222,250,252,1626,1628,1642,1644,1738,1740,1752,2638,2650,2652,2668,2680,2762,2764,2776,2792,3150,3162,3164,3192,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6672 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6672 2668 4
  · have he : independentCachedBranchMembers6672.erase 2668=independentCachedBranchMembers6668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6668
  · have he : independentCachedBranchMembers6672.filter (independentCachedEdge 2668)=independentCachedBranchMembers6671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6671
def independentCachedBranchMembers6673 : Finset ℕ := ([222,1642,1644,1738,1740,1752,2638,2652,2792,3150,3162,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6673 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6673 4 (fun x => (if x<2638 then (if x<1738 then (if x<1642 then 0 else (if x<1644 then 1 else 2)) else (if x<1740 then 0 else (if x<1752 then 1 else 2))) else (if x<3150 then (if x<2652 then 0 else (if x<2792 then 2 else 1)) else (if x<3162 then 3 else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6674 : Finset ℕ := ([1642,1738,2652,2792,3150,3162] : List ℕ).toFinset
theorem independentCachedBranchBound6674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6674 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6674 3 (fun x => (if x<2792 then (if x<1738 then 0 else (if x<2652 then 1 else 2)) else (if x<3150 then 0 else (if x<3162 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6675 : Finset ℕ := ([222,1642,1644,1738,1740,1752,2638,2652,2792,3150,3162,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6675 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6675 3164 3
  · have he : independentCachedBranchMembers6675.erase 3164=independentCachedBranchMembers6673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6673
  · have he : independentCachedBranchMembers6675.filter (independentCachedEdge 3164)=independentCachedBranchMembers6674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6674
def independentCachedBranchMembers6676 : Finset ℕ := ([1644,1740,2638,2652,3162,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6676 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6676 3 (fun x => (if x<2652 then (if x<1740 then 0 else (if x<2638 then 1 else 0)) else (if x<3162 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6677 : Finset ℕ := ([222,1642,1644,1738,1740,1752,2638,2650,2652,2792,3150,3162,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6677 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6677 2650 3
  · have he : independentCachedBranchMembers6677.erase 2650=independentCachedBranchMembers6675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6675
  · have he : independentCachedBranchMembers6677.filter (independentCachedEdge 2650)=independentCachedBranchMembers6676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6676
def independentCachedBranchMembers6678 : Finset ℕ := ([72,222,250,252,1626,1628,1642,1644,1738,1740,1752,1768,2638,2650,2652,2668,2680,2762,2764,2776,2792,3150,3162,3164,3192,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6678 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6678 1768 4
  · have he : independentCachedBranchMembers6678.erase 1768=independentCachedBranchMembers6672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6672
  · have he : independentCachedBranchMembers6678.filter (independentCachedEdge 1768)=independentCachedBranchMembers6677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6677
def independentCachedBranchMembers6679 : Finset ℕ := ([72,80,192,222,246,250,252,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1764,1768,1776,2638,2646,2650,2652,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6679 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6679 246 5
  · have he : independentCachedBranchMembers6679.erase 246=independentCachedBranchMembers6667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6667
  · have he : independentCachedBranchMembers6679.filter (independentCachedEdge 246)=independentCachedBranchMembers6678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6678
def independentCachedBranchMembers6680 : Finset ℕ := ([72,80,192,250,1642,1650,1738,1746,1752,1768,1776,2650,2674,2680,2762,2770,2776,2786,2792,2800,3162,3192,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6680 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6680 5 (fun x => (if x<2762 then (if x<1746 then (if x<250 then (if x<80 then 0 else (if x<192 then 1 else 2)) else (if x<1650 then (if x<1642 then 0 else 0) else (if x<1738 then 1 else 2))) else (if x<1776 then (if x<1752 then 3 else (if x<1768 then 0 else 3)) else (if x<2674 then (if x<2650 then 2 else 0) else (if x<2680 then 4 else 1)))) else (if x<3192 then (if x<2786 then (if x<2770 then 3 else (if x<2776 then 1 else 2)) else (if x<2800 then (if x<2792 then 2 else 0) else (if x<3162 then 3 else 1))) else (if x<3288 then (if x<3274 then 0 else (if x<3282 then 0 else 2)) else (if x<3304 then (if x<3298 then 3 else 3) else (if x<3312 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6681 : Finset ℕ := ([192,1642,1650,1738,1746,1752,2650,2786,2800,3162,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6681 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6681 4 (fun x => (if x<2650 then (if x<1738 then (if x<1642 then 0 else (if x<1650 then 1 else 2)) else (if x<1746 then 0 else (if x<1752 then 1 else 2))) else (if x<3162 then (if x<2786 then 1 else (if x<2800 then 0 else 2)) else (if x<3298 then 3 else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6682 : Finset ℕ := ([1642,1738,2650,2800,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6682 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6682 3 (fun x => (if x<2800 then (if x<1738 then 0 else (if x<2650 then 1 else 0)) else (if x<3298 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6683 : Finset ℕ := ([192,1642,1650,1738,1746,1752,2650,2786,2800,3162,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6683 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6683 3312 3
  · have he : independentCachedBranchMembers6683.erase 3312=independentCachedBranchMembers6681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6681
  · have he : independentCachedBranchMembers6683.filter (independentCachedEdge 3312)=independentCachedBranchMembers6682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6682
def independentCachedBranchMembers6684 : Finset ℕ := ([1650,1746,2786,2800,3162,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6684 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6684 3 (fun x => (if x<2800 then (if x<1746 then 0 else (if x<2786 then 1 else 0)) else (if x<3162 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6685 : Finset ℕ := ([192,1642,1650,1738,1746,1752,2650,2786,2792,2800,3162,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6685 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6685 2792 3
  · have he : independentCachedBranchMembers6685.erase 2792=independentCachedBranchMembers6683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6683
  · have he : independentCachedBranchMembers6685.filter (independentCachedEdge 2792)=independentCachedBranchMembers6684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6684
def independentCachedBranchMembers6686 : Finset ℕ := ([72,80,192,250,1626,1642,1650,1738,1746,1752,1768,1776,2650,2674,2680,2762,2770,2776,2786,2792,2800,3162,3192,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6686 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6686 1626 4
  · have he : independentCachedBranchMembers6686.erase 1626=independentCachedBranchMembers6680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6680
  · have he : independentCachedBranchMembers6686.filter (independentCachedEdge 1626)=independentCachedBranchMembers6685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6685
def independentCachedBranchMembers6687 : Finset ℕ := ([68,72,80,192,222,246,250,252,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1764,1768,1776,2638,2646,2650,2652,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3188,3192,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6687 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6687 68 5
  · have he : independentCachedBranchMembers6687.erase 68=independentCachedBranchMembers6679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6679
  · have he : independentCachedBranchMembers6687.filter (independentCachedEdge 68)=independentCachedBranchMembers6686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6686
end EntropyDesigns.QuadraticRefinement
