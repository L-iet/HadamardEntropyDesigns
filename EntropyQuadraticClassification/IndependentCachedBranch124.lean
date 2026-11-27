/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch123
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6752 : Finset ℕ := ([192,250,252,1622,1626,1628,1642,1644,1734,1738,1740,1776,2638,2674,2680,2770,2772,2776,2788,2792,3150,3188,3192,3282,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6752 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6752 250 4
  · have he : independentCachedBranchMembers6752.erase 250=independentCachedBranchMembers6750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6750
  · have he : independentCachedBranchMembers6752.filter (independentCachedEdge 250)=independentCachedBranchMembers6751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6751
def independentCachedBranchMembers6753 : Finset ℕ := ([192,1642,1644,1734,1738,1740,2638,2788,2792,3150,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6753 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6753 4 (fun x => (if x<2638 then (if x<1734 then (if x<1642 then 0 else (if x<1644 then 1 else 2)) else (if x<1738 then 0 else (if x<1740 then 2 else 1))) else (if x<3150 then (if x<2788 then 1 else (if x<2792 then 0 else 1)) else (if x<3298 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6754 : Finset ℕ := ([80,192,250,252,1622,1626,1628,1642,1644,1734,1738,1740,1776,2638,2674,2680,2770,2772,2776,2788,2792,3150,3188,3192,3282,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6754 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6754 80 4
  · have he : independentCachedBranchMembers6754.erase 80=independentCachedBranchMembers6752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6752
  · have he : independentCachedBranchMembers6754.filter (independentCachedEdge 80)=independentCachedBranchMembers6753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6753
def independentCachedBranchMembers6755 : Finset ℕ := ([250,1622,1628,1642,1738,2638,2674,2680,2770,2776,2788,3188,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6755 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6755 4 (fun x => (if x<2680 then (if x<1642 then (if x<1622 then 0 else (if x<1628 then 1 else 2)) else (if x<2638 then (if x<1738 then 0 else 1) else (if x<2674 then 1 else 0))) else (if x<3188 then (if x<2776 then (if x<2770 then 2 else 1) else (if x<2788 then 3 else 3)) else (if x<3298 then (if x<3284 then 2 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6756 : Finset ℕ := ([1642,1738,2638,2788,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6756 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6756 3 (fun x => (if x<2788 then (if x<1738 then 0 else (if x<2638 then 1 else 0)) else (if x<3298 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6757 : Finset ℕ := ([80,250,1622,1628,1642,1738,2638,2674,2680,2770,2776,2788,3188,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6757 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6757 80 3
  · have he : independentCachedBranchMembers6757.erase 80=independentCachedBranchMembers6755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6755
  · have he : independentCachedBranchMembers6757.filter (independentCachedEdge 80)=independentCachedBranchMembers6756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6756
def independentCachedBranchMembers6758 : Finset ℕ := ([80,192,250,252,1622,1626,1628,1642,1644,1734,1738,1740,1776,2638,2674,2680,2770,2772,2776,2788,2792,3150,3188,3192,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6758 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6758 3300 4
  · have he : independentCachedBranchMembers6758.erase 3300=independentCachedBranchMembers6754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6754
  · have he : independentCachedBranchMembers6758.filter (independentCachedEdge 3300)=independentCachedBranchMembers6757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6757
def independentCachedBranchMembers6759 : Finset ℕ := ([80,252,1622,1626,1644,1740,2674,2770,2788,2792,3150,3188,3192,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6759 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6759 4 (fun x => (if x<2788 then (if x<1644 then (if x<1622 then (if x<252 then 0 else 0) else (if x<1626 then 1 else 2)) else (if x<2674 then (if x<1740 then 1 else 2) else (if x<2770 then 2 else 1))) else (if x<3192 then (if x<3150 then (if x<2792 then 2 else 1) else (if x<3188 then 3 else 0)) else (if x<3288 then (if x<3284 then 3 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6760 : Finset ℕ := ([80,192,250,252,1622,1626,1628,1642,1644,1734,1738,1740,1776,2638,2674,2680,2770,2772,2776,2786,2788,2792,3150,3188,3192,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6760 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6760 2786 4
  · have he : independentCachedBranchMembers6760.erase 2786=independentCachedBranchMembers6758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6758
  · have he : independentCachedBranchMembers6760.filter (independentCachedEdge 2786)=independentCachedBranchMembers6759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6759
def independentCachedBranchMembers6761 : Finset ℕ := ([250,252,1626,1628,1642,1644,1738,1740,2638,2680,2776,2792,3150,3192,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6761 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6761 4 (fun x => (if x<2638 then (if x<1642 then (if x<1626 then (if x<252 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1738 then (if x<1644 then 2 else 3) else (if x<1740 then 3 else 2))) else (if x<3150 then (if x<2776 then (if x<2680 then 2 else 0) else (if x<2792 then 1 else 2)) else (if x<3288 then (if x<3192 then 3 else 1) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6762 : Finset ℕ := ([80,192,246,250,252,1622,1626,1628,1642,1644,1734,1738,1740,1776,2638,2674,2680,2770,2772,2776,2786,2788,2792,3150,3188,3192,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6762 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6762 246 4
  · have he : independentCachedBranchMembers6762.erase 246=independentCachedBranchMembers6760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6760
  · have he : independentCachedBranchMembers6762.filter (independentCachedEdge 246)=independentCachedBranchMembers6761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6761
def independentCachedBranchMembers6763 : Finset ℕ := ([68,72,80,192,222,246,250,252,1614,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2638,2646,2650,2652,2662,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6763 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6763 1614 5
  · have he : independentCachedBranchMembers6763.erase 1614=independentCachedBranchMembers6737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6737
  · have he : independentCachedBranchMembers6763.filter (independentCachedEdge 1614)=independentCachedBranchMembers6762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6762
def independentCachedBranchMembers6764 : Finset ℕ := ([80,222,246,250,252,1626,1628,1650,1652,1746,1748,1752,1776,2646,2652,2674,2680,2770,2772,2776,2800,3158,3162,3164,3188,3192,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6764 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6764 5 (fun x => (if x<2674 then (if x<1650 then (if x<250 then (if x<222 then 0 else (if x<246 then 0 else 1)) else (if x<1626 then (if x<252 then 2 else 3) else (if x<1628 then 0 else 3))) else (if x<1752 then (if x<1746 then (if x<1652 then 1 else 4) else (if x<1748 then 2 else 0)) else (if x<2646 then (if x<1776 then 4 else 3) else (if x<2652 then 0 else 4)))) else (if x<3162 then (if x<2772 then (if x<2680 then 2 else (if x<2770 then 3 else 1)) else (if x<2800 then (if x<2776 then 3 else 0) else (if x<3158 then 4 else 1))) else (if x<3282 then (if x<3188 then (if x<3164 then 2 else 0) else (if x<3192 then 3 else 4)) else (if x<3288 then (if x<3284 then 0 else 4) else (if x<3312 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6765 : Finset ℕ := ([246,252,1626,1652,1748,1776,2646,2652,2674,2680,2770,2776,3162,3188,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6765 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6765 4 (fun x => (if x<2674 then (if x<1748 then (if x<1626 then (if x<252 then 0 else 1) else (if x<1652 then 2 else 0)) else (if x<2646 then (if x<1776 then 1 else 2) else (if x<2652 then 0 else 1))) else (if x<3162 then (if x<2770 then (if x<2680 then 2 else 3) else (if x<2776 then 3 else 2)) else (if x<3284 then (if x<3188 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6766 : Finset ℕ := ([80,222,246,250,252,1626,1628,1650,1652,1746,1748,1752,1776,2646,2650,2652,2674,2680,2770,2772,2776,2800,3158,3162,3164,3188,3192,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6766 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6766 2650 4
  · have he : independentCachedBranchMembers6766.erase 2650=independentCachedBranchMembers6764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6764
  · have he : independentCachedBranchMembers6766.filter (independentCachedEdge 2650)=independentCachedBranchMembers6765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6765
def independentCachedBranchMembers6767 : Finset ℕ := ([250,252,1626,1628,1650,1652,1746,1748,2646,2680,2776,2800,3158,3192,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6767 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6767 4 (fun x => (if x<2646 then (if x<1650 then (if x<1626 then (if x<252 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1746 then (if x<1652 then 2 else 3) else (if x<1748 then 3 else 2))) else (if x<3158 then (if x<2776 then (if x<2680 then 2 else 0) else (if x<2800 then 1 else 2)) else (if x<3288 then (if x<3192 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6768 : Finset ℕ := ([80,222,246,250,252,1622,1626,1628,1650,1652,1746,1748,1752,1776,2646,2650,2652,2674,2680,2770,2772,2776,2800,3158,3162,3164,3188,3192,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6768 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6768 1622 4
  · have he : independentCachedBranchMembers6768.erase 1622=independentCachedBranchMembers6766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6766
  · have he : independentCachedBranchMembers6768.filter (independentCachedEdge 1622)=independentCachedBranchMembers6767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6767
def independentCachedBranchMembers6769 : Finset ℕ := ([68,72,80,192,222,238,246,250,252,1614,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2638,2646,2650,2652,2662,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6769 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6769 238 5
  · have he : independentCachedBranchMembers6769.erase 238=independentCachedBranchMembers6763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6763
  · have he : independentCachedBranchMembers6769.filter (independentCachedEdge 238)=independentCachedBranchMembers6768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6768
def independentCachedBranchMembers6770 : Finset ℕ := ([68,72,80,192,252,1628,1644,1652,1740,1748,1752,1764,1768,1776,2652,2668,2680,2764,2772,2776,2788,2792,2800,3164,3188,3192,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6770 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6770 5 (fun x => (if x<2680 then (if x<1740 then (if x<252 then (if x<80 then (if x<72 then 0 else 1) else (if x<192 then 2 else 3)) else (if x<1644 then (if x<1628 then 0 else 0) else (if x<1652 then 1 else 2))) else (if x<1768 then (if x<1752 then (if x<1748 then 3 else 4) else (if x<1764 then 1 else 0)) else (if x<2652 then (if x<1776 then 4 else 3) else (if x<2668 then 1 else 0)))) else (if x<3188 then (if x<2788 then (if x<2772 then (if x<2764 then 2 else 4) else (if x<2776 then 0 else 3)) else (if x<2800 then (if x<2792 then 3 else 1) else (if x<3164 then 4 else 2))) else (if x<3288 then (if x<3276 then (if x<3192 then 0 else 1) else (if x<3284 then 0 else 3)) else (if x<3304 then (if x<3300 then 4 else 4) else (if x<3312 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6771 : Finset ℕ := ([66,68,72,80,192,222,238,246,250,252,1614,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2638,2646,2650,2652,2662,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6771 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6771 66 5
  · have he : independentCachedBranchMembers6771.erase 66=independentCachedBranchMembers6769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6769
  · have he : independentCachedBranchMembers6771.filter (independentCachedEdge 66)=independentCachedBranchMembers6770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6770
def independentCachedBranchMembers6772 : Finset ℕ := ([72,192,238,252,1628,1644,1650,1734,1738,1752,1764,1768,2638,2668,2674,2758,2762,2772,2776,2788,2792,3158,3162,3174,3178,3188,3192,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6772 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6772 5 (fun x => (if x<2758 then (if x<1734 then (if x<252 then (if x<192 then 0 else (if x<238 then 1 else 0)) else (if x<1644 then (if x<1628 then 1 else 2) else (if x<1650 then 0 else 2))) else (if x<1768 then (if x<1752 then (if x<1738 then 2 else 0) else (if x<1764 then 1 else 1)) else (if x<2668 then (if x<2638 then 2 else 0) else (if x<2674 then 3 else 3)))) else (if x<3174 then (if x<2788 then (if x<2772 then (if x<2762 then 3 else 4) else (if x<2776 then 1 else 3)) else (if x<3158 then (if x<2792 then 4 else 0) else (if x<3162 then 2 else 4))) else (if x<3276 then (if x<3188 then (if x<3178 then 3 else 0) else (if x<3192 then 4 else 2)) else (if x<3298 then (if x<3282 then 0 else 3) else (if x<3312 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6773 : Finset ℕ := ([192,238,1628,1650,1734,1738,1764,1768,2638,2668,2772,2776,3174,3178,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6773 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6773 4 (fun x => (if x<2638 then (if x<1734 then (if x<1628 then (if x<238 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1764 then (if x<1738 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3174 then (if x<2772 then (if x<2668 then 2 else 3) else (if x<2776 then 2 else 3)) else (if x<3282 then (if x<3178 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6774 : Finset ℕ := ([72,192,238,252,1628,1644,1650,1734,1738,1752,1764,1768,2638,2652,2668,2674,2758,2762,2772,2776,2788,2792,3158,3162,3174,3178,3188,3192,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6774 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6774 2652 4
  · have he : independentCachedBranchMembers6774.erase 2652=independentCachedBranchMembers6772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6772
  · have he : independentCachedBranchMembers6774.filter (independentCachedEdge 2652)=independentCachedBranchMembers6773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6773
def independentCachedBranchMembers6775 : Finset ℕ := ([238,1628,1734,1752,1764,2638,2668,2674,2762,2772,2792,3162,3174,3192,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6775 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6775 4 (fun x => (if x<2674 then (if x<1752 then (if x<1628 then 0 else (if x<1734 then 1 else 0)) else (if x<2638 then (if x<1764 then 2 else 1) else (if x<2668 then 0 else 1))) else (if x<3162 then (if x<2772 then (if x<2762 then 3 else 2) else (if x<2792 then 1 else 3)) else (if x<3192 then (if x<3174 then 2 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6776 : Finset ℕ := ([1734,1764,2674,2772,3174,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6776 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6776 3 (fun x => (if x<2772 then (if x<1764 then 0 else (if x<2674 then 1 else 2)) else (if x<3174 then 0 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6777 : Finset ℕ := ([72,238,1628,1734,1752,1764,2638,2668,2674,2762,2772,2792,3162,3174,3192,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6777 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6777 72 3
  · have he : independentCachedBranchMembers6777.erase 72=independentCachedBranchMembers6775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6775
  · have he : independentCachedBranchMembers6777.filter (independentCachedEdge 72)=independentCachedBranchMembers6776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6776
def independentCachedBranchMembers6778 : Finset ℕ := ([72,192,238,252,1628,1644,1650,1734,1738,1748,1752,1764,1768,2638,2652,2668,2674,2758,2762,2772,2776,2788,2792,3158,3162,3174,3178,3188,3192,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6778 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6778 1748 4
  · have he : independentCachedBranchMembers6778.erase 1748=independentCachedBranchMembers6774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6774
  · have he : independentCachedBranchMembers6778.filter (independentCachedEdge 1748)=independentCachedBranchMembers6777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6777
def independentCachedBranchMembers6779 : Finset ℕ := ([252,1628,1644,1734,1738,2638,2674,2772,2776,2788,2792,3188,3192,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6779 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6779 4 (fun x => (if x<2772 then (if x<1734 then (if x<1628 then 0 else (if x<1644 then 0 else 1)) else (if x<2638 then (if x<1738 then 1 else 2) else (if x<2674 then 1 else 3))) else (if x<3188 then (if x<2788 then (if x<2776 then 0 else 2) else (if x<2792 then 1 else 3)) else (if x<3282 then (if x<3192 then 0 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6780 : Finset ℕ := ([1628,1644,2638,2674,3188,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6780 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6780 3 (fun x => (if x<2674 then (if x<1644 then 0 else (if x<2638 then 1 else 0)) else (if x<3188 then 2 else (if x<3192 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6781 : Finset ℕ := ([192,252,1628,1644,1734,1738,2638,2674,2772,2776,2788,2792,3188,3192,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6781 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6781 192 3
  · have he : independentCachedBranchMembers6781.erase 192=independentCachedBranchMembers6779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6779
  · have he : independentCachedBranchMembers6781.filter (independentCachedEdge 192)=independentCachedBranchMembers6780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6780
def independentCachedBranchMembers6782 : Finset ℕ := ([72,192,238,252,1614,1628,1644,1650,1734,1738,1748,1752,1764,1768,2638,2652,2668,2674,2758,2762,2772,2776,2788,2792,3158,3162,3174,3178,3188,3192,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6782 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6782 1614 4
  · have he : independentCachedBranchMembers6782.erase 1614=independentCachedBranchMembers6778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6778
  · have he : independentCachedBranchMembers6782.filter (independentCachedEdge 1614)=independentCachedBranchMembers6781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6781
def independentCachedBranchMembers6783 : Finset ℕ := ([238,252,1644,1650,1764,1768,2668,2674,2788,2792,3174,3178,3188,3192,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6783 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6783 4 (fun x => (if x<2788 then (if x<1764 then (if x<1644 then (if x<252 then 0 else 1) else (if x<1650 then 0 else 2)) else (if x<2668 then (if x<1768 then 1 else 2) else (if x<2674 then 1 else 3))) else (if x<3188 then (if x<3174 then (if x<2792 then 0 else 3) else (if x<3178 then 0 else 2)) else (if x<3298 then (if x<3192 then 1 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
