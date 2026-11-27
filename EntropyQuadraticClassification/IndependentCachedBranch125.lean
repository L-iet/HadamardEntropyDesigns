/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch124
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6784 : Finset ℕ := ([72,192,222,238,252,1614,1628,1644,1650,1734,1738,1748,1752,1764,1768,2638,2652,2668,2674,2758,2762,2772,2776,2788,2792,3158,3162,3174,3178,3188,3192,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6784 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6784 222 4
  · have he : independentCachedBranchMembers6784.erase 222=independentCachedBranchMembers6782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6782
  · have he : independentCachedBranchMembers6784.filter (independentCachedEdge 222)=independentCachedBranchMembers6783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6783
def independentCachedBranchMembers6785 : Finset ℕ := ([72,192,1650,1738,1752,1768,2674,2762,2776,2792,3162,3178,3192,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6785 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6785 4 (fun x => (if x<2776 then (if x<1752 then (if x<1650 then (if x<192 then 0 else 1) else (if x<1738 then 2 else 0)) else (if x<2674 then (if x<1768 then 1 else 2) else (if x<2762 then 3 else 1))) else (if x<3192 then (if x<3162 then (if x<2792 then 0 else 3) else (if x<3178 then 0 else 2)) else (if x<3298 then (if x<3282 then 3 else 1) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6786 : Finset ℕ := ([68,72,192,222,238,252,1614,1628,1644,1650,1734,1738,1748,1752,1764,1768,2638,2652,2668,2674,2758,2762,2772,2776,2788,2792,3158,3162,3174,3178,3188,3192,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6786 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6786 68 4
  · have he : independentCachedBranchMembers6786.erase 68=independentCachedBranchMembers6784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6784
  · have he : independentCachedBranchMembers6786.filter (independentCachedEdge 68)=independentCachedBranchMembers6785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6785
def independentCachedBranchMembers6787 : Finset ℕ := ([66,68,72,80,192,222,238,246,250,252,1614,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2638,2646,2650,2652,2662,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3186,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6787 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6787 3186 5
  · have he : independentCachedBranchMembers6787.erase 3186=independentCachedBranchMembers6771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6771
  · have he : independentCachedBranchMembers6787.filter (independentCachedEdge 3186)=independentCachedBranchMembers6786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6786
def independentCachedBranchMembers6788 : Finset ℕ := ([80,192,246,250,1626,1644,1650,1734,1748,1752,1762,1776,2646,2668,2674,2758,2762,2772,2776,2786,2800,3150,3164,3174,3178,3188,3192,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6788 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6788 5 (fun x => (if x<2758 then (if x<1734 then (if x<250 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<1644 then (if x<1626 then 1 else 2) else (if x<1650 then 2 else 0))) else (if x<1776 then (if x<1752 then (if x<1748 then 2 else 0) else (if x<1762 then 1 else 1)) else (if x<2668 then (if x<2646 then 2 else 0) else (if x<2674 then 3 else 3)))) else (if x<3174 then (if x<2786 then (if x<2772 then (if x<2762 then 3 else 1) else (if x<2776 then 4 else 3)) else (if x<3150 then (if x<2800 then 4 else 0) else (if x<3164 then 2 else 4))) else (if x<3276 then (if x<3188 then (if x<3178 then 3 else 4) else (if x<3192 then 0 else 2)) else (if x<3300 then (if x<3282 then 3 else 0) else (if x<3304 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6789 : Finset ℕ := ([192,246,1626,1644,1734,1748,1762,1776,2646,2674,2762,2776,3174,3188,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6789 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6789 4 (fun x => (if x<2646 then (if x<1734 then (if x<1626 then (if x<246 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<1762 then (if x<1748 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3174 then (if x<2762 then (if x<2674 then 2 else 3) else (if x<2776 then 2 else 3)) else (if x<3276 then (if x<3188 then 3 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6790 : Finset ℕ := ([80,192,246,250,1626,1644,1650,1734,1748,1752,1762,1776,2646,2650,2668,2674,2758,2762,2772,2776,2786,2800,3150,3164,3174,3178,3188,3192,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6790 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6790 2650 4
  · have he : independentCachedBranchMembers6790.erase 2650=independentCachedBranchMembers6788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6788
  · have he : independentCachedBranchMembers6790.filter (independentCachedEdge 2650)=independentCachedBranchMembers6789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6789
def independentCachedBranchMembers6791 : Finset ℕ := ([246,1626,1734,1752,1762,2646,2668,2674,2762,2772,2800,3164,3174,3192,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6791 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6791 4 (fun x => (if x<2674 then (if x<1752 then (if x<1626 then 0 else (if x<1734 then 1 else 0)) else (if x<2646 then (if x<1762 then 2 else 1) else (if x<2668 then 0 else 3))) else (if x<3164 then (if x<2772 then (if x<2762 then 1 else 1) else (if x<2800 then 2 else 3)) else (if x<3192 then (if x<3174 then 2 else 0) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6792 : Finset ℕ := ([1734,1762,2668,2762,3174,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6792 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6792 3 (fun x => (if x<2762 then (if x<1762 then 0 else (if x<2668 then 1 else 2)) else (if x<3174 then 0 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6793 : Finset ℕ := ([80,246,1626,1734,1752,1762,2646,2668,2674,2762,2772,2800,3164,3174,3192,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6793 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6793 80 3
  · have he : independentCachedBranchMembers6793.erase 80=independentCachedBranchMembers6791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6791
  · have he : independentCachedBranchMembers6793.filter (independentCachedEdge 80)=independentCachedBranchMembers6792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6792
def independentCachedBranchMembers6794 : Finset ℕ := ([80,192,246,250,1626,1644,1650,1734,1738,1748,1752,1762,1776,2646,2650,2668,2674,2758,2762,2772,2776,2786,2800,3150,3164,3174,3178,3188,3192,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6794 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6794 1738 4
  · have he : independentCachedBranchMembers6794.erase 1738=independentCachedBranchMembers6790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6790
  · have he : independentCachedBranchMembers6794.filter (independentCachedEdge 1738)=independentCachedBranchMembers6793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6793
def independentCachedBranchMembers6795 : Finset ℕ := ([250,1626,1650,1734,1748,2646,2668,2762,2776,2786,2800,3178,3192,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6795 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6795 4 (fun x => (if x<2762 then (if x<1734 then (if x<1626 then 0 else (if x<1650 then 0 else 1)) else (if x<2646 then (if x<1748 then 1 else 2) else (if x<2668 then 1 else 3))) else (if x<3178 then (if x<2786 then (if x<2776 then 0 else 2) else (if x<2800 then 1 else 3)) else (if x<3276 then (if x<3192 then 0 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6796 : Finset ℕ := ([1626,1650,2646,2668,3178,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6796 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6796 3 (fun x => (if x<2668 then (if x<1650 then 0 else (if x<2646 then 1 else 0)) else (if x<3178 then 2 else (if x<3192 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6797 : Finset ℕ := ([192,250,1626,1650,1734,1748,2646,2668,2762,2776,2786,2800,3178,3192,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6797 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6797 192 3
  · have he : independentCachedBranchMembers6797.erase 192=independentCachedBranchMembers6795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6795
  · have he : independentCachedBranchMembers6797.filter (independentCachedEdge 192)=independentCachedBranchMembers6796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6796
def independentCachedBranchMembers6798 : Finset ℕ := ([80,192,246,250,1622,1626,1644,1650,1734,1738,1748,1752,1762,1776,2646,2650,2668,2674,2758,2762,2772,2776,2786,2800,3150,3164,3174,3178,3188,3192,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6798 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6798 1622 4
  · have he : independentCachedBranchMembers6798.erase 1622=independentCachedBranchMembers6794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6794
  · have he : independentCachedBranchMembers6798.filter (independentCachedEdge 1622)=independentCachedBranchMembers6797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6797
def independentCachedBranchMembers6799 : Finset ℕ := ([246,250,1644,1650,1762,1776,2668,2674,2786,2800,3174,3178,3188,3192,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6799 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6799 4 (fun x => (if x<2786 then (if x<1762 then (if x<1644 then (if x<250 then 0 else 1) else (if x<1650 then 2 else 0)) else (if x<2668 then (if x<1776 then 1 else 2) else (if x<2674 then 3 else 1))) else (if x<3188 then (if x<3174 then (if x<2800 then 0 else 3) else (if x<3178 then 0 else 1)) else (if x<3300 then (if x<3192 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6800 : Finset ℕ := ([80,192,222,246,250,1622,1626,1644,1650,1734,1738,1748,1752,1762,1776,2646,2650,2668,2674,2758,2762,2772,2776,2786,2800,3150,3164,3174,3178,3188,3192,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6800 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6800 222 4
  · have he : independentCachedBranchMembers6800.erase 222=independentCachedBranchMembers6798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6798
  · have he : independentCachedBranchMembers6800.filter (independentCachedEdge 222)=independentCachedBranchMembers6799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6799
def independentCachedBranchMembers6801 : Finset ℕ := ([80,192,1644,1748,1752,1776,2668,2772,2776,2800,3164,3188,3192,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6801 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6801 4 (fun x => (if x<2776 then (if x<1752 then (if x<1644 then (if x<192 then 0 else 1) else (if x<1748 then 2 else 0)) else (if x<2668 then (if x<1776 then 1 else 2) else (if x<2772 then 3 else 1))) else (if x<3192 then (if x<3164 then (if x<2800 then 0 else 3) else (if x<3188 then 0 else 2)) else (if x<3300 then (if x<3276 then 3 else 1) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6802 : Finset ℕ := ([66,80,192,222,246,250,1622,1626,1644,1650,1734,1738,1748,1752,1762,1776,2646,2650,2668,2674,2758,2762,2772,2776,2786,2800,3150,3164,3174,3178,3188,3192,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6802 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6802 66 4
  · have he : independentCachedBranchMembers6802.erase 66=independentCachedBranchMembers6800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6800
  · have he : independentCachedBranchMembers6802.filter (independentCachedEdge 66)=independentCachedBranchMembers6801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6801
def independentCachedBranchMembers6803 : Finset ℕ := ([66,68,72,80,192,222,238,246,250,252,1614,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2638,2646,2650,2652,2662,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6803 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6803 3180 5
  · have he : independentCachedBranchMembers6803.erase 3180=independentCachedBranchMembers6787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6787
  · have he : independentCachedBranchMembers6803.filter (independentCachedEdge 3180)=independentCachedBranchMembers6802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6802
def independentCachedBranchMembers6804 : Finset ℕ := ([72,192,238,250,1626,1642,1652,1734,1740,1752,1762,1768,2652,2662,2668,2674,2680,2762,2772,2788,2800,3150,3178,3188,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6804 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6804 5 (fun x => (if x<2668 then (if x<1734 then (if x<250 then (if x<192 then 0 else (if x<238 then 1 else 0)) else (if x<1642 then (if x<1626 then 1 else 2) else (if x<1652 then 0 else 2))) else (if x<1762 then (if x<1740 then 2 else (if x<1752 then 0 else 1)) else (if x<2652 then (if x<1768 then 1 else 2) else (if x<2662 then 3 else 3)))) else (if x<3150 then (if x<2762 then (if x<2674 then 0 else (if x<2680 then 4 else 2)) else (if x<2788 then (if x<2772 then 0 else 4) else (if x<2800 then 2 else 1))) else (if x<3282 then (if x<3188 then (if x<3178 then 0 else 4) else (if x<3276 then 3 else 4)) else (if x<3298 then (if x<3288 then 1 else 3) else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6805 : Finset ℕ := ([72,250,1626,1642,1652,1734,1752,1768,2652,2668,2674,2800,3150,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6805 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6805 4 (fun x => (if x<2652 then (if x<1652 then (if x<1626 then (if x<250 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3150 then (if x<2674 then (if x<2668 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3282 then (if x<3276 then 3 else 2) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6806 : Finset ℕ := ([72,192,238,250,1626,1642,1652,1734,1740,1752,1762,1768,2652,2662,2668,2674,2680,2762,2772,2788,2800,3150,3178,3188,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6806 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6806 3270 4
  · have he : independentCachedBranchMembers6806.erase 3270=independentCachedBranchMembers6804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6804
  · have he : independentCachedBranchMembers6806.filter (independentCachedEdge 3270)=independentCachedBranchMembers6805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6805
def independentCachedBranchMembers6807 : Finset ℕ := ([192,238,1626,1652,1734,1740,1762,1768,2662,2668,2772,2800,3150,3178,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6807 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6807 4 (fun x => (if x<2662 then (if x<1734 then (if x<1626 then (if x<238 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1762 then (if x<1740 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3150 then (if x<2772 then (if x<2668 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3282 then (if x<3178 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6808 : Finset ℕ := ([72,192,238,250,1626,1642,1652,1734,1740,1752,1762,1768,2652,2662,2668,2674,2680,2762,2772,2788,2800,3150,3162,3178,3188,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6808 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6808 3162 4
  · have he : independentCachedBranchMembers6808.erase 3162=independentCachedBranchMembers6806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6806
  · have he : independentCachedBranchMembers6808.filter (independentCachedEdge 3162)=independentCachedBranchMembers6807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6807
def independentCachedBranchMembers6809 : Finset ℕ := ([72,192,238,250,1642,1740,1752,1762,2652,2662,2674,2772,3178,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6809 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6809 4 (fun x => (if x<2652 then (if x<1642 then (if x<238 then (if x<192 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1752 then (if x<1740 then 0 else 0) else (if x<1762 then 1 else 1))) else (if x<3178 then (if x<2674 then (if x<2662 then 2 else 2) else (if x<2772 then 3 else 3)) else (if x<3288 then (if x<3276 then 3 else 3) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6810 : Finset ℕ := ([72,192,238,250,1626,1642,1652,1734,1740,1752,1762,1768,2646,2652,2662,2668,2674,2680,2762,2772,2788,2800,3150,3162,3178,3188,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6810 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6810 2646 4
  · have he : independentCachedBranchMembers6810.erase 2646=independentCachedBranchMembers6808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6808
  · have he : independentCachedBranchMembers6810.filter (independentCachedEdge 2646)=independentCachedBranchMembers6809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6809
def independentCachedBranchMembers6811 : Finset ℕ := ([72,238,1626,1734,1752,1762,2652,2662,2680,2788,3150,3178,3188,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6811 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6811 4 (fun x => (if x<2680 then (if x<1752 then (if x<1626 then (if x<238 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2652 then (if x<1762 then 2 else 2) else (if x<2662 then 2 else 2))) else (if x<3188 then (if x<3150 then (if x<2788 then 1 else 1) else (if x<3178 then 0 else 3)) else (if x<3282 then (if x<3276 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6812 : Finset ℕ := ([72,192,238,250,1626,1642,1652,1734,1740,1746,1752,1762,1768,2646,2652,2662,2668,2674,2680,2762,2772,2788,2800,3150,3162,3178,3188,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6812 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6812 1746 4
  · have he : independentCachedBranchMembers6812.erase 1746=independentCachedBranchMembers6810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6810
  · have he : independentCachedBranchMembers6812.filter (independentCachedEdge 1746)=independentCachedBranchMembers6811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6811
def independentCachedBranchMembers6813 : Finset ℕ := ([192,250,1626,1642,1734,1740,2674,2680,2772,2788,3150,3188,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6813 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6813 4 (fun x => (if x<2772 then (if x<1734 then (if x<1626 then (if x<250 then 0 else 0) else (if x<1642 then 1 else 2)) else (if x<2674 then (if x<1740 then 1 else 2) else (if x<2680 then 2 else 1))) else (if x<3282 then (if x<3150 then (if x<2788 then 2 else 1) else (if x<3188 then 3 else 3)) else (if x<3298 then (if x<3288 then 0 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6814 : Finset ℕ := ([72,192,238,250,1614,1626,1642,1652,1734,1740,1746,1752,1762,1768,2646,2652,2662,2668,2674,2680,2762,2772,2788,2800,3150,3162,3178,3188,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6814 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6814 1614 4
  · have he : independentCachedBranchMembers6814.erase 1614=independentCachedBranchMembers6812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6812
  · have he : independentCachedBranchMembers6814.filter (independentCachedEdge 1614)=independentCachedBranchMembers6813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6813
def independentCachedBranchMembers6815 : Finset ℕ := ([238,250,1642,1652,1762,1768,2662,2668,2674,2680,2788,2800,3178,3188,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6815 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6815 4 (fun x => (if x<2674 then (if x<1762 then (if x<1642 then (if x<250 then 0 else 1) else (if x<1652 then 0 else 2)) else (if x<2662 then (if x<1768 then 1 else 2) else (if x<2668 then 0 else 2))) else (if x<3178 then (if x<2788 then (if x<2680 then 1 else 3) else (if x<2800 then 3 else 2)) else (if x<3298 then (if x<3188 then 1 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
