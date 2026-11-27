/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch125
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6816 : Finset ℕ := ([72,192,222,238,250,1614,1626,1642,1652,1734,1740,1746,1752,1762,1768,2646,2652,2662,2668,2674,2680,2762,2772,2788,2800,3150,3162,3178,3188,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6816 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6816 222 4
  · have he : independentCachedBranchMembers6816.erase 222=independentCachedBranchMembers6814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6814
  · have he : independentCachedBranchMembers6816.filter (independentCachedEdge 222)=independentCachedBranchMembers6815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6815
def independentCachedBranchMembers6817 : Finset ℕ := ([72,192,1652,1740,1752,1768,2652,2668,2680,2772,2788,2800,3188,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6817 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6817 4 (fun x => (if x<2680 then (if x<1752 then (if x<1652 then (if x<192 then 0 else 1) else (if x<1740 then 2 else 0)) else (if x<2652 then (if x<1768 then 1 else 2) else (if x<2668 then 0 else 2))) else (if x<3188 then (if x<2788 then (if x<2772 then 3 else 1) else (if x<2800 then 3 else 2)) else (if x<3288 then (if x<3276 then 3 else 1) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6818 : Finset ℕ := ([66,72,192,222,238,250,1614,1626,1642,1652,1734,1740,1746,1752,1762,1768,2646,2652,2662,2668,2674,2680,2762,2772,2788,2800,3150,3162,3178,3188,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6818 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6818 66 4
  · have he : independentCachedBranchMembers6818.erase 66=independentCachedBranchMembers6816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6816
  · have he : independentCachedBranchMembers6818.filter (independentCachedEdge 66)=independentCachedBranchMembers6817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6817
def independentCachedBranchMembers6819 : Finset ℕ := ([66,68,72,80,192,222,238,246,250,252,1614,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2638,2646,2650,2652,2662,2668,2674,2676,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6819 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6819 2676 5
  · have he : independentCachedBranchMembers6819.erase 2676=independentCachedBranchMembers6803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6803
  · have he : independentCachedBranchMembers6819.filter (independentCachedEdge 2676)=independentCachedBranchMembers6818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6818
def independentCachedBranchMembers6820 : Finset ℕ := ([80,192,246,252,1628,1642,1652,1734,1746,1752,1764,1776,2650,2662,2668,2674,2680,2762,2772,2786,2792,3158,3178,3188,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6820 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6820 5 (fun x => (if x<2668 then (if x<1734 then (if x<252 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<1642 then (if x<1628 then 1 else 2) else (if x<1652 then 2 else 0))) else (if x<1764 then (if x<1746 then 2 else (if x<1752 then 0 else 1)) else (if x<2650 then (if x<1776 then 1 else 2) else (if x<2662 then 3 else 3)))) else (if x<3158 then (if x<2762 then (if x<2674 then 4 else (if x<2680 then 0 else 2)) else (if x<2786 then (if x<2772 then 4 else 0) else (if x<2792 then 2 else 1))) else (if x<3282 then (if x<3188 then (if x<3178 then 0 else 3) else (if x<3276 then 4 else 1)) else (if x<3300 then (if x<3288 then 4 else 3) else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6821 : Finset ℕ := ([80,252,1628,1642,1652,1734,1752,1776,2650,2668,2674,2792,3158,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6821 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6821 4 (fun x => (if x<2650 then (if x<1652 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3158 then (if x<2674 then (if x<2668 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3282 then (if x<3276 then 3 else 3) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6822 : Finset ℕ := ([80,192,246,252,1628,1642,1652,1734,1746,1752,1764,1776,2650,2662,2668,2674,2680,2762,2772,2786,2792,3158,3178,3188,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6822 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6822 3270 4
  · have he : independentCachedBranchMembers6822.erase 3270=independentCachedBranchMembers6820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6820
  · have he : independentCachedBranchMembers6822.filter (independentCachedEdge 3270)=independentCachedBranchMembers6821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6821
def independentCachedBranchMembers6823 : Finset ℕ := ([192,246,1628,1642,1734,1746,1764,1776,2662,2674,2762,2792,3158,3188,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6823 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6823 4 (fun x => (if x<2662 then (if x<1734 then (if x<1628 then (if x<246 then 0 else 0) else (if x<1642 then 1 else 1)) else (if x<1764 then (if x<1746 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3158 then (if x<2762 then (if x<2674 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3276 then (if x<3188 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6824 : Finset ℕ := ([80,192,246,252,1628,1642,1652,1734,1746,1752,1764,1776,2650,2662,2668,2674,2680,2762,2772,2786,2792,3158,3164,3178,3188,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6824 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6824 3164 4
  · have he : independentCachedBranchMembers6824.erase 3164=independentCachedBranchMembers6822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6822
  · have he : independentCachedBranchMembers6824.filter (independentCachedEdge 3164)=independentCachedBranchMembers6823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6823
def independentCachedBranchMembers6825 : Finset ℕ := ([80,192,246,252,1652,1746,1752,1764,2650,2662,2668,2762,3188,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6825 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6825 4 (fun x => (if x<2650 then (if x<1652 then (if x<246 then (if x<192 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1752 then (if x<1746 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3188 then (if x<2668 then (if x<2662 then 2 else 2) else (if x<2762 then 3 else 3)) else (if x<3288 then (if x<3282 then 3 else 3) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6826 : Finset ℕ := ([80,192,246,252,1628,1642,1652,1734,1746,1752,1764,1776,2638,2650,2662,2668,2674,2680,2762,2772,2786,2792,3158,3164,3178,3188,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6826 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6826 2638 4
  · have he : independentCachedBranchMembers6826.erase 2638=independentCachedBranchMembers6824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6824
  · have he : independentCachedBranchMembers6826.filter (independentCachedEdge 2638)=independentCachedBranchMembers6825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6825
def independentCachedBranchMembers6827 : Finset ℕ := ([80,246,1628,1734,1752,1764,2650,2662,2680,2786,3158,3178,3188,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6827 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6827 4 (fun x => (if x<2680 then (if x<1752 then (if x<1628 then (if x<246 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2650 then (if x<1764 then 2 else 2) else (if x<2662 then 2 else 2))) else (if x<3188 then (if x<3158 then (if x<2786 then 1 else 1) else (if x<3178 then 0 else 3)) else (if x<3282 then (if x<3276 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6828 : Finset ℕ := ([80,192,246,252,1628,1642,1652,1734,1740,1746,1752,1764,1776,2638,2650,2662,2668,2674,2680,2762,2772,2786,2792,3158,3164,3178,3188,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6828 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6828 1740 4
  · have he : independentCachedBranchMembers6828.erase 1740=independentCachedBranchMembers6826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6826
  · have he : independentCachedBranchMembers6828.filter (independentCachedEdge 1740)=independentCachedBranchMembers6827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6827
def independentCachedBranchMembers6829 : Finset ℕ := ([192,252,1628,1652,1734,1746,2668,2680,2762,2786,3158,3178,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6829 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6829 4 (fun x => (if x<2762 then (if x<1734 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<2668 then (if x<1746 then 1 else 2) else (if x<2680 then 2 else 1))) else (if x<3276 then (if x<3158 then (if x<2786 then 2 else 1) else (if x<3178 then 3 else 3)) else (if x<3300 then (if x<3288 then 0 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6830 : Finset ℕ := ([80,192,246,252,1622,1628,1642,1652,1734,1740,1746,1752,1764,1776,2638,2650,2662,2668,2674,2680,2762,2772,2786,2792,3158,3164,3178,3188,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6830 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6830 1622 4
  · have he : independentCachedBranchMembers6830.erase 1622=independentCachedBranchMembers6828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6828
  · have he : independentCachedBranchMembers6830.filter (independentCachedEdge 1622)=independentCachedBranchMembers6829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6829
def independentCachedBranchMembers6831 : Finset ℕ := ([246,252,1642,1652,1764,1776,2662,2668,2674,2680,2786,2792,3178,3188,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6831 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6831 4 (fun x => (if x<2674 then (if x<1764 then (if x<1642 then (if x<252 then 0 else 1) else (if x<1652 then 2 else 0)) else (if x<2662 then (if x<1776 then 1 else 2) else (if x<2668 then 0 else 1))) else (if x<3178 then (if x<2786 then (if x<2680 then 2 else 3) else (if x<2792 then 3 else 2)) else (if x<3300 then (if x<3188 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6832 : Finset ℕ := ([80,192,222,246,252,1622,1628,1642,1652,1734,1740,1746,1752,1764,1776,2638,2650,2662,2668,2674,2680,2762,2772,2786,2792,3158,3164,3178,3188,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6832 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6832 222 4
  · have he : independentCachedBranchMembers6832.erase 222=independentCachedBranchMembers6830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6830
  · have he : independentCachedBranchMembers6832.filter (independentCachedEdge 222)=independentCachedBranchMembers6831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6831
def independentCachedBranchMembers6833 : Finset ℕ := ([80,192,1642,1746,1752,1776,2650,2674,2680,2762,2786,2792,3178,3282,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6833 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6833 4 (fun x => (if x<2680 then (if x<1752 then (if x<1642 then (if x<192 then 0 else 1) else (if x<1746 then 2 else 0)) else (if x<2650 then (if x<1776 then 1 else 2) else (if x<2674 then 0 else 2))) else (if x<3178 then (if x<2786 then (if x<2762 then 3 else 1) else (if x<2792 then 3 else 2)) else (if x<3288 then (if x<3282 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6834 : Finset ℕ := ([68,80,192,222,246,252,1622,1628,1642,1652,1734,1740,1746,1752,1764,1776,2638,2650,2662,2668,2674,2680,2762,2772,2786,2792,3158,3164,3178,3188,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6834 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6834 68 4
  · have he : independentCachedBranchMembers6834.erase 68=independentCachedBranchMembers6832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6832
  · have he : independentCachedBranchMembers6834.filter (independentCachedEdge 68)=independentCachedBranchMembers6833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6833
def independentCachedBranchMembers6835 : Finset ℕ := ([66,68,72,80,192,222,238,246,250,252,1614,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6835 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6835 2666 5
  · have he : independentCachedBranchMembers6835.erase 2666=independentCachedBranchMembers6819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6819
  · have he : independentCachedBranchMembers6835.filter (independentCachedEdge 2666)=independentCachedBranchMembers6834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6834
def independentCachedBranchMembers6836 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,190,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6836 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6836 190 6
  · have he : independentCachedBranchMembers6836.erase 190=independentCachedBranchMembers6580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6580
  · have he : independentCachedBranchMembers6836.filter (independentCachedEdge 190)=independentCachedBranchMembers6835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6835
def independentCachedBranchMembers6837 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2680,2714,2716,2758,2762,2770,3130,3132,3174,3188,3222,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6837 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6837 6 (fun x => (if x<2614 then (if x<1644 then (if x<192 then (if x<130 then (if x<48 then 0 else 1) else (if x<136 then 0 else 1)) else (if x<1590 then (if x<222 then 2 else 2) else (if x<1596 then 1 else 0))) else (if x<1734 then (if x<1678 then (if x<1650 then 3 else 3) else (if x<1690 then 1 else 0)) else (if x<1748 then (if x<1738 then 2 else 3) else (if x<1752 then 3 else 2)))) else (if x<3132 then (if x<2758 then (if x<2714 then (if x<2680 then 4 else 4) else (if x<2716 then 4 else 5)) else (if x<2770 then (if x<2762 then 5 else 0) else (if x<3130 then 2 else 4))) else (if x<3274 then (if x<3188 then (if x<3174 then 5 else 5) else (if x<3222 then 0 else 4)) else (if x<3282 then (if x<3276 then 1 else 3) else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6838 : Finset ℕ := ([48,130,136,222,1650,1690,1734,1738,2680,2714,2716,2758,2762,3130,3132,3174,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6838 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6838 5 (fun x => (if x<2714 then (if x<1650 then (if x<136 then (if x<130 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1734 then (if x<1690 then 2 else 1) else (if x<1738 then 0 else (if x<2680 then 2 else 0)))) else (if x<3130 then (if x<2758 then (if x<2716 then 3 else 1) else (if x<2762 then 3 else 0)) else (if x<3174 then (if x<3132 then 3 else 0) else (if x<3282 then 3 else (if x<3288 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6839 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2680,2714,2716,2758,2762,2770,3118,3130,3132,3174,3188,3222,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6839 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6839 3118 5
  · have he : independentCachedBranchMembers6839.erase 3118=independentCachedBranchMembers6837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6837
  · have he : independentCachedBranchMembers6839.filter (independentCachedEdge 3118)=independentCachedBranchMembers6838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6838
def independentCachedBranchMembers6840 : Finset ℕ := ([36,192,1590,1596,1644,1678,1748,1752,2680,2714,2716,2758,2762,3130,3132,3174,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6840 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6840 5 (fun x => (if x<2714 then (if x<1644 then (if x<1590 then (if x<192 then 0 else 0) else (if x<1596 then 0 else 1)) else (if x<1748 then (if x<1678 then 2 else 1) else (if x<1752 then 1 else (if x<2680 then 2 else 2)))) else (if x<3130 then (if x<2758 then (if x<2716 then 2 else 1) else (if x<2762 then 1 else 0)) else (if x<3174 then (if x<3132 then 3 else 0) else (if x<3282 then 3 else (if x<3288 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6841 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2680,2702,2714,2716,2758,2762,2770,3118,3130,3132,3174,3188,3222,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6841 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6841 2702 5
  · have he : independentCachedBranchMembers6841.erase 2702=independentCachedBranchMembers6839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6839
  · have he : independentCachedBranchMembers6841.filter (independentCachedEdge 2702)=independentCachedBranchMembers6840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6840
def independentCachedBranchMembers6842 : Finset ℕ := ([48,136,192,222,1590,1644,1650,1678,1734,1738,1748,1752,2680,2714,2770,3130,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6842 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6842 5 (fun x => (if x<1738 then (if x<1590 then (if x<192 then (if x<136 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1650 then (if x<1644 then 0 else 2) else (if x<1678 then 2 else (if x<1734 then 0 else 1)))) else (if x<2714 then (if x<1752 then (if x<1748 then 2 else 2) else (if x<2680 then 1 else 3)) else (if x<3130 then (if x<2770 then 3 else 1) else (if x<3274 then 3 else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6843 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2668,2680,2702,2714,2716,2758,2762,2770,3118,3130,3132,3174,3188,3222,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6843 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6843 2668 5
  · have he : independentCachedBranchMembers6843.erase 2668=independentCachedBranchMembers6841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6841
  · have he : independentCachedBranchMembers6843.filter (independentCachedEdge 2668)=independentCachedBranchMembers6842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6842
def independentCachedBranchMembers6844 : Finset ℕ := ([36,136,192,222,1590,1690,1738,1748,2614,2680,2714,2716,2762,2770,3130,3132,3188,3222,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6844 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6844 5 (fun x => (if x<2680 then (if x<1590 then (if x<192 then (if x<136 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1738 then (if x<1690 then 0 else 0) else (if x<1748 then 1 else (if x<2614 then 1 else 2)))) else (if x<3130 then (if x<2716 then (if x<2714 then 2 else 2) else (if x<2762 then 3 else (if x<2770 then 0 else 1))) else (if x<3188 then (if x<3132 then 2 else 3) else (if x<3222 then 0 else (if x<3288 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6845 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2668,2680,2702,2714,2716,2758,2762,2770,3118,3130,3132,3174,3188,3192,3222,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6845 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6845 3192 5
  · have he : independentCachedBranchMembers6845.erase 3192=independentCachedBranchMembers6843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6843
  · have he : independentCachedBranchMembers6845.filter (independentCachedEdge 3192)=independentCachedBranchMembers6844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6844
def independentCachedBranchMembers6846 : Finset ℕ := ([48,130,1596,1644,1650,1678,1734,1752,2614,2680,2714,2716,2762,2770,3130,3132,3188,3222,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6846 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6846 5 (fun x => (if x<2680 then (if x<1650 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1734 then (if x<1678 then 1 else 0) else (if x<1752 then 1 else (if x<2614 then 1 else 2)))) else (if x<3130 then (if x<2716 then (if x<2714 then 0 else 2) else (if x<2762 then 3 else (if x<2770 then 0 else 1))) else (if x<3188 then (if x<3132 then 2 else 3) else (if x<3222 then 0 else (if x<3288 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6847 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2668,2680,2702,2714,2716,2758,2762,2770,2776,3118,3130,3132,3174,3188,3192,3222,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6847 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6847 2776 5
  · have he : independentCachedBranchMembers6847.erase 2776=independentCachedBranchMembers6845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6845
  · have he : independentCachedBranchMembers6847.filter (independentCachedEdge 2776)=independentCachedBranchMembers6846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6846
end EntropyDesigns.QuadraticRefinement
