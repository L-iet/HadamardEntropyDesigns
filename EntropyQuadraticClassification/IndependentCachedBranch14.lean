/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch13
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers1792 : Finset ℕ := ([72,132,252,1594,1644,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2732,2758,2772,2792,3132,3158,3178,3192,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1792 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1792 72 4
  · have he : independentCachedBranchMembers1792.erase 72=independentCachedBranchMembers1790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1790
  · have he : independentCachedBranchMembers1792.filter (independentCachedEdge 72)=independentCachedBranchMembers1791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1791
def independentCachedBranchMembers1793 : Finset ℕ := ([1644,1692,1752,1764,2652,2732,2772,2792,3158,3178,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound1793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1793 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1793 4 (fun x => (if x<2772 then (if x<1764 then (if x<1692 then 0 else (if x<1752 then 0 else 1)) else (if x<2652 then 1 else (if x<2732 then 0 else 0))) else (if x<3178 then (if x<2792 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1794 : Finset ℕ := ([48,72,132,252,1594,1644,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2732,2758,2772,2792,3132,3158,3178,3192,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1794 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1794 48 4
  · have he : independentCachedBranchMembers1794.erase 48=independentCachedBranchMembers1792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1792
  · have he : independentCachedBranchMembers1794.filter (independentCachedEdge 48)=independentCachedBranchMembers1793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1793
def independentCachedBranchMembers1795 : Finset ℕ := ([48,72,132,252,1594,1644,1678,1752,2614,2638,2732,2772,3132,3178,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1795 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1795 4 (fun x => (if x<2614 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1644 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3132 then (if x<2732 then (if x<2638 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3238 then (if x<3178 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1796 : Finset ℕ := ([48,72,132,252,1594,1644,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2732,2758,2772,2792,3132,3158,3178,3192,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1796 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1796 3298 4
  · have he : independentCachedBranchMembers1796.erase 3298=independentCachedBranchMembers1794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1794
  · have he : independentCachedBranchMembers1796.filter (independentCachedEdge 3298)=independentCachedBranchMembers1795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1795
def independentCachedBranchMembers1797 : Finset ℕ := ([48,72,132,252,1692,1714,1738,1764,2652,2674,2758,2792,3132,3178,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1797 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1797 4 (fun x => (if x<2652 then (if x<1692 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3132 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3238 then (if x<3178 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1798 : Finset ℕ := ([48,72,132,252,1594,1644,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2732,2758,2772,2792,3118,3132,3158,3178,3192,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1798 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1798 3118 4
  · have he : independentCachedBranchMembers1798.erase 3118=independentCachedBranchMembers1796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1796
  · have he : independentCachedBranchMembers1798.filter (independentCachedEdge 3118)=independentCachedBranchMembers1797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1797
def independentCachedBranchMembers1799 : Finset ℕ := ([72,132,1644,1678,1692,1714,2638,2652,2674,2732,3158,3178,3192,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1799 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1799 4 (fun x => (if x<2674 then (if x<1692 then (if x<1644 then (if x<132 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1714 then 2 else 2) else (if x<2652 then 1 else 2))) else (if x<3192 then (if x<3158 then (if x<2732 then 2 else 1) else (if x<3178 then 3 else 0)) else (if x<3238 then (if x<3226 then 3 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1800 : Finset ℕ := ([48,72,132,192,252,1594,1644,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2732,2758,2772,2792,3118,3132,3158,3178,3192,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1800 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1800 192 4
  · have he : independentCachedBranchMembers1800.erase 192=independentCachedBranchMembers1798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1798
  · have he : independentCachedBranchMembers1800.filter (independentCachedEdge 192)=independentCachedBranchMembers1799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1799
def independentCachedBranchMembers1801 : Finset ℕ := ([72,132,1594,1738,1752,1764,2614,2758,2772,2792,3158,3178,3192,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1801 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1801 4 (fun x => (if x<2772 then (if x<1752 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1738 then 1 else 1)) else (if x<2614 then (if x<1764 then 2 else 2) else (if x<2758 then 1 else 1))) else (if x<3192 then (if x<3158 then (if x<2792 then 2 else 2) else (if x<3178 then 3 else 0)) else (if x<3238 then (if x<3226 then 3 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1802 : Finset ℕ := ([12,48,72,132,192,252,1594,1644,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2732,2758,2772,2792,3118,3132,3158,3178,3192,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1802 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1802 12 4
  · have he : independentCachedBranchMembers1802.erase 12=independentCachedBranchMembers1800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1800
  · have he : independentCachedBranchMembers1802.filter (independentCachedEdge 12)=independentCachedBranchMembers1801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1801
def independentCachedBranchMembers1803 : Finset ℕ := ([12,48,72,132,192,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2646,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800,3118,3126,3132,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1803 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1803 2646 5
  · have he : independentCachedBranchMembers1803.erase 2646=independentCachedBranchMembers1789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1789
  · have he : independentCachedBranchMembers1803.filter (independentCachedEdge 2646)=independentCachedBranchMembers1802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1802
def independentCachedBranchMembers1804 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1804 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1804 1690 6
  · have he : independentCachedBranchMembers1804.erase 1690=independentCachedBranchMembers1696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1696
  · have he : independentCachedBranchMembers1804.filter (independentCachedEdge 1690)=independentCachedBranchMembers1803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1803
def independentCachedBranchMembers1805 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2680,2740,2764,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1805 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1805 6 (fun x => (if x<2740 then (if x<1650 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1626 then (if x<1614 then 1 else 1) else (if x<1628 then 2 else 3))) else (if x<1720 then (if x<1686 then (if x<1652 then 3 else 2) else (if x<1708 then 2 else 1)) else (if x<1748 then (if x<1734 then 2 else 3) else (if x<1768 then 1 else (if x<2680 then 3 else 0))))) else (if x<3228 then (if x<3178 then (if x<3132 then (if x<2764 then 0 else 0) else (if x<3158 then 4 else 1)) else (if x<3192 then (if x<3180 then 4 else 5) else (if x<3214 then 2 else 4))) else (if x<3274 then (if x<3250 then (if x<3238 then 5 else 5) else (if x<3252 then 4 else 1)) else (if x<3288 then (if x<3276 then 5 else 1) else (if x<3300 then 4 else (if x<3312 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1806 : Finset ℕ := ([72,252,1614,1628,1652,1686,1708,1768,2740,3132,3178,3192,3250,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1806 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1806 5 (fun x => (if x<1768 then (if x<1628 then (if x<252 then 0 else (if x<1614 then 0 else 1)) else (if x<1686 then (if x<1652 then 0 else 1) else (if x<1708 then 1 else 1))) else (if x<3192 then (if x<3132 then (if x<2740 then 0 else 1) else (if x<3178 then 2 else 2)) else (if x<3276 then (if x<3250 then 0 else 2) else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1807 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2680,2740,2764,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1807 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1807 3130 5
  · have he : independentCachedBranchMembers1807.erase 3130=independentCachedBranchMembers1805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1805
  · have he : independentCachedBranchMembers1807.filter (independentCachedEdge 3130)=independentCachedBranchMembers1806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1806
def independentCachedBranchMembers1808 : Finset ℕ := ([48,72,1590,1614,1628,1650,1686,1720,2740,2764,3132,3158,3178,3192,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1808 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1808 5 (fun x => (if x<3132 then (if x<1650 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else (if x<1628 then 0 else 1))) else (if x<1720 then (if x<1686 then 1 else 1) else (if x<2740 then 1 else (if x<2764 then 0 else 0)))) else (if x<3228 then (if x<3178 then (if x<3158 then 2 else 1) else (if x<3192 then 2 else (if x<3214 then 1 else 2))) else (if x<3274 then (if x<3250 then 1 else 0) else (if x<3288 then 0 else (if x<3300 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1809 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2680,2740,2764,2788,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1809 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1809 2788 5
  · have he : independentCachedBranchMembers1809.erase 2788=independentCachedBranchMembers1807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1807
  · have he : independentCachedBranchMembers1809.filter (independentCachedEdge 2788)=independentCachedBranchMembers1808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1808
def independentCachedBranchMembers1810 : Finset ℕ := ([132,252,1628,1650,1686,1708,1720,1748,2740,2764,3130,3158,3180,3192,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1810 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1810 5 (fun x => (if x<3130 then (if x<1708 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1650 then 1 else (if x<1686 then 1 else 1))) else (if x<1748 then (if x<1720 then 0 else 1) else (if x<2740 then 0 else (if x<2764 then 0 else 0)))) else (if x<3238 then (if x<3180 then (if x<3158 then 2 else 1) else (if x<3192 then 2 else (if x<3228 then 1 else 0))) else (if x<3274 then (if x<3250 then 2 else 1) else (if x<3300 then 2 else (if x<3312 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1811 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2680,2740,2762,2764,2788,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1811 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1811 2762 5
  · have he : independentCachedBranchMembers1811.erase 2762=independentCachedBranchMembers1809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1809
  · have he : independentCachedBranchMembers1811.filter (independentCachedEdge 2762)=independentCachedBranchMembers1810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1810
def independentCachedBranchMembers1812 : Finset ℕ := ([132,252,1626,1652,1708,1734,1748,1768,2740,2764,3132,3158,3178,3192,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1812 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1812 5 (fun x => (if x<3132 then (if x<1734 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1708 then 1 else 0))) else (if x<1768 then (if x<1748 then 1 else 0) else (if x<2740 then 1 else (if x<2764 then 0 else 0)))) else (if x<3228 then (if x<3178 then (if x<3158 then 2 else 1) else (if x<3192 then 2 else (if x<3214 then 1 else 2))) else (if x<3274 then (if x<3250 then 0 else 2) else (if x<3288 then 1 else (if x<3300 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1813 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2680,2738,2740,2762,2764,2788,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1813 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1813 2738 5
  · have he : independentCachedBranchMembers1813.erase 2738=independentCachedBranchMembers1811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1811
  · have he : independentCachedBranchMembers1813.filter (independentCachedEdge 2738)=independentCachedBranchMembers1812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1812
def independentCachedBranchMembers1814 : Finset ℕ := ([48,72,1590,1614,1626,1652,1734,1768,2740,2764,3130,3158,3180,3192,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1814 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1814 5 (fun x => (if x<3130 then (if x<1652 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else (if x<1626 then 0 else 1))) else (if x<1768 then (if x<1734 then 1 else 1) else (if x<2740 then 1 else (if x<2764 then 0 else 0)))) else (if x<3238 then (if x<3180 then (if x<3158 then 2 else 1) else (if x<3192 then 2 else (if x<3228 then 1 else 2))) else (if x<3274 then (if x<3250 then 2 else 0) else (if x<3300 then 0 else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1815 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2680,2716,2738,2740,2762,2764,2788,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1815 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1815 2716 5
  · have he : independentCachedBranchMembers1815.erase 2716=independentCachedBranchMembers1813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1813
  · have he : independentCachedBranchMembers1815.filter (independentCachedEdge 2716)=independentCachedBranchMembers1814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1814
def independentCachedBranchMembers1816 : Finset ℕ := ([48,72,132,252,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1816 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1816 5 (fun x => (if x<3214 then (if x<3132 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else (if x<3130 then 0 else 1))) else (if x<3178 then (if x<3158 then 2 else 1) else (if x<3180 then 2 else (if x<3192 then 1 else 0)))) else (if x<3274 then (if x<3238 then (if x<3228 then 1 else 3) else (if x<3250 then 2 else (if x<3252 then 3 else 0))) else (if x<3288 then (if x<3276 then 3 else 0) else (if x<3300 then 1 else (if x<3312 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1817 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2646,2680,2716,2738,2740,2762,2764,2788,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1817 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1817 2646 5
  · have he : independentCachedBranchMembers1817.erase 2646=independentCachedBranchMembers1815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1815
  · have he : independentCachedBranchMembers1817.filter (independentCachedEdge 2646)=independentCachedBranchMembers1816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1816
def independentCachedBranchMembers1818 : Finset ℕ := ([48,132,1614,1650,1652,1686,1708,1734,2680,2716,2762,2764,3130,3132,3158,3178,3180,3214,3250,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1818 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1818 5 (fun x => (if x<2764 then (if x<1686 then (if x<1614 then (if x<132 then 0 else 0) else (if x<1650 then 1 else (if x<1652 then 0 else 1))) else (if x<2680 then (if x<1708 then 1 else (if x<1734 then 1 else 0)) else (if x<2716 then 0 else (if x<2762 then 2 else 2)))) else (if x<3180 then (if x<3132 then (if x<3130 then 0 else 0) else (if x<3158 then 2 else (if x<3178 then 1 else 2))) else (if x<3252 then (if x<3214 then 1 else (if x<3250 then 0 else 3)) else (if x<3288 then 1 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1819 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2646,2680,2716,2738,2740,2762,2764,2776,2788,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1819 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1819 2776 5
  · have he : independentCachedBranchMembers1819.erase 2776=independentCachedBranchMembers1817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1817
  · have he : independentCachedBranchMembers1819.filter (independentCachedEdge 2776)=independentCachedBranchMembers1818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1818
def independentCachedBranchMembers1820 : Finset ℕ := ([72,252,1590,1626,1628,1720,1748,1768,2680,2716,2762,2764,3130,3132,3158,3178,3180,3214,3250,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1820 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1820 5 (fun x => (if x<2764 then (if x<1720 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1626 then 1 else (if x<1628 then 1 else 0))) else (if x<2680 then (if x<1748 then 1 else (if x<1768 then 1 else 0)) else (if x<2716 then 0 else (if x<2762 then 2 else 2)))) else (if x<3180 then (if x<3132 then (if x<3130 then 0 else 1) else (if x<3158 then 2 else (if x<3178 then 1 else 2))) else (if x<3252 then (if x<3214 then 0 else (if x<3250 then 2 else 3)) else (if x<3288 then 1 else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1821 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2646,2680,2702,2716,2738,2740,2762,2764,2776,2788,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1821 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1821 2702 5
  · have he : independentCachedBranchMembers1821.erase 2702=independentCachedBranchMembers1819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1819
  · have he : independentCachedBranchMembers1821.filter (independentCachedEdge 2702)=independentCachedBranchMembers1820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1820
def independentCachedBranchMembers1822 : Finset ℕ := ([48,132,1590,1626,1650,1720,1734,1748,2680,2738,2764,2788,3130,3158,3180,3214,3228,3238,3252,3274,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1822 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1822 5 (fun x => (if x<2788 then (if x<1720 then (if x<1590 then (if x<132 then 0 else 0) else (if x<1626 then 1 else (if x<1650 then 1 else 0))) else (if x<2680 then (if x<1734 then 1 else (if x<1748 then 0 else 1)) else (if x<2738 then 0 else (if x<2764 then 2 else 0)))) else (if x<3228 then (if x<3158 then (if x<3130 then 2 else 0) else (if x<3180 then 1 else (if x<3214 then 2 else 0))) else (if x<3274 then (if x<3238 then 3 else (if x<3252 then 2 else 1)) else (if x<3288 then 3 else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1823 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2788,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1823 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1823 2668 5
  · have he : independentCachedBranchMembers1823.erase 2668=independentCachedBranchMembers1821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1821
  · have he : independentCachedBranchMembers1823.filter (independentCachedEdge 2668)=independentCachedBranchMembers1822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1822
def independentCachedBranchMembers1824 : Finset ℕ := ([72,252,1614,1628,1652,1686,1708,1768,2680,2738,2764,2788,3130,3158,3180,3214,3228,3238,3252,3274,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1824 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1824 5 (fun x => (if x<2788 then (if x<1686 then (if x<1614 then (if x<252 then 0 else 0) else (if x<1628 then 1 else (if x<1652 then 0 else 1))) else (if x<2680 then (if x<1708 then 1 else (if x<1768 then 1 else 0)) else (if x<2738 then 0 else (if x<2764 then 2 else 0)))) else (if x<3228 then (if x<3158 then (if x<3130 then 2 else 2) else (if x<3180 then 1 else (if x<3214 then 0 else 1))) else (if x<3274 then (if x<3238 then 3 else (if x<3252 then 2 else 1)) else (if x<3288 then 3 else (if x<3312 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1825 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2618,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2788,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1825 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1825 2618 5
  · have he : independentCachedBranchMembers1825.erase 2618=independentCachedBranchMembers1823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1823
  · have he : independentCachedBranchMembers1825.filter (independentCachedEdge 2618)=independentCachedBranchMembers1824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1824
def independentCachedBranchMembers1826 : Finset ℕ := ([72,132,1590,1626,1628,1686,1708,1734,2680,2702,2738,2740,2776,2788,3130,3132,3158,3178,3180,3228,3238,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1826 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1826 5 (fun x => (if x<2776 then (if x<1708 then (if x<1626 then (if x<132 then 0 else (if x<1590 then 0 else 1)) else (if x<1628 then 0 else (if x<1686 then 1 else 0))) else (if x<2702 then (if x<1734 then 1 else (if x<2680 then 1 else 0)) else (if x<2738 then 2 else (if x<2740 then 2 else 0)))) else (if x<3180 then (if x<3132 then (if x<2788 then 2 else (if x<3130 then 2 else 3)) else (if x<3158 then 1 else (if x<3178 then 1 else 0))) else (if x<3274 then (if x<3228 then 3 else (if x<3238 then 3 else 0)) else (if x<3276 then 3 else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1827 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2618,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2788,2800,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1827 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1827 2800 5
  · have he : independentCachedBranchMembers1827.erase 2800=independentCachedBranchMembers1825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1825
  · have he : independentCachedBranchMembers1827.filter (independentCachedEdge 2800)=independentCachedBranchMembers1826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1826
def independentCachedBranchMembers1828 : Finset ℕ := ([72,132,1614,1626,1650,1686,1748,1768,2618,2668,2680,2716,2740,2762,3132,3158,3178,3214,3238,3250,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1828 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1828 5 (fun x => (if x<2740 then (if x<1748 then (if x<1626 then (if x<132 then 0 else (if x<1614 then 0 else 1)) else (if x<1650 then 0 else (if x<1686 then 1 else 0))) else (if x<2668 then (if x<1768 then 1 else (if x<2618 then 1 else 2)) else (if x<2680 then 2 else (if x<2716 then 0 else 2)))) else (if x<3238 then (if x<3158 then (if x<2762 then 0 else (if x<3132 then 2 else 2)) else (if x<3178 then 1 else (if x<3214 then 0 else 3))) else (if x<3288 then (if x<3250 then 0 else (if x<3276 then 3 else 1)) else (if x<3300 then 3 else (if x<3312 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1829 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2788,2800,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1829 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1829 2620 5
  · have he : independentCachedBranchMembers1829.erase 2620=independentCachedBranchMembers1827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1827
  · have he : independentCachedBranchMembers1829.filter (independentCachedEdge 2620)=independentCachedBranchMembers1828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1828
def independentCachedBranchMembers1830 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1652,1686,1708,1720,1748,2620,2716,2738,2762,2788,2800,3130,3158,3180,3192,3214,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1830 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1830 5 (fun x => (if x<2716 then (if x<1626 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1590 then 0 else (if x<1614 then 1 else 1))) else (if x<1708 then (if x<1652 then 2 else (if x<1686 then 2 else 2)) else (if x<1748 then (if x<1720 then 1 else 2) else (if x<2620 then 1 else 3)))) else (if x<3158 then (if x<2788 then (if x<2738 then 4 else (if x<2762 then 3 else 4)) else (if x<2800 then 3 else (if x<3130 then 4 else 3))) else (if x<3214 then (if x<3180 then 1 else (if x<3192 then 3 else 0)) else (if x<3276 then (if x<3252 then 4 else 0) else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1831 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1831 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1831 2786 5
  · have he : independentCachedBranchMembers1831.erase 2786=independentCachedBranchMembers1829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1829
  · have he : independentCachedBranchMembers1831.filter (independentCachedEdge 2786)=independentCachedBranchMembers1830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1830
def independentCachedBranchMembers1832 : Finset ℕ := ([48,72,132,252,1626,1628,1650,1652,1686,1720,1734,1768,2618,2668,2702,2776,3158,3192,3228,3250,3252,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1832 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1832 5 (fun x => (if x<2618 then (if x<1650 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1626 then 0 else (if x<1628 then 1 else 2))) else (if x<1720 then (if x<1652 then 2 else (if x<1686 then 1 else 1)) else (if x<1734 then 1 else (if x<1768 then 2 else 2)))) else (if x<3228 then (if x<2776 then (if x<2668 then 3 else (if x<2702 then 3 else 3)) else (if x<3158 then 3 else (if x<3192 then 1 else 0))) else (if x<3274 then (if x<3250 then 4 else (if x<3252 then 4 else 0)) else (if x<3276 then 4 else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1833 : Finset ℕ := ([72,132,1626,1628,1686,1734,2702,2776,3158,3228,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound1833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1833 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1833 4 (fun x => (if x<2702 then (if x<1628 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1686 then 1 else (if x<1734 then 0 else 1))) else (if x<3228 then (if x<2776 then 2 else (if x<3158 then 2 else 1)) else (if x<3274 then 2 else (if x<3276 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1834 : Finset ℕ := ([48,72,132,252,1626,1628,1650,1652,1686,1720,1734,1768,2618,2668,2702,2776,2800,3158,3192,3228,3250,3252,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1834 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1834 2800 4
  · have he : independentCachedBranchMembers1834.erase 2800=independentCachedBranchMembers1832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1832
  · have he : independentCachedBranchMembers1834.filter (independentCachedEdge 2800)=independentCachedBranchMembers1833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1833
def independentCachedBranchMembers1835 : Finset ℕ := ([72,132,1626,1650,1686,1768,2618,2668,3158,3250,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1835 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1835 4 (fun x => (if x<2618 then (if x<1650 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1686 then 1 else (if x<1768 then 0 else 1))) else (if x<3250 then (if x<2668 then 2 else (if x<3158 then 2 else 1)) else (if x<3276 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1836 : Finset ℕ := ([48,72,132,252,1626,1628,1650,1652,1686,1720,1734,1768,2618,2620,2668,2702,2776,2800,3158,3192,3228,3250,3252,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1836 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1836 2620 4
  · have he : independentCachedBranchMembers1836.erase 2620=independentCachedBranchMembers1834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1834
  · have he : independentCachedBranchMembers1836.filter (independentCachedEdge 2620)=independentCachedBranchMembers1835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1835
def independentCachedBranchMembers1837 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1837 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1837 2606 5
  · have he : independentCachedBranchMembers1837.erase 2606=independentCachedBranchMembers1831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1831
  · have he : independentCachedBranchMembers1837.filter (independentCachedEdge 2606)=independentCachedBranchMembers1836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1836
def independentCachedBranchMembers1838 : Finset ℕ := ([48,132,252,1626,1650,1686,1708,1734,1748,2680,2716,2740,2764,2788,3130,3178,3192,3214,3228,3238,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1838 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1838 5 (fun x => (if x<2740 then (if x<1686 then (if x<252 then (if x<132 then 0 else 0) else (if x<1626 then 0 else (if x<1650 then 1 else 2))) else (if x<1748 then (if x<1708 then 1 else (if x<1734 then 3 else 2)) else (if x<2680 then 3 else (if x<2716 then 0 else 3)))) else (if x<3214 then (if x<3130 then (if x<2764 then 0 else (if x<2788 then 0 else 3)) else (if x<3178 then 2 else (if x<3192 then 1 else 4))) else (if x<3252 then (if x<3228 then 2 else (if x<3238 then 4 else 1)) else (if x<3276 then 3 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1839 : Finset ℕ := ([252,1626,1748,2680,2716,2764,3130,3178,3214,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1839 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1839 4 (fun x => (if x<2764 then (if x<1748 then (if x<1626 then 0 else 1) else (if x<2680 then 0 else (if x<2716 then 1 else 0))) else (if x<3214 then (if x<3130 then 2 else (if x<3178 then 1 else 3)) else (if x<3252 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1840 : Finset ℕ := ([48,132,252,1626,1650,1686,1708,1734,1748,2680,2702,2716,2740,2764,2788,3130,3178,3192,3214,3228,3238,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1840 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1840 2702 4
  · have he : independentCachedBranchMembers1840.erase 2702=independentCachedBranchMembers1838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1838
  · have he : independentCachedBranchMembers1840.filter (independentCachedEdge 2702)=independentCachedBranchMembers1839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1839
def independentCachedBranchMembers1841 : Finset ℕ := ([252,1686,1708,2680,2764,2788,3130,3214,3228,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1841 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1841 4 (fun x => (if x<2788 then (if x<1708 then (if x<1686 then 0 else 1) else (if x<2680 then 0 else (if x<2764 then 1 else 0))) else (if x<3228 then (if x<3130 then 2 else (if x<3214 then 2 else 1)) else (if x<3238 then 0 else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1842 : Finset ℕ := ([48,132,252,1626,1650,1686,1708,1734,1748,2618,2680,2702,2716,2740,2764,2788,3130,3178,3192,3214,3228,3238,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1842 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1842 2618 4
  · have he : independentCachedBranchMembers1842.erase 2618=independentCachedBranchMembers1840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1840
  · have he : independentCachedBranchMembers1842.filter (independentCachedEdge 2618)=independentCachedBranchMembers1841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1841
def independentCachedBranchMembers1843 : Finset ℕ := ([1650,1708,1734,1748,2618,2702,2716,2788,3130,3214,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1843 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1843 4 (fun x => (if x<2716 then (if x<1748 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<2618 then 1 else (if x<2702 then 0 else 0))) else (if x<3214 then (if x<2788 then 1 else (if x<3130 then 1 else 2)) else (if x<3228 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1844 : Finset ℕ := ([48,72,132,252,1626,1650,1686,1708,1734,1748,2618,2680,2702,2716,2740,2764,2788,3130,3178,3192,3214,3228,3238,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1844 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1844 72 4
  · have he : independentCachedBranchMembers1844.erase 72=independentCachedBranchMembers1842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1842
  · have he : independentCachedBranchMembers1844.filter (independentCachedEdge 72)=independentCachedBranchMembers1843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1843
def independentCachedBranchMembers1845 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1845 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1845 1746 5
  · have he : independentCachedBranchMembers1845.erase 1746=independentCachedBranchMembers1837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1837
  · have he : independentCachedBranchMembers1845.filter (independentCachedEdge 1746)=independentCachedBranchMembers1844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1844
def independentCachedBranchMembers1846 : Finset ℕ := ([72,132,1614,1628,1650,1686,1708,1720,2680,2716,2738,2740,3158,3178,3180,3192,3214,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1846 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1846 5 (fun x => (if x<2738 then (if x<1686 then (if x<1614 then (if x<132 then 0 else 0) else (if x<1628 then 1 else (if x<1650 then 2 else 1))) else (if x<1720 then (if x<1708 then 0 else 2) else (if x<2680 then 3 else (if x<2716 then 0 else 2)))) else (if x<3192 then (if x<3158 then (if x<2740 then 1 else 0) else (if x<3178 then 3 else (if x<3180 then 0 else 4))) else (if x<3238 then (if x<3214 then 3 else (if x<3228 then 4 else 3)) else (if x<3250 then 0 else (if x<3252 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1847 : Finset ℕ := ([72,132,1628,1650,2716,2738,3178,3228,3238,3250] : List ℕ).toFinset
theorem independentCachedBranchBound1847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1847 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1847 4 (fun x => (if x<2738 then (if x<1628 then (if x<132 then 0 else 0) else (if x<1650 then 1 else (if x<2716 then 1 else 1))) else (if x<3228 then (if x<3178 then 1 else 0) else (if x<3238 then 2 else (if x<3250 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1848 : Finset ℕ := ([72,132,1614,1628,1650,1652,1686,1708,1720,2680,2716,2738,2740,3158,3178,3180,3192,3214,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1848 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1848 1652 4
  · have he : independentCachedBranchMembers1848.erase 1652=independentCachedBranchMembers1846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1846
  · have he : independentCachedBranchMembers1848.filter (independentCachedEdge 1652)=independentCachedBranchMembers1847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1847
def independentCachedBranchMembers1849 : Finset ℕ := ([72,1628,1720,2680,2716,3158,3178,3180,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1849 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1849 4 (fun x => (if x<3158 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<2680 then 1 else (if x<2716 then 0 else 1))) else (if x<3214 then (if x<3178 then 2 else (if x<3180 then 2 else 0)) else (if x<3250 then 2 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1850 : Finset ℕ := ([72,132,1614,1628,1650,1652,1686,1708,1720,2680,2702,2716,2738,2740,3158,3178,3180,3192,3214,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1850 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1850 2702 4
  · have he : independentCachedBranchMembers1850.erase 2702=independentCachedBranchMembers1848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1848
  · have he : independentCachedBranchMembers1850.filter (independentCachedEdge 2702)=independentCachedBranchMembers1849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1849
def independentCachedBranchMembers1851 : Finset ℕ := ([132,1650,1720,2680,2738,3158,3180,3214,3228,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1851 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1851 4 (fun x => (if x<3158 then (if x<1720 then (if x<1650 then 0 else 0) else (if x<2680 then 1 else (if x<2738 then 0 else 1))) else (if x<3228 then (if x<3180 then 2 else (if x<3214 then 2 else 0)) else (if x<3238 then 2 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1852 : Finset ℕ := ([72,132,1614,1628,1650,1652,1686,1708,1720,2668,2680,2702,2716,2738,2740,3158,3178,3180,3192,3214,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1852 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1852 2668 4
  · have he : independentCachedBranchMembers1852.erase 2668=independentCachedBranchMembers1850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1850
  · have he : independentCachedBranchMembers1852.filter (independentCachedEdge 2668)=independentCachedBranchMembers1851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1851
def independentCachedBranchMembers1853 : Finset ℕ := ([72,132,3158,3178,3180,3192,3214,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1853 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1853 4 (fun x => (if x<3192 then (if x<3158 then (if x<132 then 0 else 0) else (if x<3178 then 1 else (if x<3180 then 0 else 1))) else (if x<3238 then (if x<3214 then 2 else (if x<3228 then 1 else 2)) else (if x<3250 then 0 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1854 : Finset ℕ := ([72,132,1614,1628,1650,1652,1686,1708,1720,2646,2668,2680,2702,2716,2738,2740,3158,3178,3180,3192,3214,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1854 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1854 2646 4
  · have he : independentCachedBranchMembers1854.erase 2646=independentCachedBranchMembers1852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1852
  · have he : independentCachedBranchMembers1854.filter (independentCachedEdge 2646)=independentCachedBranchMembers1853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1853
def independentCachedBranchMembers1855 : Finset ℕ := ([1614,1628,1650,1708,2668,2702,2716,2738,3180,3214,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound1855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1855 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1855 4 (fun x => (if x<2716 then (if x<1708 then (if x<1628 then 0 else (if x<1650 then 1 else 0)) else (if x<2668 then 1 else (if x<2702 then 1 else 0))) else (if x<3214 then (if x<2738 then 1 else (if x<3180 then 0 else 2)) else (if x<3228 then 2 else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1856 : Finset ℕ := ([72,132,1614,1626,1628,1650,1652,1686,1708,1720,2646,2668,2680,2702,2716,2738,2740,3158,3178,3180,3192,3214,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1856 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1856 1626 4
  · have he : independentCachedBranchMembers1856.erase 1626=independentCachedBranchMembers1854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1854
  · have he : independentCachedBranchMembers1856.filter (independentCachedEdge 1626)=independentCachedBranchMembers1855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1855
def independentCachedBranchMembers1857 : Finset ℕ := ([48,72,132,192,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1857 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1857 192 5
  · have he : independentCachedBranchMembers1857.erase 192=independentCachedBranchMembers1845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1845
  · have he : independentCachedBranchMembers1857.filter (independentCachedEdge 192)=independentCachedBranchMembers1856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1856
def independentCachedBranchMembers1858 : Finset ℕ := ([72,132,1590,1626,1652,1686,1720,1734,1748,1768,2618,2646,2680,2740,2762,2776,2788,3130,3158,3178,3192,3238,3252,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1858 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1858 5 (fun x => (if x<2740 then (if x<1720 then (if x<1626 then (if x<132 then 0 else (if x<1590 then 0 else 1)) else (if x<1652 then 0 else (if x<1686 then 2 else 0))) else (if x<1768 then (if x<1734 then 1 else (if x<1748 then 2 else 1)) else (if x<2646 then (if x<2618 then 2 else 1) else (if x<2680 then 1 else 0)))) else (if x<3178 then (if x<2788 then (if x<2762 then 0 else (if x<2776 then 2 else 1)) else (if x<3130 then 2 else (if x<3158 then 3 else 3))) else (if x<3252 then (if x<3192 then 0 else (if x<3238 then 4 else 0)) else (if x<3288 then (if x<3274 then 3 else 4) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1859 : Finset ℕ := ([12,48,72,132,192,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1859 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1859 12 5
  · have he : independentCachedBranchMembers1859.erase 12=independentCachedBranchMembers1857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1857
  · have he : independentCachedBranchMembers1859.filter (independentCachedEdge 12)=independentCachedBranchMembers1858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1858
def independentCachedBranchMembers1860 : Finset ℕ := ([1590,1614,1626,1652,1686,1708,1720,1748,2618,2646,2668,2680,2702,2740,2764,2776,2786,3132,3178,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1860 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1860 5 (fun x => (if x<2702 then (if x<1720 then (if x<1652 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 1 else 0))) else (if x<2646 then (if x<1748 then 1 else (if x<2618 then 0 else 2)) else (if x<2668 then 0 else (if x<2680 then 2 else 1)))) else (if x<3178 then (if x<2776 then (if x<2740 then 2 else (if x<2764 then 0 else 0)) else (if x<2786 then 2 else (if x<3132 then 2 else 3))) else (if x<3250 then (if x<3228 then 3 else (if x<3238 then 4 else 3)) else (if x<3300 then (if x<3274 then 4 else 4) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1861 : Finset ℕ := ([1590,1614,1626,1686,2618,2646,2702,2786,3178,3238,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1861 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1861 4 (fun x => (if x<2702 then (if x<1686 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<2618 then 1 else (if x<2646 then 2 else 0))) else (if x<3238 then (if x<2786 then 2 else (if x<3178 then 2 else 1)) else (if x<3250 then 1 else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1862 : Finset ℕ := ([252,1590,1614,1626,1652,1686,1708,1720,1748,2618,2646,2668,2680,2702,2740,2764,2776,2786,3132,3178,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1862 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1862 252 4
  · have he : independentCachedBranchMembers1862.erase 252=independentCachedBranchMembers1860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1860
  · have he : independentCachedBranchMembers1862.filter (independentCachedEdge 252)=independentCachedBranchMembers1861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1861
def independentCachedBranchMembers1863 : Finset ℕ := ([1590,1614,1652,1720,2646,2668,2776,2786,3132,3250,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1863 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1863 4 (fun x => (if x<2776 then (if x<1720 then (if x<1614 then 0 else (if x<1652 then 0 else 1)) else (if x<2646 then 1 else (if x<2668 then 0 else 2))) else (if x<3250 then (if x<2786 then 2 else (if x<3132 then 2 else 1)) else (if x<3274 then 3 else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1864 : Finset ℕ := ([132,252,1590,1614,1626,1652,1686,1708,1720,1748,2618,2646,2668,2680,2702,2740,2764,2776,2786,3132,3178,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1864 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1864 132 4
  · have he : independentCachedBranchMembers1864.erase 132=independentCachedBranchMembers1862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1862
  · have he : independentCachedBranchMembers1864.filter (independentCachedEdge 132)=independentCachedBranchMembers1863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1863
def independentCachedBranchMembers1865 : Finset ℕ := ([1652,1708,1720,1748,2618,2646,2702,2786,3132,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1865 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1865 4 (fun x => (if x<2702 then (if x<1748 then (if x<1708 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2646 then 1 else 0))) else (if x<3228 then (if x<2786 then 0 else (if x<3132 then 2 else 2)) else (if x<3300 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1866 : Finset ℕ := ([72,132,252,1590,1614,1626,1652,1686,1708,1720,1748,2618,2646,2668,2680,2702,2740,2764,2776,2786,3132,3178,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1866 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1866 72 4
  · have he : independentCachedBranchMembers1866.erase 72=independentCachedBranchMembers1864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1864
  · have he : independentCachedBranchMembers1866.filter (independentCachedEdge 72)=independentCachedBranchMembers1865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1865
def independentCachedBranchMembers1867 : Finset ℕ := ([1626,1686,1708,1748,2646,2668,2776,2786,3178,3228,3238,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1867 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1867 4 (fun x => (if x<2776 then (if x<1748 then (if x<1686 then 0 else (if x<1708 then 0 else 1)) else (if x<2646 then 1 else (if x<2668 then 0 else 2))) else (if x<3228 then (if x<2786 then 2 else (if x<3178 then 2 else 3)) else (if x<3238 then 1 else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1868 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1652,1686,1708,1720,1748,2618,2646,2668,2680,2702,2740,2764,2776,2786,3132,3178,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1868 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1868 48 4
  · have he : independentCachedBranchMembers1868.erase 48=independentCachedBranchMembers1866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1866
  · have he : independentCachedBranchMembers1868.filter (independentCachedEdge 48)=independentCachedBranchMembers1867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1867
def independentCachedBranchMembers1869 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1720,2618,2668,2702,2776,3228,3250,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1869 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1869 4 (fun x => (if x<2618 then (if x<1626 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1686 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3228 then (if x<2702 then (if x<2668 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3274 then (if x<3250 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1870 : Finset ℕ := ([48,72,132,252,1590,1614,1626,1652,1686,1708,1720,1748,2606,2618,2646,2668,2680,2702,2740,2764,2776,2786,3132,3178,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1870 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1870 2606 4
  · have he : independentCachedBranchMembers1870.erase 2606=independentCachedBranchMembers1868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1868
  · have he : independentCachedBranchMembers1870.filter (independentCachedEdge 2606)=independentCachedBranchMembers1869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1869
def independentCachedBranchMembers1871 : Finset ℕ := ([12,48,72,132,192,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1871 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1871 3298 5
  · have he : independentCachedBranchMembers1871.erase 3298=independentCachedBranchMembers1859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1859
  · have he : independentCachedBranchMembers1871.filter (independentCachedEdge 3298)=independentCachedBranchMembers1870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1870
def independentCachedBranchMembers1872 : Finset ℕ := ([12,48,192,252,1590,1614,1628,1650,1708,1734,1748,1768,2606,2620,2646,2680,2740,2764,2786,2800,3130,3180,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1872 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1872 5 (fun x => (if x<2646 then (if x<1650 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1614 then (if x<1590 then 0 else 1) else (if x<1628 then 1 else 2))) else (if x<1748 then (if x<1708 then 2 else (if x<1734 then 1 else 2)) else (if x<2606 then (if x<1768 then 1 else 2) else (if x<2620 then 1 else 0)))) else (if x<3180 then (if x<2764 then (if x<2680 then 1 else (if x<2740 then 2 else 1)) else (if x<2800 then (if x<2786 then 0 else 2) else (if x<3130 then 0 else 3))) else (if x<3250 then (if x<3214 then 3 else (if x<3228 then 3 else 4)) else (if x<3288 then (if x<3274 then 4 else 4) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1873 : Finset ℕ := ([12,192,1590,1614,1628,1768,2620,2786,2800,3180,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1873 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1873 4 (fun x => (if x<2620 then (if x<1614 then (if x<192 then 0 else (if x<1590 then 0 else 1)) else (if x<1628 then 1 else (if x<1768 then 2 else 2))) else (if x<3180 then (if x<2786 then 0 else (if x<2800 then 2 else 0)) else (if x<3274 then (if x<3250 then 3 else 1) else (if x<3288 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1874 : Finset ℕ := ([12,192,3180,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1874 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1874 3 (fun x => (if x<3250 then (if x<192 then 0 else (if x<3180 then 0 else 1)) else (if x<3274 then 2 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1875 : Finset ℕ := ([12,192,1590,1614,1628,1768,2620,2646,2786,2800,3180,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1875 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1875 2646 3
  · have he : independentCachedBranchMembers1875.erase 2646=independentCachedBranchMembers1873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1873
  · have he : independentCachedBranchMembers1875.filter (independentCachedEdge 2646)=independentCachedBranchMembers1874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1874
def independentCachedBranchMembers1876 : Finset ℕ := ([1628,1768,2620,2800,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1876 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1876 3 (fun x => (if x<2800 then (if x<1768 then 0 else (if x<2620 then 0 else 1)) else (if x<3250 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1877 : Finset ℕ := ([12,192,1590,1614,1628,1768,2606,2620,2646,2786,2800,3180,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1877 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1877 2606 3
  · have he : independentCachedBranchMembers1877.erase 2606=independentCachedBranchMembers1875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1875
  · have he : independentCachedBranchMembers1877.filter (independentCachedEdge 2606)=independentCachedBranchMembers1876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1876
def independentCachedBranchMembers1878 : Finset ℕ := ([12,48,132,192,252,1590,1614,1628,1650,1708,1734,1748,1768,2606,2620,2646,2680,2740,2764,2786,2800,3130,3180,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1878 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1878 132 4
  · have he : independentCachedBranchMembers1878.erase 132=independentCachedBranchMembers1872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1872
  · have he : independentCachedBranchMembers1878.filter (independentCachedEdge 132)=independentCachedBranchMembers1877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1877
def independentCachedBranchMembers1879 : Finset ℕ := ([12,192,1650,1708,1734,1748,2620,2646,2786,2800,3130,3214,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1879 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1879 4 (fun x => (if x<2646 then (if x<1708 then (if x<192 then 0 else (if x<1650 then 0 else 1)) else (if x<1748 then (if x<1734 then 2 else 1) else (if x<2620 then 2 else 0))) else (if x<3130 then (if x<2786 then 1 else (if x<2800 then 1 else 0)) else (if x<3228 then (if x<3214 then 3 else 3) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1880 : Finset ℕ := ([1650,1734,2620,2800,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1880 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1880 3 (fun x => (if x<2800 then (if x<1734 then 0 else (if x<2620 then 0 else 1)) else (if x<3228 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1881 : Finset ℕ := ([12,192,1650,1708,1734,1748,2606,2620,2646,2786,2800,3130,3214,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1881 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1881 2606 3
  · have he : independentCachedBranchMembers1881.erase 2606=independentCachedBranchMembers1879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1879
  · have he : independentCachedBranchMembers1881.filter (independentCachedEdge 2606)=independentCachedBranchMembers1880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1880
def independentCachedBranchMembers1882 : Finset ℕ := ([12,48,72,132,192,252,1590,1614,1628,1650,1708,1734,1748,1768,2606,2620,2646,2680,2740,2764,2786,2800,3130,3180,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1882 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1882 72 4
  · have he : independentCachedBranchMembers1882.erase 72=independentCachedBranchMembers1878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1878
  · have he : independentCachedBranchMembers1882.filter (independentCachedEdge 72)=independentCachedBranchMembers1881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1881
def independentCachedBranchMembers1883 : Finset ℕ := ([12,48,72,132,192,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800,3130,3132,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1883 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1883 3226 5
  · have he : independentCachedBranchMembers1883.erase 3226=independentCachedBranchMembers1871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1871
  · have he : independentCachedBranchMembers1883.filter (independentCachedEdge 3226)=independentCachedBranchMembers1882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1882
def independentCachedBranchMembers1884 : Finset ℕ := ([1626,1628,1650,1652,1686,1720,1734,1768,2606,2646,2680,2716,2738,2740,2762,2764,2788,3130,3132,3178,3180,3214,3238,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1884 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1884 5 (fun x => (if x<2738 then (if x<1734 then (if x<1652 then (if x<1628 then 0 else (if x<1650 then 1 else 1)) else (if x<1686 then 0 else (if x<1720 then 0 else 0))) else (if x<2646 then (if x<1768 then 1 else (if x<2606 then 1 else 2)) else (if x<2680 then 0 else (if x<2716 then 0 else 2)))) else (if x<3132 then (if x<2764 then (if x<2740 then 2 else (if x<2762 then 0 else 2)) else (if x<2788 then 1 else (if x<3130 then 2 else 3))) else (if x<3214 then (if x<3178 then 4 else (if x<3180 then 4 else 3)) else (if x<3288 then (if x<3238 then 3 else 4) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1885 : Finset ℕ := ([1626,1650,1686,1734,2606,2646,2738,2762,3130,3178,3214,3238] : List ℕ).toFinset
theorem independentCachedBranchBound1885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1885 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1885 4 (fun x => (if x<2738 then (if x<1734 then (if x<1650 then 0 else (if x<1686 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 2 else 0))) else (if x<3178 then (if x<2762 then 2 else (if x<3130 then 2 else 1)) else (if x<3214 then 3 else (if x<3238 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1886 : Finset ℕ := ([252,1626,1628,1650,1652,1686,1720,1734,1768,2606,2646,2680,2716,2738,2740,2762,2764,2788,3130,3132,3178,3180,3214,3238,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1886 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1886 252 4
  · have he : independentCachedBranchMembers1886.erase 252=independentCachedBranchMembers1884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1884
  · have he : independentCachedBranchMembers1886.filter (independentCachedEdge 252)=independentCachedBranchMembers1885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1885
def independentCachedBranchMembers1887 : Finset ℕ := ([1628,1652,1720,1768,2606,2646,2738,2762,3132,3180,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1887 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1887 4 (fun x => (if x<2738 then (if x<1768 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 2 else 0))) else (if x<3180 then (if x<2762 then 0 else (if x<3132 then 1 else 2)) else (if x<3288 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1888 : Finset ℕ := ([132,252,1626,1628,1650,1652,1686,1720,1734,1768,2606,2646,2680,2716,2738,2740,2762,2764,2788,3130,3132,3178,3180,3214,3238,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1888 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1888 132 4
  · have he : independentCachedBranchMembers1888.erase 132=independentCachedBranchMembers1886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1886
  · have he : independentCachedBranchMembers1888.filter (independentCachedEdge 132)=independentCachedBranchMembers1887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1887
def independentCachedBranchMembers1889 : Finset ℕ := ([1650,1652,1720,1734,2606,2646,2716,2788,3130,3132,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1889 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1889 4 (fun x => (if x<2716 then (if x<1734 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 2 else 0))) else (if x<3132 then (if x<2788 then 0 else (if x<3130 then 1 else 2)) else (if x<3214 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1890 : Finset ℕ := ([72,132,252,1626,1628,1650,1652,1686,1720,1734,1768,2606,2646,2680,2716,2738,2740,2762,2764,2788,3130,3132,3178,3180,3214,3238,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1890 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1890 72 4
  · have he : independentCachedBranchMembers1890.erase 72=independentCachedBranchMembers1888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1888
  · have he : independentCachedBranchMembers1890.filter (independentCachedEdge 72)=independentCachedBranchMembers1889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1889
def independentCachedBranchMembers1891 : Finset ℕ := ([1626,1628,1686,1768,2606,2646,2716,2788,3178,3180,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1891 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1891 4 (fun x => (if x<2716 then (if x<1768 then (if x<1628 then 0 else (if x<1686 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 2 else 0))) else (if x<3180 then (if x<2788 then 2 else (if x<3178 then 2 else 3)) else (if x<3238 then 1 else (if x<3288 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1892 : Finset ℕ := ([48,72,132,252,1626,1628,1650,1652,1686,1720,1734,1768,2606,2646,2680,2716,2738,2740,2762,2764,2788,3130,3132,3178,3180,3214,3238,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1892 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1892 48 4
  · have he : independentCachedBranchMembers1892.erase 48=independentCachedBranchMembers1890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1890
  · have he : independentCachedBranchMembers1892.filter (independentCachedEdge 48)=independentCachedBranchMembers1891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1891
def independentCachedBranchMembers1893 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1720,2716,2738,2762,2788,3130,3180,3214,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1893 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1893 4 (fun x => (if x<2716 then (if x<1626 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1686 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3130 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3214 then (if x<3180 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1894 : Finset ℕ := ([48,72,132,252,1626,1628,1650,1652,1686,1720,1734,1768,2606,2646,2680,2716,2738,2740,2762,2764,2786,2788,3130,3132,3178,3180,3214,3238,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1894 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1894 2786 4
  · have he : independentCachedBranchMembers1894.erase 2786=independentCachedBranchMembers1892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1892
  · have he : independentCachedBranchMembers1894.filter (independentCachedEdge 2786)=independentCachedBranchMembers1893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1893
def independentCachedBranchMembers1895 : Finset ℕ := ([12,48,72,132,192,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800,3118,3130,3132,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1895 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1895 3118 5
  · have he : independentCachedBranchMembers1895.erase 3118=independentCachedBranchMembers1883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1883
  · have he : independentCachedBranchMembers1895.filter (independentCachedEdge 3118)=independentCachedBranchMembers1894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1894
def independentCachedBranchMembers1896 : Finset ℕ := ([132,252,1590,1614,1628,1650,1708,1734,1748,1768,2618,2668,2702,2716,2738,2762,2776,2788,3132,3158,3178,3192,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1896 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1896 5 (fun x => (if x<2716 then (if x<1708 then (if x<1614 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1628 then 1 else (if x<1650 then 2 else 2))) else (if x<1768 then (if x<1734 then 0 else (if x<1748 then 2 else 0)) else (if x<2668 then (if x<2618 then 2 else 3) else (if x<2702 then 3 else 3)))) else (if x<3178 then (if x<2776 then (if x<2738 then 0 else (if x<2762 then 1 else 1)) else (if x<3132 then (if x<2788 then 3 else 0) else (if x<3158 then 4 else 2))) else (if x<3238 then (if x<3192 then 4 else (if x<3226 then 2 else 3)) else (if x<3276 then (if x<3252 then 4 else 0) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1897 : Finset ℕ := ([1650,1708,1734,1748,2618,2702,2716,2788,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1897 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1897 4 (fun x => (if x<2716 then (if x<1748 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<2618 then 1 else (if x<2702 then 0 else 0))) else (if x<3158 then (if x<2788 then 1 else (if x<3132 then 1 else 2)) else (if x<3226 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1898 : Finset ℕ := ([72,132,252,1590,1614,1628,1650,1708,1734,1748,1768,2618,2668,2702,2716,2738,2762,2776,2788,3132,3158,3178,3192,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1898 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1898 72 4
  · have he : independentCachedBranchMembers1898.erase 72=independentCachedBranchMembers1896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1896
  · have he : independentCachedBranchMembers1898.filter (independentCachedEdge 72)=independentCachedBranchMembers1897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1897
def independentCachedBranchMembers1899 : Finset ℕ := ([1628,1708,1748,1768,2668,2716,2776,2788,3158,3178,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound1899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1899 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1899 4 (fun x => (if x<2776 then (if x<1768 then (if x<1708 then 0 else (if x<1748 then 0 else 1)) else (if x<2668 then 1 else (if x<2716 then 0 else 0))) else (if x<3178 then (if x<2788 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1900 : Finset ℕ := ([48,72,132,252,1590,1614,1628,1650,1708,1734,1748,1768,2618,2668,2702,2716,2738,2762,2776,2788,3132,3158,3178,3192,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1900 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1900 48 4
  · have he : independentCachedBranchMembers1900.erase 48=independentCachedBranchMembers1898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1898
  · have he : independentCachedBranchMembers1900.filter (independentCachedEdge 48)=independentCachedBranchMembers1899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1899
def independentCachedBranchMembers1901 : Finset ℕ := ([48,72,132,252,1590,1614,1708,1748,2618,2668,2702,2776,3132,3178,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1901 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1901 4 (fun x => (if x<2618 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1708 then (if x<1614 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3132 then (if x<2702 then (if x<2668 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3238 then (if x<3178 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1902 : Finset ℕ := ([48,72,132,252,1590,1614,1628,1650,1708,1734,1748,1768,2618,2668,2702,2716,2738,2762,2776,2788,3132,3158,3178,3192,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1902 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1902 3298 4
  · have he : independentCachedBranchMembers1902.erase 3298=independentCachedBranchMembers1900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1900
  · have he : independentCachedBranchMembers1902.filter (independentCachedEdge 3298)=independentCachedBranchMembers1901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1901
def independentCachedBranchMembers1903 : Finset ℕ := ([48,72,132,252,1628,1650,1734,1768,2716,2738,2762,2788,3132,3178,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1903 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1903 4 (fun x => (if x<2716 then (if x<1628 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3132 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3238 then (if x<3178 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1904 : Finset ℕ := ([48,72,132,252,1590,1614,1628,1650,1708,1734,1748,1768,2618,2668,2702,2716,2738,2762,2776,2788,3118,3132,3158,3178,3192,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1904 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1904 3118 4
  · have he : independentCachedBranchMembers1904.erase 3118=independentCachedBranchMembers1902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1902
  · have he : independentCachedBranchMembers1904.filter (independentCachedEdge 3118)=independentCachedBranchMembers1903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1903
def independentCachedBranchMembers1905 : Finset ℕ := ([72,132,1614,1628,1650,1708,2668,2702,2716,2738,3158,3178,3192,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1905 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1905 4 (fun x => (if x<2716 then (if x<1650 then (if x<1614 then (if x<132 then 0 else 0) else (if x<1628 then 1 else 2)) else (if x<2668 then (if x<1708 then 1 else 2) else (if x<2702 then 2 else 1))) else (if x<3192 then (if x<3158 then (if x<2738 then 2 else 1) else (if x<3178 then 3 else 0)) else (if x<3238 then (if x<3226 then 3 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1906 : Finset ℕ := ([48,72,132,192,252,1590,1614,1628,1650,1708,1734,1748,1768,2618,2668,2702,2716,2738,2762,2776,2788,3118,3132,3158,3178,3192,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1906 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1906 192 4
  · have he : independentCachedBranchMembers1906.erase 192=independentCachedBranchMembers1904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1904
  · have he : independentCachedBranchMembers1906.filter (independentCachedEdge 192)=independentCachedBranchMembers1905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1905
def independentCachedBranchMembers1907 : Finset ℕ := ([72,132,1590,1734,1748,1768,2618,2762,2776,2788,3158,3178,3192,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1907 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1907 4 (fun x => (if x<2776 then (if x<1748 then (if x<1590 then (if x<132 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2618 then (if x<1768 then 2 else 2) else (if x<2762 then 1 else 1))) else (if x<3192 then (if x<3158 then (if x<2788 then 2 else 2) else (if x<3178 then 3 else 0)) else (if x<3238 then (if x<3226 then 3 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1908 : Finset ℕ := ([12,48,72,132,192,252,1590,1614,1628,1650,1708,1734,1748,1768,2618,2668,2702,2716,2738,2762,2776,2788,3118,3132,3158,3178,3192,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1908 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1908 12 4
  · have he : independentCachedBranchMembers1908.erase 12=independentCachedBranchMembers1906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1906
  · have he : independentCachedBranchMembers1908.filter (independentCachedEdge 12)=independentCachedBranchMembers1907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1907
def independentCachedBranchMembers1909 : Finset ℕ := ([12,48,72,132,192,252,1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2714,2716,2738,2740,2762,2764,2776,2786,2788,2800,3118,3130,3132,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1909 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1909 2714 5
  · have he : independentCachedBranchMembers1909.erase 2714=independentCachedBranchMembers1895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1895
  · have he : independentCachedBranchMembers1909.filter (independentCachedEdge 2714)=independentCachedBranchMembers1908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1908
def independentCachedBranchMembers1910 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1910 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1910 1622 6
  · have he : independentCachedBranchMembers1910.erase 1622=independentCachedBranchMembers1804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1804
  · have he : independentCachedBranchMembers1910.filter (independentCachedEdge 1622)=independentCachedBranchMembers1909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1909
def independentCachedBranchMembers1911 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2680,2740,2764,3118,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1911 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1911 6 (fun x => (if x<2740 then (if x<1642 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1596 then (if x<1594 then 1 else 2) else (if x<1614 then 3 else 1))) else (if x<1708 then (if x<1678 then (if x<1644 then 3 else 2) else (if x<1702 then 2 else 3)) else (if x<1752 then (if x<1748 then 1 else 1) else (if x<1776 then 2 else (if x<2680 then 3 else 0))))) else (if x<3228 then (if x<3186 then (if x<3118 then (if x<2764 then 0 else 0) else (if x<3164 then 1 else 4)) else (if x<3192 then (if x<3188 then 4 else 5) else (if x<3222 then 2 else 4))) else (if x<3270 then (if x<3252 then (if x<3250 then 5 else 5) else (if x<3256 then 1 else 4)) else (if x<3276 then (if x<3274 then 5 else 4) else (if x<3300 then 1 else (if x<3304 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1912 : Finset ℕ := ([48,252,1590,1596,1644,1678,1748,1776,2764,3164,3186,3192,3252,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1912 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1912 5 (fun x => (if x<1776 then (if x<1596 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1678 then (if x<1644 then 0 else 1) else (if x<1748 then 1 else 1))) else (if x<3192 then (if x<3164 then (if x<2764 then 0 else 1) else (if x<3186 then 2 else 2)) else (if x<3274 then (if x<3252 then 0 else 0) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1913 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2680,2740,2764,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1913 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1913 3162 5
  · have he : independentCachedBranchMembers1913.erase 3162=independentCachedBranchMembers1911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1911
  · have he : independentCachedBranchMembers1913.filter (independentCachedEdge 3162)=independentCachedBranchMembers1912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1912
def independentCachedBranchMembers1914 : Finset ℕ := ([48,72,1590,1596,1614,1642,1678,1752,2740,2764,3118,3164,3186,3192,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1914 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1914 5 (fun x => (if x<3118 then (if x<1642 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1596 then 0 else (if x<1614 then 1 else 0))) else (if x<1752 then (if x<1678 then 1 else 1) else (if x<2740 then 1 else (if x<2764 then 0 else 0)))) else (if x<3228 then (if x<3186 then (if x<3164 then 1 else 2) else (if x<3192 then 2 else (if x<3222 then 1 else 2))) else (if x<3256 then (if x<3250 then 1 else 0) else (if x<3274 then 2 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1915 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2680,2740,2764,2788,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1915 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1915 2788 5
  · have he : independentCachedBranchMembers1915.erase 2788=independentCachedBranchMembers1913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1913
  · have he : independentCachedBranchMembers1915.filter (independentCachedEdge 2788)=independentCachedBranchMembers1914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1914
def independentCachedBranchMembers1916 : Finset ℕ := ([132,252,1594,1644,1702,1708,1748,1776,2740,2764,3118,3164,3186,3192,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1916 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1916 5 (fun x => (if x<3118 then (if x<1708 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1644 then 1 else (if x<1702 then 1 else 1))) else (if x<1776 then (if x<1748 then 0 else 0) else (if x<2740 then 1 else (if x<2764 then 0 else 0)))) else (if x<3228 then (if x<3186 then (if x<3164 then 1 else 2) else (if x<3192 then 2 else (if x<3222 then 1 else 2))) else (if x<3256 then (if x<3250 then 0 else 1) else (if x<3274 then 2 else (if x<3300 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1917 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2680,2740,2762,2764,2788,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1917 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1917 2762 5
  · have he : independentCachedBranchMembers1917.erase 2762=independentCachedBranchMembers1915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1915
  · have he : independentCachedBranchMembers1917.filter (independentCachedEdge 2762)=independentCachedBranchMembers1916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1916
def independentCachedBranchMembers1918 : Finset ℕ := ([132,252,1596,1642,1678,1708,1748,1752,2740,2764,3118,3162,3188,3192,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1918 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1918 5 (fun x => (if x<3118 then (if x<1708 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1642 then 1 else (if x<1678 then 1 else 1))) else (if x<1752 then (if x<1748 then 0 else 0) else (if x<2740 then 1 else (if x<2764 then 0 else 0)))) else (if x<3250 then (if x<3188 then (if x<3162 then 1 else 2) else (if x<3192 then 2 else (if x<3228 then 1 else 0))) else (if x<3274 then (if x<3270 then 2 else 2) else (if x<3300 then 1 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1919 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2680,2738,2740,2762,2764,2788,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1919 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1919 2738 5
  · have he : independentCachedBranchMembers1919.erase 2738=independentCachedBranchMembers1917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1917
  · have he : independentCachedBranchMembers1919.filter (independentCachedEdge 2738)=independentCachedBranchMembers1918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1918
end EntropyDesigns.QuadraticRefinement
