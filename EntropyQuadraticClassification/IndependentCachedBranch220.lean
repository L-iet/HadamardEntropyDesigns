/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch219
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9824 : Finset ℕ := ([48,72,192,222,1590,1596,1614,1626,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,2726,2732,2738,2744,2762,2772,3126,3132,3150,3162,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9824 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9824 1596 4
  · have he : independentCachedBranchMembers9824.erase 1596=independentCachedBranchMembers9822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9822
  · have he : independentCachedBranchMembers9824.filter (independentCachedEdge 1596)=independentCachedBranchMembers9823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9823
def independentCachedBranchMembers9825 : Finset ℕ := ([72,192,1590,1706,1740,1752,2606,2618,2652,2726,2738,2772,3126,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9825 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9825 4 (fun x => (if x<2652 then (if x<1740 then (if x<1590 then (if x<192 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2618 then 2 else 1))) else (if x<3126 then (if x<2738 then (if x<2726 then 2 else 0) else (if x<2772 then 3 else 3)) else (if x<3276 then (if x<3242 then 1 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9826 : Finset ℕ := ([48,66,72,192,222,1590,1596,1614,1626,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,2726,2732,2738,2744,2762,2772,3126,3132,3150,3162,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9826 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9826 66 4
  · have he : independentCachedBranchMembers9826.erase 66=independentCachedBranchMembers9824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9824
  · have he : independentCachedBranchMembers9826.filter (independentCachedEdge 66)=independentCachedBranchMembers9825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9825
def independentCachedBranchMembers9827 : Finset ℕ := ([48,222,1614,1706,1734,1740,2618,2646,2652,2738,2744,2772,3150,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9827 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9827 4 (fun x => (if x<2652 then (if x<1734 then (if x<1614 then (if x<222 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<2618 then (if x<1740 then 1 else 2) else (if x<2646 then 2 else 1))) else (if x<3150 then (if x<2744 then (if x<2738 then 2 else 0) else (if x<2772 then 3 else 3)) else (if x<3270 then (if x<3242 then 1 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9828 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,2726,2732,2738,2744,2762,2772,3126,3132,3150,3162,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9828 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9828 36 4
  · have he : independentCachedBranchMembers9828.erase 36=independentCachedBranchMembers9826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9826
  · have he : independentCachedBranchMembers9828.filter (independentCachedEdge 36)=independentCachedBranchMembers9827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9827
def independentCachedBranchMembers9829 : Finset ℕ := ([36,40,48,66,72,80,160,190,192,222,1582,1590,1596,1614,1622,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9829 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9829 2730 5
  · have he : independentCachedBranchMembers9829.erase 2730=independentCachedBranchMembers9811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9811
  · have he : independentCachedBranchMembers9829.filter (independentCachedEdge 2730)=independentCachedBranchMembers9828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9828
def independentCachedBranchMembers9830 : Finset ℕ := ([48,192,1596,1614,1622,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2740,2744,2758,2770,3118,3126,3130,3164,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9830 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9830 5 (fun x => (if x<2618 then (if x<1706 then (if x<1614 then (if x<192 then 0 else (if x<1596 then 0 else 0)) else (if x<1622 then 1 else (if x<1702 then 2 else 1))) else (if x<1748 then (if x<1714 then 3 else (if x<1740 then 2 else 0)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2614 then 1 else 0)))) else (if x<3126 then (if x<2744 then (if x<2652 then 3 else (if x<2740 then 1 else 1)) else (if x<2770 then (if x<2758 then 2 else 0) else (if x<3118 then 2 else 3))) else (if x<3244 then (if x<3130 then 4 else (if x<3164 then 0 else 4)) else (if x<3270 then (if x<3256 then 4 else 3) else (if x<3274 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9831 : Finset ℕ := ([192,1614,1622,1740,1748,1752,2652,2758,2770,3164,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9831 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9831 4 (fun x => (if x<2652 then (if x<1740 then (if x<1614 then 0 else (if x<1622 then 1 else 2)) else (if x<1748 then 0 else (if x<1752 then 1 else 2))) else (if x<3164 then (if x<2758 then 1 else (if x<2770 then 0 else 2)) else (if x<3270 then 3 else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9832 : Finset ℕ := ([48,190,192,1596,1614,1622,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2740,2744,2758,2770,3118,3126,3130,3164,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9832 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9832 190 4
  · have he : independentCachedBranchMembers9832.erase 190=independentCachedBranchMembers9830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9830
  · have he : independentCachedBranchMembers9832.filter (independentCachedEdge 190)=independentCachedBranchMembers9831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9831
def independentCachedBranchMembers9833 : Finset ℕ := ([48,1614,1702,1714,1740,1752,2614,2652,2740,3126,3164,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9833 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9833 4 (fun x => (if x<2614 then (if x<1714 then (if x<1614 then 0 else (if x<1702 then 0 else 1)) else (if x<1740 then 2 else (if x<1752 then 1 else 2))) else (if x<3126 then (if x<2652 then 1 else (if x<2740 then 1 else 0)) else (if x<3164 then 2 else (if x<3274 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9834 : Finset ℕ := ([40,48,190,192,1596,1614,1622,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2740,2744,2758,2770,3118,3126,3130,3164,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9834 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9834 40 4
  · have he : independentCachedBranchMembers9834.erase 40=independentCachedBranchMembers9832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9832
  · have he : independentCachedBranchMembers9834.filter (independentCachedEdge 40)=independentCachedBranchMembers9833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9833
def independentCachedBranchMembers9835 : Finset ℕ := ([190,1614,1702,1706,1740,2614,2618,2652,2740,2744,2770,3118,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9835 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9835 4 (fun x => (if x<2652 then (if x<1706 then (if x<1614 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then (if x<1740 then 1 else 2) else (if x<2618 then 0 else 2))) else (if x<3118 then (if x<2744 then (if x<2740 then 1 else 3) else (if x<2770 then 1 else 3)) else (if x<3270 then (if x<3244 then 0 else 3) else (if x<3274 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9836 : Finset ℕ := ([1702,1706,2652,2770,3118,3244] : List ℕ).toFinset
theorem independentCachedBranchBound9836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9836 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9836 3 (fun x => (if x<2770 then (if x<1706 then 0 else (if x<2652 then 1 else 0)) else (if x<3118 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9837 : Finset ℕ := ([48,190,1614,1702,1706,1740,2614,2618,2652,2740,2744,2770,3118,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9837 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9837 48 3
  · have he : independentCachedBranchMembers9837.erase 48=independentCachedBranchMembers9835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9835
  · have he : independentCachedBranchMembers9837.filter (independentCachedEdge 48)=independentCachedBranchMembers9836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9836
def independentCachedBranchMembers9838 : Finset ℕ := ([40,48,190,192,1596,1614,1622,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2740,2744,2758,2770,3118,3126,3130,3164,3244,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9838 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9838 3282 4
  · have he : independentCachedBranchMembers9838.erase 3282=independentCachedBranchMembers9834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9834
  · have he : independentCachedBranchMembers9838.filter (independentCachedEdge 3282)=independentCachedBranchMembers9837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9837
def independentCachedBranchMembers9839 : Finset ℕ := ([192,1622,1706,1740,1752,2606,2618,2652,2740,2758,2770,3126,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9839 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9839 4 (fun x => (if x<2652 then (if x<1740 then (if x<1622 then 0 else (if x<1706 then 1 else 2)) else (if x<2606 then (if x<1752 then 0 else 1) else (if x<2618 then 2 else 0))) else (if x<3126 then (if x<2758 then (if x<2740 then 1 else 3) else (if x<2770 then 3 else 1)) else (if x<3256 then (if x<3244 then 0 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9840 : Finset ℕ := ([1740,1752,2652,2740,3126,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9840 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9840 3 (fun x => (if x<2740 then (if x<1752 then 0 else (if x<2652 then 1 else 0)) else (if x<3126 then 2 else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9841 : Finset ℕ := ([40,192,1622,1706,1740,1752,2606,2618,2652,2740,2758,2770,3126,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9841 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9841 40 3
  · have he : independentCachedBranchMembers9841.erase 40=independentCachedBranchMembers9839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9839
  · have he : independentCachedBranchMembers9841.filter (independentCachedEdge 40)=independentCachedBranchMembers9840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9840
def independentCachedBranchMembers9842 : Finset ℕ := ([40,48,190,192,1596,1614,1622,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2740,2744,2758,2770,3118,3126,3130,3164,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9842 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9842 3252 4
  · have he : independentCachedBranchMembers9842.erase 3252=independentCachedBranchMembers9838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9838
  · have he : independentCachedBranchMembers9842.filter (independentCachedEdge 3252)=independentCachedBranchMembers9841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9841
def independentCachedBranchMembers9843 : Finset ℕ := ([40,190,1622,1702,1714,1748,2614,2740,2758,2770,3118,3130,3164,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9843 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9843 4 (fun x => (if x<2758 then (if x<1714 then (if x<1622 then (if x<190 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2614 then (if x<1748 then 2 else 2) else (if x<2740 then 1 else 2))) else (if x<3164 then (if x<3118 then (if x<2770 then 1 else 2) else (if x<3130 then 0 else 3)) else (if x<3256 then (if x<3244 then 3 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9844 : Finset ℕ := ([40,48,190,192,1596,1614,1622,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2740,2744,2758,2762,2770,3118,3126,3130,3164,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9844 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9844 2762 4
  · have he : independentCachedBranchMembers9844.erase 2762=independentCachedBranchMembers9842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9842
  · have he : independentCachedBranchMembers9844.filter (independentCachedEdge 2762)=independentCachedBranchMembers9843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9843
def independentCachedBranchMembers9845 : Finset ℕ := ([48,192,1614,1714,1748,1752,2606,2740,2744,2770,3126,3130,3164,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9845 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9845 4 (fun x => (if x<2744 then (if x<1748 then (if x<1614 then (if x<192 then 0 else 0) else (if x<1714 then 1 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2740 then 1 else 1))) else (if x<3164 then (if x<3126 then (if x<2770 then 2 else 2) else (if x<3130 then 0 else 3)) else (if x<3270 then (if x<3244 then 3 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9846 : Finset ℕ := ([40,48,190,192,1596,1614,1622,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2732,2740,2744,2758,2762,2770,3118,3126,3130,3164,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9846 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9846 2732 4
  · have he : independentCachedBranchMembers9846.erase 2732=independentCachedBranchMembers9844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9844
  · have he : independentCachedBranchMembers9846.filter (independentCachedEdge 2732)=independentCachedBranchMembers9845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9845
def independentCachedBranchMembers9847 : Finset ℕ := ([40,48,190,192,1614,1622,1702,1752,2606,2614,2744,2758,3118,3126,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound9847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9847 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9847 4 (fun x => (if x<2606 then (if x<1614 then (if x<190 then (if x<48 then 0 else 1) else (if x<192 then 0 else 1)) else (if x<1702 then (if x<1622 then 2 else 3) else (if x<1752 then 2 else 3))) else (if x<3118 then (if x<2744 then (if x<2614 then 0 else 1) else (if x<2758 then 0 else 1)) else (if x<3256 then (if x<3126 then 2 else 3) else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9848 : Finset ℕ := ([40,48,190,192,1596,1614,1622,1626,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2732,2740,2744,2758,2762,2770,3118,3126,3130,3164,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9848 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9848 1626 4
  · have he : independentCachedBranchMembers9848.erase 1626=independentCachedBranchMembers9846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9846
  · have he : independentCachedBranchMembers9848.filter (independentCachedEdge 1626)=independentCachedBranchMembers9847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9847
def independentCachedBranchMembers9849 : Finset ℕ := ([192,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,3118,3126,3130,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9849 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9849 4 (fun x => (if x<2606 then (if x<1714 then (if x<1702 then 0 else (if x<1706 then 1 else 2)) else (if x<1748 then (if x<1740 then 3 else 0) else (if x<1752 then 1 else 2))) else (if x<3118 then (if x<2618 then (if x<2614 then 1 else 0) else (if x<2652 then 3 else 1)) else (if x<3130 then (if x<3126 then 2 else 3) else (if x<3164 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9850 : Finset ℕ := ([192,1740,1748,1752,2652,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9850 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9850 3 (fun x => (if x<1752 then (if x<1740 then 0 else (if x<1748 then 0 else 1)) else (if x<2652 then 2 else (if x<3164 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9851 : Finset ℕ := ([190,192,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,3118,3126,3130,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9851 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9851 190 3
  · have he : independentCachedBranchMembers9851.erase 190=independentCachedBranchMembers9849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9849
  · have he : independentCachedBranchMembers9851.filter (independentCachedEdge 190)=independentCachedBranchMembers9850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9850
def independentCachedBranchMembers9852 : Finset ℕ := ([40,48,66,190,192,1596,1614,1622,1626,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2732,2740,2744,2758,2762,2770,3118,3126,3130,3164,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9852 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9852 66 4
  · have he : independentCachedBranchMembers9852.erase 66=independentCachedBranchMembers9848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9848
  · have he : independentCachedBranchMembers9852.filter (independentCachedEdge 66)=independentCachedBranchMembers9851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9851
def independentCachedBranchMembers9853 : Finset ℕ := ([40,48,1614,1622,1706,1714,1740,1748,2618,2652,2744,2758,3130,3164,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound9853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9853 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9853 4 (fun x => (if x<2618 then (if x<1706 then (if x<1614 then (if x<48 then 0 else 1) else (if x<1622 then 1 else 0)) else (if x<1740 then (if x<1714 then 2 else 3) else (if x<1748 then 2 else 3))) else (if x<3130 then (if x<2744 then (if x<2652 then 2 else 2) else (if x<2758 then 0 else 1)) else (if x<3256 then (if x<3164 then 3 else 3) else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9854 : Finset ℕ := ([36,40,48,66,190,192,1596,1614,1622,1626,1702,1706,1714,1740,1748,1752,2606,2614,2618,2652,2732,2740,2744,2758,2762,2770,3118,3126,3130,3164,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9854 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9854 36 4
  · have he : independentCachedBranchMembers9854.erase 36=independentCachedBranchMembers9852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9852
  · have he : independentCachedBranchMembers9854.filter (independentCachedEdge 36)=independentCachedBranchMembers9853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9853
def independentCachedBranchMembers9855 : Finset ℕ := ([36,40,48,66,72,80,160,190,192,222,1582,1590,1596,1614,1622,1626,1628,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9855 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9855 1628 5
  · have he : independentCachedBranchMembers9855.erase 1628=independentCachedBranchMembers9829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9829
  · have he : independentCachedBranchMembers9855.filter (independentCachedEdge 1628)=independentCachedBranchMembers9854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9854
end EntropyDesigns.QuadraticRefinement
