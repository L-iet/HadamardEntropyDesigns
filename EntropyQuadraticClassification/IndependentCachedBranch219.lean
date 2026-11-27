/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch218
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9792 : Finset ℕ := ([160,190,1582,1622,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2772,2776,3118,3132,3158,3162,3238,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9792 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9792 5 (fun x => (if x<2652 then (if x<1716 then (if x<1622 then (if x<190 then 0 else (if x<1582 then 0 else 1)) else (if x<1702 then 1 else (if x<1706 then 0 else 2))) else (if x<1746 then (if x<1720 then 1 else (if x<1740 then 0 else 1)) else (if x<2618 then (if x<2614 then 2 else 1) else (if x<2638 then 3 else 1)))) else (if x<3132 then (if x<2758 then (if x<2732 then 3 else (if x<2738 then 0 else 0)) else (if x<2776 then (if x<2772 then 4 else 1) else (if x<3118 then 4 else 2))) else (if x<3238 then (if x<3158 then 3 else (if x<3162 then 2 else 3)) else (if x<3256 then (if x<3242 then 4 else 0) else (if x<3276 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9793 : Finset ℕ := ([190,1716,1720,1740,2614,2618,2638,2738,2758,3132,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9793 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9793 4 (fun x => (if x<2638 then (if x<1740 then (if x<1716 then 0 else (if x<1720 then 0 else 1)) else (if x<2614 then 1 else (if x<2618 then 0 else 1))) else (if x<3132 then (if x<2738 then 1 else (if x<2758 then 2 else 2)) else (if x<3256 then 0 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9794 : Finset ℕ := ([80,160,190,1582,1622,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2772,2776,3118,3132,3158,3162,3238,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9794 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9794 80 4
  · have he : independentCachedBranchMembers9794.erase 80=independentCachedBranchMembers9792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9792
  · have he : independentCachedBranchMembers9794.filter (independentCachedEdge 80)=independentCachedBranchMembers9793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9793
def independentCachedBranchMembers9795 : Finset ℕ := ([160,1702,1716,1740,2614,2638,2652,2738,2776,3162,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9795 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9795 4 (fun x => (if x<2652 then (if x<1740 then (if x<1702 then 0 else (if x<1716 then 0 else 1)) else (if x<2614 then 1 else (if x<2638 then 1 else 1))) else (if x<3162 then (if x<2738 then 0 else (if x<2776 then 2 else 2)) else (if x<3238 then 0 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9796 : Finset ℕ := ([40,80,160,190,1582,1622,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2772,2776,3118,3132,3158,3162,3238,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9796 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9796 40 4
  · have he : independentCachedBranchMembers9796.erase 40=independentCachedBranchMembers9794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9794
  · have he : independentCachedBranchMembers9796.filter (independentCachedEdge 40)=independentCachedBranchMembers9795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9795
def independentCachedBranchMembers9797 : Finset ℕ := ([160,190,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,3118,3132,3158,3162] : List ℕ).toFinset
theorem independentCachedBranchBound9797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9797 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9797 4 (fun x => (if x<2614 then (if x<1716 then (if x<1702 then (if x<190 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1740 then (if x<1720 then 1 else 0) else (if x<1746 then 1 else 1))) else (if x<3118 then (if x<2638 then (if x<2618 then 2 else 3) else (if x<2652 then 2 else 3)) else (if x<3158 then (if x<3132 then 2 else 3) else (if x<3162 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9798 : Finset ℕ := ([40,80,160,190,1582,1622,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2772,2776,3118,3132,3158,3162,3238,3242,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9798 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9798 3282 4
  · have he : independentCachedBranchMembers9798.erase 3282=independentCachedBranchMembers9796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9796
  · have he : independentCachedBranchMembers9798.filter (independentCachedEdge 3282)=independentCachedBranchMembers9797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9797
def independentCachedBranchMembers9799 : Finset ℕ := ([40,80,1582,1622,1706,1716,1740,1746,2618,2652,2758,2776,3132,3162,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9799 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9799 4 (fun x => (if x<2618 then (if x<1706 then (if x<1582 then (if x<80 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1740 then (if x<1716 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3132 then (if x<2758 then (if x<2652 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3238 then (if x<3162 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9800 : Finset ℕ := ([40,80,160,190,1582,1622,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2772,2776,3118,3132,3158,3162,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9800 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9800 3252 4
  · have he : independentCachedBranchMembers9800.erase 3252=independentCachedBranchMembers9798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9798
  · have he : independentCachedBranchMembers9800.filter (independentCachedEdge 3252)=independentCachedBranchMembers9799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9799
def independentCachedBranchMembers9801 : Finset ℕ := ([40,80,160,190,1582,1622,1702,1720,2614,2638,2758,2776,3118,3158,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9801 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9801 4 (fun x => (if x<2614 then (if x<1582 then (if x<160 then (if x<80 then 0 else 0) else (if x<190 then 1 else 1)) else (if x<1702 then (if x<1622 then 0 else 0) else (if x<1720 then 1 else 1))) else (if x<3118 then (if x<2758 then (if x<2638 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3238 then (if x<3158 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9802 : Finset ℕ := ([40,80,160,190,1582,1622,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2762,2772,2776,3118,3132,3158,3162,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9802 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9802 2762 4
  · have he : independentCachedBranchMembers9802.erase 2762=independentCachedBranchMembers9800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9800
  · have he : independentCachedBranchMembers9802.filter (independentCachedEdge 2762)=independentCachedBranchMembers9801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9801
def independentCachedBranchMembers9803 : Finset ℕ := ([40,190,1622,1702,1716,1746,2614,2738,2758,2772,3118,3132,3162,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9803 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9803 4 (fun x => (if x<2758 then (if x<1716 then (if x<1622 then (if x<190 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2614 then (if x<1746 then 2 else 2) else (if x<2738 then 1 else 2))) else (if x<3162 then (if x<3118 then (if x<2772 then 1 else 2) else (if x<3132 then 0 else 3)) else (if x<3256 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9804 : Finset ℕ := ([40,80,160,190,1582,1622,1626,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2762,2772,2776,3118,3132,3158,3162,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9804 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9804 1626 4
  · have he : independentCachedBranchMembers9804.erase 1626=independentCachedBranchMembers9802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9802
  · have he : independentCachedBranchMembers9804.filter (independentCachedEdge 1626)=independentCachedBranchMembers9803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9803
def independentCachedBranchMembers9805 : Finset ℕ := ([80,160,1582,1716,1720,1746,2638,2738,2772,2776,3132,3158,3162,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9805 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9805 4 (fun x => (if x<2772 then (if x<1720 then (if x<1582 then (if x<160 then 0 else 0) else (if x<1716 then 1 else 1)) else (if x<2638 then (if x<1746 then 2 else 2) else (if x<2738 then 1 else 2))) else (if x<3162 then (if x<3132 then (if x<2776 then 1 else 2) else (if x<3158 then 3 else 0)) else (if x<3242 then (if x<3238 then 3 else 0) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9806 : Finset ℕ := ([40,80,160,190,1582,1596,1622,1626,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2762,2772,2776,3118,3132,3158,3162,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9806 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9806 1596 4
  · have he : independentCachedBranchMembers9806.erase 1596=independentCachedBranchMembers9804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9804
  · have he : independentCachedBranchMembers9806.filter (independentCachedEdge 1596)=independentCachedBranchMembers9805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9805
def independentCachedBranchMembers9807 : Finset ℕ := ([80,190,1582,1702,1706,1740,2614,2618,2652,2738,2772,2776,3118,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9807 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9807 4 (fun x => (if x<2652 then (if x<1706 then (if x<1582 then (if x<190 then 0 else 1) else (if x<1702 then 0 else 1)) else (if x<2614 then (if x<1740 then 2 else 2) else (if x<2618 then 1 else 2))) else (if x<3118 then (if x<2772 then (if x<2738 then 2 else 3) else (if x<2776 then 0 else 3)) else (if x<3242 then (if x<3238 then 1 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9808 : Finset ℕ := ([40,66,80,160,190,1582,1596,1622,1626,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2762,2772,2776,3118,3132,3158,3162,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9808 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9808 66 4
  · have he : independentCachedBranchMembers9808.erase 66=independentCachedBranchMembers9806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9806
  · have he : independentCachedBranchMembers9808.filter (independentCachedEdge 66)=independentCachedBranchMembers9807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9807
def independentCachedBranchMembers9809 : Finset ℕ := ([40,160,1622,1706,1720,1740,2618,2638,2652,2738,2758,2772,3158,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9809 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9809 4 (fun x => (if x<2652 then (if x<1720 then (if x<1622 then (if x<160 then 0 else 1) else (if x<1706 then 0 else 1)) else (if x<2618 then (if x<1740 then 2 else 2) else (if x<2638 then 2 else 2))) else (if x<3158 then (if x<2758 then (if x<2738 then 1 else 3) else (if x<2772 then 0 else 3)) else (if x<3256 then (if x<3242 then 1 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9810 : Finset ℕ := ([36,40,66,80,160,190,1582,1596,1622,1626,1702,1706,1716,1720,1740,1746,2614,2618,2638,2652,2732,2738,2758,2762,2772,2776,3118,3132,3158,3162,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9810 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9810 36 4
  · have he : independentCachedBranchMembers9810.erase 36=independentCachedBranchMembers9808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9808
  · have he : independentCachedBranchMembers9810.filter (independentCachedEdge 36)=independentCachedBranchMembers9809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9809
def independentCachedBranchMembers9811 : Finset ℕ := ([36,40,48,66,72,80,160,190,192,222,1582,1590,1596,1614,1622,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9811 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9811 2764 5
  · have he : independentCachedBranchMembers9811.erase 2764=independentCachedBranchMembers9791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9791
  · have he : independentCachedBranchMembers9811.filter (independentCachedEdge 2764)=independentCachedBranchMembers9810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9810
def independentCachedBranchMembers9812 : Finset ℕ := ([72,192,222,1590,1614,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,2726,2738,2744,2762,2772,3126,3132,3150,3162,3242,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9812 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9812 5 (fun x => (if x<2652 then (if x<1734 then (if x<1590 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1706 then (if x<1614 then 1 else 0) else (if x<1716 then 2 else 2))) else (if x<1752 then (if x<1740 then 1 else (if x<1746 then 2 else 2)) else (if x<2618 then (if x<2606 then 0 else 3) else (if x<2646 then 1 else 3)))) else (if x<3132 then (if x<2744 then (if x<2726 then 0 else (if x<2738 then 4 else 2)) else (if x<2772 then (if x<2762 then 4 else 0) else (if x<3126 then 2 else 3))) else (if x<3242 then (if x<3150 then 1 else (if x<3162 then 3 else 0)) else (if x<3276 then (if x<3270 then 3 else 4) else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9813 : Finset ℕ := ([222,1706,1746,1752,2606,2646,2652,2726,2772,3162,3242,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9813 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9813 4 (fun x => (if x<2652 then (if x<1752 then (if x<1706 then 0 else (if x<1746 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 1 else 0))) else (if x<3162 then (if x<2726 then 1 else (if x<2772 then 2 else 2)) else (if x<3242 then 0 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9814 : Finset ℕ := ([48,72,192,222,1590,1614,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,2726,2738,2744,2762,2772,3126,3132,3150,3162,3242,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9814 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9814 48 4
  · have he : independentCachedBranchMembers9814.erase 48=independentCachedBranchMembers9812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9812
  · have he : independentCachedBranchMembers9814.filter (independentCachedEdge 48)=independentCachedBranchMembers9813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9813
def independentCachedBranchMembers9815 : Finset ℕ := ([48,72,1590,1614,1706,1716,1740,1746,2618,2652,2726,2744,3132,3162,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9815 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9815 4 (fun x => (if x<2618 then (if x<1706 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1740 then (if x<1716 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3132 then (if x<2726 then (if x<2652 then 2 else 2) else (if x<2744 then 3 else 3)) else (if x<3270 then (if x<3162 then 2 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9816 : Finset ℕ := ([48,72,192,222,1590,1614,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,2726,2738,2744,2762,2772,3126,3132,3150,3162,3242,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9816 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9816 3282 4
  · have he : independentCachedBranchMembers9816.erase 3282=independentCachedBranchMembers9814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9814
  · have he : independentCachedBranchMembers9816.filter (independentCachedEdge 3282)=independentCachedBranchMembers9815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9815
def independentCachedBranchMembers9817 : Finset ℕ := ([192,222,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,3126,3132,3150,3162] : List ℕ).toFinset
theorem independentCachedBranchBound9817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9817 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9817 4 (fun x => (if x<2606 then (if x<1734 then (if x<1706 then (if x<222 then 0 else 0) else (if x<1716 then 1 else 1)) else (if x<1746 then (if x<1740 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3126 then (if x<2646 then (if x<2618 then 2 else 3) else (if x<2652 then 2 else 3)) else (if x<3150 then (if x<3132 then 2 else 3) else (if x<3162 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9818 : Finset ℕ := ([48,72,192,222,1590,1614,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,2726,2738,2744,2762,2772,3126,3132,3150,3162,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9818 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9818 3252 4
  · have he : independentCachedBranchMembers9818.erase 3252=independentCachedBranchMembers9816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9816
  · have he : independentCachedBranchMembers9818.filter (independentCachedEdge 3252)=independentCachedBranchMembers9817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9817
def independentCachedBranchMembers9819 : Finset ℕ := ([48,72,192,222,1590,1614,1734,1752,2606,2646,2726,2744,3126,3150,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9819 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9819 4 (fun x => (if x<2606 then (if x<1590 then (if x<192 then (if x<72 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1734 then (if x<1614 then 0 else 0) else (if x<1752 then 1 else 1))) else (if x<3126 then (if x<2726 then (if x<2646 then 2 else 2) else (if x<2744 then 3 else 3)) else (if x<3270 then (if x<3150 then 2 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9820 : Finset ℕ := ([48,72,192,222,1590,1614,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,2726,2732,2738,2744,2762,2772,3126,3132,3150,3162,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9820 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9820 2732 4
  · have he : independentCachedBranchMembers9820.erase 2732=independentCachedBranchMembers9818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9818
  · have he : independentCachedBranchMembers9820.filter (independentCachedEdge 2732)=independentCachedBranchMembers9819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9819
def independentCachedBranchMembers9821 : Finset ℕ := ([48,192,1614,1716,1746,1752,2606,2738,2744,2772,3126,3132,3162,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9821 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9821 4 (fun x => (if x<2744 then (if x<1746 then (if x<1614 then (if x<192 then 0 else 0) else (if x<1716 then 1 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2738 then 1 else 1))) else (if x<3162 then (if x<3126 then (if x<2772 then 2 else 2) else (if x<3132 then 0 else 3)) else (if x<3270 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9822 : Finset ℕ := ([48,72,192,222,1590,1614,1626,1706,1716,1734,1740,1746,1752,2606,2618,2646,2652,2726,2732,2738,2744,2762,2772,3126,3132,3150,3162,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9822 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9822 1626 4
  · have he : independentCachedBranchMembers9822.erase 1626=independentCachedBranchMembers9820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9820
  · have he : independentCachedBranchMembers9822.filter (independentCachedEdge 1626)=independentCachedBranchMembers9821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9821
def independentCachedBranchMembers9823 : Finset ℕ := ([72,222,1590,1716,1734,1746,2646,2726,2738,2772,3132,3150,3162,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9823 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9823 4 (fun x => (if x<2738 then (if x<1734 then (if x<1590 then (if x<222 then 0 else 0) else (if x<1716 then 1 else 2)) else (if x<2646 then (if x<1746 then 1 else 2) else (if x<2726 then 1 else 1))) else (if x<3162 then (if x<3132 then (if x<2772 then 2 else 2) else (if x<3150 then 3 else 0)) else (if x<3276 then (if x<3242 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
