/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch221
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9888 : Finset ℕ := ([36,80,190,192,1582,1590,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2740,2770,2776,3118,3126,3132,3162,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9888 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9888 1590 4
  · have he : independentCachedBranchMembers9888.erase 1590=independentCachedBranchMembers9886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9886
  · have he : independentCachedBranchMembers9888.filter (independentCachedEdge 1590)=independentCachedBranchMembers9887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9887
def independentCachedBranchMembers9889 : Finset ℕ := ([80,190,192,1582,1708,1746,2606,2620,2770,3118,3132,3244] : List ℕ).toFinset
theorem independentCachedBranchBound9889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9889 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9889 4 (fun x => (if x<2606 then (if x<1582 then (if x<190 then 0 else (if x<192 then 1 else 2)) else (if x<1708 then 0 else (if x<1746 then 1 else 2))) else (if x<3118 then (if x<2620 then 1 else (if x<2770 then 2 else 0)) else (if x<3132 then 2 else (if x<3244 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9890 : Finset ℕ := ([36,72,80,190,192,1582,1590,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2740,2770,2776,3118,3126,3132,3162,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9890 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9890 72 4
  · have he : independentCachedBranchMembers9890.erase 72=independentCachedBranchMembers9888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9888
  · have he : independentCachedBranchMembers9890.filter (independentCachedEdge 72)=independentCachedBranchMembers9889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9889
def independentCachedBranchMembers9891 : Finset ℕ := ([72,190,1590,1702,1716,1746,2614,2726,2740,2770,3118,3132,3162,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9891 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9891 4 (fun x => (if x<2740 then (if x<1716 then (if x<1590 then (if x<190 then 0 else 1) else (if x<1702 then 0 else 1)) else (if x<2614 then (if x<1746 then 2 else 2) else (if x<2726 then 1 else 0))) else (if x<3162 then (if x<3118 then (if x<2770 then 3 else 3) else (if x<3132 then 1 else 2)) else (if x<3274 then (if x<3244 then 2 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9892 : Finset ℕ := ([36,72,80,190,192,1582,1590,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2740,2770,2776,3118,3126,3132,3162,3238,3244,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9892 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9892 3282 4
  · have he : independentCachedBranchMembers9892.erase 3282=independentCachedBranchMembers9890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9890
  · have he : independentCachedBranchMembers9892.filter (independentCachedEdge 3282)=independentCachedBranchMembers9891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9891
def independentCachedBranchMembers9893 : Finset ℕ := ([80,192,1582,1716,1746,1752,2606,2740,2770,2776,3126,3132,3162,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9893 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9893 4 (fun x => (if x<2770 then (if x<1746 then (if x<1582 then (if x<192 then 0 else 1) else (if x<1716 then 0 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2740 then 1 else 3))) else (if x<3162 then (if x<3126 then (if x<2776 then 0 else 3) else (if x<3132 then 2 else 1)) else (if x<3244 then (if x<3238 then 2 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9894 : Finset ℕ := ([36,72,80,190,192,1582,1590,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2740,2770,2776,3118,3126,3132,3162,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9894 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9894 3252 4
  · have he : independentCachedBranchMembers9894.erase 3252=independentCachedBranchMembers9892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9892
  · have he : independentCachedBranchMembers9894.filter (independentCachedEdge 3252)=independentCachedBranchMembers9893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9893
def independentCachedBranchMembers9895 : Finset ℕ := ([80,190,1582,1702,1708,1738,2614,2620,2650,2740,2770,2776,3118,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9895 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9895 4 (fun x => (if x<2650 then (if x<1708 then (if x<1582 then (if x<190 then 0 else 1) else (if x<1702 then 0 else 1)) else (if x<2614 then (if x<1738 then 2 else 2) else (if x<2620 then 1 else 2))) else (if x<3118 then (if x<2770 then (if x<2740 then 2 else 3) else (if x<2776 then 0 else 3)) else (if x<3244 then (if x<3238 then 1 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9896 : Finset ℕ := ([36,72,80,190,192,1582,1590,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2740,2762,2770,2776,3118,3126,3132,3162,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9896 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9896 2762 4
  · have he : independentCachedBranchMembers9896.erase 2762=independentCachedBranchMembers9894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9894
  · have he : independentCachedBranchMembers9896.filter (independentCachedEdge 2762)=independentCachedBranchMembers9895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9895
def independentCachedBranchMembers9897 : Finset ℕ := ([72,192,1590,1708,1738,1752,2606,2620,2650,2726,2740,2770,3126,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9897 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9897 4 (fun x => (if x<2650 then (if x<1738 then (if x<1590 then (if x<192 then 0 else 1) else (if x<1708 then 0 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2620 then 2 else 1))) else (if x<3126 then (if x<2740 then (if x<2726 then 2 else 0) else (if x<2770 then 3 else 3)) else (if x<3274 then (if x<3244 then 1 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9898 : Finset ℕ := ([36,72,80,190,192,1582,1590,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2732,2740,2762,2770,2776,3118,3126,3132,3162,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9898 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9898 2732 4
  · have he : independentCachedBranchMembers9898.erase 2732=independentCachedBranchMembers9896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9896
  · have he : independentCachedBranchMembers9898.filter (independentCachedEdge 2732)=independentCachedBranchMembers9897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9897
def independentCachedBranchMembers9899 : Finset ℕ := ([192,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,3118,3126,3132,3162] : List ℕ).toFinset
theorem independentCachedBranchBound9899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9899 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9899 4 (fun x => (if x<2606 then (if x<1716 then (if x<1702 then 0 else (if x<1708 then 1 else 2)) else (if x<1746 then (if x<1738 then 3 else 0) else (if x<1752 then 1 else 2))) else (if x<3118 then (if x<2620 then (if x<2614 then 1 else 0) else (if x<2650 then 3 else 1)) else (if x<3132 then (if x<3126 then 2 else 3) else (if x<3162 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9900 : Finset ℕ := ([192,1738,1746,1752,2650,3162] : List ℕ).toFinset
theorem independentCachedBranchBound9900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9900 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9900 3 (fun x => (if x<1752 then (if x<1738 then 0 else (if x<1746 then 0 else 1)) else (if x<2650 then 2 else (if x<3162 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9901 : Finset ℕ := ([190,192,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,3118,3126,3132,3162] : List ℕ).toFinset
theorem independentCachedBranchBound9901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9901 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9901 190 3
  · have he : independentCachedBranchMembers9901.erase 190=independentCachedBranchMembers9899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9899
  · have he : independentCachedBranchMembers9901.filter (independentCachedEdge 190)=independentCachedBranchMembers9900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9900
def independentCachedBranchMembers9902 : Finset ℕ := ([36,72,80,190,192,1582,1590,1626,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2732,2740,2762,2770,2776,3118,3126,3132,3162,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9902 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9902 1626 4
  · have he : independentCachedBranchMembers9902.erase 1626=independentCachedBranchMembers9898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9898
  · have he : independentCachedBranchMembers9902.filter (independentCachedEdge 1626)=independentCachedBranchMembers9901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9901
def independentCachedBranchMembers9903 : Finset ℕ := ([72,80,1582,1590,1708,1716,1738,1746,2620,2650,2726,2776,3132,3162,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9903 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9903 4 (fun x => (if x<2620 then (if x<1708 then (if x<1582 then (if x<80 then 0 else 1) else (if x<1590 then 1 else 0)) else (if x<1738 then (if x<1716 then 2 else 3) else (if x<1746 then 2 else 3))) else (if x<3132 then (if x<2726 then (if x<2650 then 2 else 2) else (if x<2776 then 0 else 1)) else (if x<3238 then (if x<3162 then 3 else 3) else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9904 : Finset ℕ := ([36,72,80,190,192,1582,1590,1596,1626,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2732,2740,2762,2770,2776,3118,3126,3132,3162,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9904 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9904 1596 4
  · have he : independentCachedBranchMembers9904.erase 1596=independentCachedBranchMembers9902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9902
  · have he : independentCachedBranchMembers9904.filter (independentCachedEdge 1596)=independentCachedBranchMembers9903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9903
def independentCachedBranchMembers9905 : Finset ℕ := ([72,80,190,192,1582,1590,1702,1752,2606,2614,2726,2776,3118,3126,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9905 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9905 4 (fun x => (if x<2606 then (if x<1582 then (if x<190 then (if x<80 then 0 else 1) else (if x<192 then 2 else 3)) else (if x<1702 then (if x<1590 then 1 else 0) else (if x<1752 then 2 else 3))) else (if x<3118 then (if x<2726 then (if x<2614 then 2 else 3) else (if x<2776 then 0 else 1)) else (if x<3238 then (if x<3126 then 3 else 2) else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9906 : Finset ℕ := ([36,66,72,80,190,192,1582,1590,1596,1626,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2732,2740,2762,2770,2776,3118,3126,3132,3162,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9906 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9906 66 4
  · have he : independentCachedBranchMembers9906.erase 66=independentCachedBranchMembers9904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9904
  · have he : independentCachedBranchMembers9906.filter (independentCachedEdge 66)=independentCachedBranchMembers9905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9905
def independentCachedBranchMembers9907 : Finset ℕ := ([36,40,48,66,68,72,80,160,190,192,222,1582,1590,1594,1596,1614,1622,1626,1628,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9907 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9907 68 5
  · have he : independentCachedBranchMembers9907.erase 68=independentCachedBranchMembers9879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9879
  · have he : independentCachedBranchMembers9907.filter (independentCachedEdge 68)=independentCachedBranchMembers9906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9906
def independentCachedBranchMembers9908 : Finset ℕ := ([48,66,160,222,1614,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2758,3132,3150,3158,3162,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9908 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9908 5 (fun x => (if x<2620 then (if x<1708 then (if x<160 then (if x<66 then 0 else 0) else (if x<222 then 1 else (if x<1614 then 2 else 0))) else (if x<1734 then (if x<1716 then 1 else (if x<1720 then 3 else 4)) else (if x<1738 then 2 else (if x<1746 then 4 else 3)))) else (if x<3132 then (if x<2650 then (if x<2638 then 3 else (if x<2646 then 2 else 1)) else (if x<2740 then 3 else (if x<2758 then 0 else 0))) else (if x<3162 then (if x<3150 then 4 else (if x<3158 then 4 else 2)) else (if x<3256 then 1 else (if x<3274 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9909 : Finset ℕ := ([160,1708,1716,1734,2650,2740,2758,3132,3150,3158,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9909 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9909 4 (fun x => (if x<2758 then (if x<1734 then (if x<1708 then 0 else (if x<1716 then 0 else 1)) else (if x<2650 then 1 else (if x<2740 then 0 else 2))) else (if x<3158 then (if x<3132 then 2 else (if x<3150 then 1 else 1)) else (if x<3256 then 0 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9910 : Finset ℕ := ([48,66,160,222,1614,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2758,3132,3150,3158,3162,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9910 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9910 3270 4
  · have he : independentCachedBranchMembers9910.erase 3270=independentCachedBranchMembers9908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9908
  · have he : independentCachedBranchMembers9910.filter (independentCachedEdge 3270)=independentCachedBranchMembers9909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9909
def independentCachedBranchMembers9911 : Finset ℕ := ([48,222,1614,1708,1734,1738,2638,2758,3132,3158,3162,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9911 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9911 4 (fun x => (if x<2638 then (if x<1708 then (if x<222 then 0 else (if x<1614 then 1 else 0)) else (if x<1734 then 2 else (if x<1738 then 1 else 2))) else (if x<3158 then (if x<2758 then 1 else (if x<3132 then 0 else 2)) else (if x<3162 then 1 else (if x<3256 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9912 : Finset ℕ := ([48,66,160,222,1614,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2758,3132,3150,3158,3162,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9912 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9912 3244 4
  · have he : independentCachedBranchMembers9912.erase 3244=independentCachedBranchMembers9910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9910
  · have he : independentCachedBranchMembers9912.filter (independentCachedEdge 3244)=independentCachedBranchMembers9911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9911
def independentCachedBranchMembers9913 : Finset ℕ := ([48,160,1614,1716,1720,1746,2620,2646,2650,2758,3150,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9913 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9913 4 (fun x => (if x<2620 then (if x<1716 then (if x<160 then 0 else (if x<1614 then 1 else 0)) else (if x<1720 then 1 else (if x<1746 then 2 else 2))) else (if x<2758 then (if x<2646 then 2 else (if x<2650 then 2 else 1)) else (if x<3150 then 0 else (if x<3256 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9914 : Finset ℕ := ([48,66,160,222,1614,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2758,2770,3132,3150,3158,3162,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9914 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9914 2770 4
  · have he : independentCachedBranchMembers9914.erase 2770=independentCachedBranchMembers9912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9912
  · have he : independentCachedBranchMembers9914.filter (independentCachedEdge 2770)=independentCachedBranchMembers9913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9913
def independentCachedBranchMembers9915 : Finset ℕ := ([222,1720,1738,1746,2620,2638,2646,2740,2758,3162,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9915 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9915 4 (fun x => (if x<2646 then (if x<1746 then (if x<1720 then 0 else (if x<1738 then 1 else 0)) else (if x<2620 then 1 else (if x<2638 then 1 else 0))) else (if x<3162 then (if x<2740 then 1 else (if x<2758 then 2 else 2)) else (if x<3256 then 0 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9916 : Finset ℕ := ([48,66,160,222,1614,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2744,2758,2770,3132,3150,3158,3162,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9916 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9916 2744 4
  · have he : independentCachedBranchMembers9916.erase 2744=independentCachedBranchMembers9914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9914
  · have he : independentCachedBranchMembers9916.filter (independentCachedEdge 2744)=independentCachedBranchMembers9915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9915
def independentCachedBranchMembers9917 : Finset ℕ := ([48,1614,1708,1720,1734,1746,2620,2646,2740,3132,3158,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9917 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9917 4 (fun x => (if x<2620 then (if x<1720 then (if x<1614 then 0 else (if x<1708 then 0 else 1)) else (if x<1734 then 2 else (if x<1746 then 1 else 2))) else (if x<3132 then (if x<2646 then 1 else (if x<2740 then 1 else 0)) else (if x<3158 then 2 else (if x<3274 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9918 : Finset ℕ := ([48,66,160,222,1614,1622,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2744,2758,2770,3132,3150,3158,3162,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9918 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9918 1622 4
  · have he : independentCachedBranchMembers9918.erase 1622=independentCachedBranchMembers9916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9916
  · have he : independentCachedBranchMembers9918.filter (independentCachedEdge 1622)=independentCachedBranchMembers9917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9917
def independentCachedBranchMembers9919 : Finset ℕ := ([48,160,222,1614,1716,1738,2638,2650,2740,3150,3162,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9919 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9919 4 (fun x => (if x<2638 then (if x<1614 then (if x<160 then 0 else (if x<222 then 1 else 2)) else (if x<1716 then 0 else (if x<1738 then 1 else 2))) else (if x<3150 then (if x<2650 then 1 else (if x<2740 then 2 else 0)) else (if x<3162 then 2 else (if x<3274 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
