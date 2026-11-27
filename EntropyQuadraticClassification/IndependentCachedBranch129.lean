/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch128
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6912 : Finset ℕ := ([40,130,144,1582,1596,1642,1652,1686,1690,1740,1746,2614,2618,2668,2702,2716,2758,2762,2772,2776,3118,3132,3174,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6912 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6912 5 (fun x => (if x<2702 then (if x<1686 then (if x<1582 then (if x<130 then 0 else (if x<144 then 0 else 1)) else (if x<1642 then (if x<1596 then 1 else 0) else (if x<1652 then 2 else 2))) else (if x<1746 then (if x<1690 then 0 else (if x<1740 then 1 else 2)) else (if x<2618 then (if x<2614 then 2 else 3) else (if x<2668 then 4 else 0)))) else (if x<3132 then (if x<2762 then (if x<2716 then 3 else (if x<2758 then 4 else 0)) else (if x<2776 then (if x<2772 then 2 else 2) else (if x<3118 then 1 else 3))) else (if x<3222 then (if x<3174 then 4 else (if x<3192 then 1 else 0)) else (if x<3276 then (if x<3226 then 3 else 4) else (if x<3282 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6913 : Finset ℕ := ([40,1642,1686,1740,2618,2702,2716,2758,2772,3192,3222,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6913 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6913 4 (fun x => (if x<2716 then (if x<1740 then (if x<1642 then 0 else (if x<1686 then 0 else 1)) else (if x<2618 then 1 else (if x<2702 then 0 else 1))) else (if x<3192 then (if x<2758 then 2 else (if x<2772 then 2 else 1)) else (if x<3222 then 0 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6914 : Finset ℕ := ([36,40,130,144,1582,1596,1642,1652,1686,1690,1740,1746,2614,2618,2668,2702,2716,2758,2762,2772,2776,3118,3132,3174,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6914 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6914 36 4
  · have he : independentCachedBranchMembers6914.erase 36=independentCachedBranchMembers6912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6912
  · have he : independentCachedBranchMembers6914.filter (independentCachedEdge 36)=independentCachedBranchMembers6913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6913
def independentCachedBranchMembers6915 : Finset ℕ := ([40,144,1582,1642,1652,1686,1740,1746,2618,2716,2758,2776,3132,3174,3192,3226] : List ℕ).toFinset
theorem independentCachedBranchBound6915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6915 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6915 4 (fun x => (if x<2618 then (if x<1652 then (if x<1582 then (if x<144 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1740 then (if x<1686 then 1 else 0) else (if x<1746 then 1 else 1))) else (if x<3132 then (if x<2758 then (if x<2716 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3192 then (if x<3174 then 2 else 3) else (if x<3226 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6916 : Finset ℕ := ([36,40,130,144,1582,1596,1642,1652,1686,1690,1740,1746,2614,2618,2668,2702,2716,2758,2762,2772,2776,3118,3132,3174,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6916 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6916 3188 4
  · have he : independentCachedBranchMembers6916.erase 3188=independentCachedBranchMembers6914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6914
  · have he : independentCachedBranchMembers6916.filter (independentCachedEdge 3188)=independentCachedBranchMembers6915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6915
def independentCachedBranchMembers6917 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6917 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6917 2764 5
  · have he : independentCachedBranchMembers6917.erase 2764=independentCachedBranchMembers6911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6911
  · have he : independentCachedBranchMembers6917.filter (independentCachedEdge 2764)=independentCachedBranchMembers6916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6916
def independentCachedBranchMembers6918 : Finset ℕ := ([36,48,136,192,1582,1596,1650,1652,1686,1738,1740,1752,2614,2668,2680,2702,2714,2716,2758,2770,2772,3130,3132,3174,3188,3222,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6918 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6918 5 (fun x => (if x<2680 then (if x<1652 then (if x<192 then (if x<48 then 0 else (if x<136 then 1 else 0)) else (if x<1596 then (if x<1582 then 1 else 2) else (if x<1650 then 1 else 2))) else (if x<1740 then (if x<1686 then 0 else (if x<1738 then 2 else 2)) else (if x<2614 then (if x<1752 then 1 else 0) else (if x<2668 then 0 else 3)))) else (if x<3130 then (if x<2716 then (if x<2702 then 4 else (if x<2714 then 2 else 0)) else (if x<2770 then (if x<2758 then 3 else 1) else (if x<2772 then 2 else 4))) else (if x<3222 then (if x<3174 then (if x<3132 then 1 else 3) else (if x<3188 then 0 else 4)) else (if x<3276 then (if x<3274 then 3 else 0) else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6919 : Finset ℕ := ([48,136,1582,1650,1652,1686,1738,1740,2680,2714,2716,2758,3130,3132,3174,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6919 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6919 4 (fun x => (if x<2680 then (if x<1652 then (if x<1582 then (if x<136 then 0 else 0) else (if x<1650 then 1 else 0)) else (if x<1738 then (if x<1686 then 1 else 1) else (if x<1740 then 0 else 1))) else (if x<3130 then (if x<2716 then (if x<2714 then 2 else 2) else (if x<2758 then 3 else 3)) else (if x<3174 then (if x<3132 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6920 : Finset ℕ := ([36,48,136,192,1582,1596,1650,1652,1686,1738,1740,1752,2614,2668,2680,2702,2714,2716,2758,2770,2772,3118,3130,3132,3174,3188,3222,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6920 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6920 3118 4
  · have he : independentCachedBranchMembers6920.erase 3118=independentCachedBranchMembers6918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6918
  · have he : independentCachedBranchMembers6920.filter (independentCachedEdge 3118)=independentCachedBranchMembers6919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6919
def independentCachedBranchMembers6921 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6921 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6921 2710 5
  · have he : independentCachedBranchMembers6921.erase 2710=independentCachedBranchMembers6917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6917
  · have he : independentCachedBranchMembers6921.filter (independentCachedEdge 2710)=independentCachedBranchMembers6920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6920
def independentCachedBranchMembers6922 : Finset ℕ := ([48,130,136,222,1582,1650,1652,1686,1690,1734,1738,1740,2614,2618,2620,2662,2668,2702,2770,2772,2776,3118,3188,3192,3222,3226,3228,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6922 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6922 5 (fun x => (if x<2662 then (if x<1686 then (if x<222 then (if x<130 then 0 else (if x<136 then 0 else 1)) else (if x<1650 then (if x<1582 then 1 else 2) else (if x<1652 then 2 else 0))) else (if x<1740 then (if x<1734 then (if x<1690 then 2 else 1) else (if x<1738 then 0 else 2)) else (if x<2618 then (if x<2614 then 1 else 2) else (if x<2620 then 3 else 0)))) else (if x<3188 then (if x<2770 then (if x<2668 then 3 else (if x<2702 then 4 else 0)) else (if x<2776 then (if x<2772 then 2 else 4) else (if x<3118 then 1 else 3))) else (if x<3228 then (if x<3222 then (if x<3192 then 4 else 0) else (if x<3226 then 4 else 3)) else (if x<3274 then (if x<3270 then 1 else 3) else (if x<3276 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6923 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6923 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6923 2606 5
  · have he : independentCachedBranchMembers6923.erase 2606=independentCachedBranchMembers6921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6921
  · have he : independentCachedBranchMembers6923.filter (independentCachedEdge 2606)=independentCachedBranchMembers6922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6922
def independentCachedBranchMembers6924 : Finset ℕ := ([136,192,222,1590,1642,1652,1678,1734,1740,1746,1752,2614,2620,2702,2714,2758,2776,3118,3130,3174,3192,3222,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6924 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6924 5 (fun x => (if x<2620 then (if x<1678 then (if x<1590 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1642 then 1 else (if x<1652 then 2 else 2))) else (if x<1746 then (if x<1734 then 0 else (if x<1740 then 1 else 2)) else (if x<1752 then 2 else (if x<2614 then 0 else 3)))) else (if x<3130 then (if x<2758 then (if x<2702 then 1 else (if x<2714 then 3 else 0)) else (if x<2776 then 4 else (if x<3118 then 4 else 3))) else (if x<3222 then (if x<3174 then 1 else (if x<3192 then 4 else 4)) else (if x<3228 then 3 else (if x<3274 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6925 : Finset ℕ := ([222,1642,1746,1752,2714,2776,3118,3174,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6925 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6925 4 (fun x => (if x<2776 then (if x<1746 then (if x<1642 then 0 else 1) else (if x<1752 then 0 else (if x<2714 then 1 else 0))) else (if x<3174 then (if x<3118 then 2 else 1) else (if x<3222 then 2 else (if x<3228 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6926 : Finset ℕ := ([48,136,192,222,1590,1642,1652,1678,1734,1740,1746,1752,2614,2620,2702,2714,2758,2776,3118,3130,3174,3192,3222,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6926 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6926 48 4
  · have he : independentCachedBranchMembers6926.erase 48=independentCachedBranchMembers6924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6924
  · have he : independentCachedBranchMembers6926.filter (independentCachedEdge 48)=independentCachedBranchMembers6925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6925
def independentCachedBranchMembers6927 : Finset ℕ := ([48,192,1652,1678,1746,1752,2614,2620,2714,2758,3118,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6927 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6927 4 (fun x => (if x<2614 then (if x<1678 then (if x<192 then 0 else (if x<1652 then 0 else 1)) else (if x<1746 then 2 else (if x<1752 then 1 else 2))) else (if x<2758 then (if x<2620 then 0 else (if x<2714 then 1 else 1)) else (if x<3118 then 0 else (if x<3192 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6928 : Finset ℕ := ([48,136,192,222,1590,1642,1652,1678,1690,1734,1740,1746,1752,2614,2620,2702,2714,2758,2776,3118,3130,3174,3192,3222,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6928 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6928 1690 4
  · have he : independentCachedBranchMembers6928.erase 1690=independentCachedBranchMembers6926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6926
  · have he : independentCachedBranchMembers6928.filter (independentCachedEdge 1690)=independentCachedBranchMembers6927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6927
def independentCachedBranchMembers6929 : Finset ℕ := ([136,222,1590,1652,1734,1746,2620,2702,2714,2776,3174,3222] : List ℕ).toFinset
theorem independentCachedBranchBound6929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6929 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6929 4 (fun x => (if x<2620 then (if x<1652 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1734 then 2 else (if x<1746 then 1 else 2))) else (if x<2776 then (if x<2702 then 1 else (if x<2714 then 0 else 2)) else (if x<3174 then 0 else (if x<3222 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6930 : Finset ℕ := ([48,136,192,222,1590,1596,1642,1652,1678,1690,1734,1740,1746,1752,2614,2620,2702,2714,2758,2776,3118,3130,3174,3192,3222,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6930 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6930 1596 4
  · have he : independentCachedBranchMembers6930.erase 1596=independentCachedBranchMembers6928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6928
  · have he : independentCachedBranchMembers6930.filter (independentCachedEdge 1596)=independentCachedBranchMembers6929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6929
def independentCachedBranchMembers6931 : Finset ℕ := ([136,192,1590,1642,1740,1752,2614,2776,3118,3130,3174,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6931 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6931 4 (fun x => (if x<2614 then (if x<1642 then (if x<192 then 0 else (if x<1590 then 1 else 0)) else (if x<1740 then 2 else (if x<1752 then 1 else 2))) else (if x<3130 then (if x<2776 then 1 else (if x<3118 then 0 else 2)) else (if x<3174 then 1 else (if x<3228 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6932 : Finset ℕ := ([48,130,136,192,222,1590,1596,1642,1652,1678,1690,1734,1740,1746,1752,2614,2620,2702,2714,2758,2776,3118,3130,3174,3192,3222,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6932 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6932 130 4
  · have he : independentCachedBranchMembers6932.erase 130=independentCachedBranchMembers6930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6930
  · have he : independentCachedBranchMembers6932.filter (independentCachedEdge 130)=independentCachedBranchMembers6931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6931
def independentCachedBranchMembers6933 : Finset ℕ := ([48,222,1642,1678,1734,1740,2702,2758,3130,3192,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6933 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6933 4 (fun x => (if x<2702 then (if x<1678 then (if x<222 then 0 else (if x<1642 then 1 else 2)) else (if x<1734 then 0 else (if x<1740 then 1 else 2))) else (if x<3192 then (if x<2758 then 1 else (if x<3130 then 0 else 2)) else (if x<3222 then 0 else (if x<3228 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6934 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1642,1652,1678,1690,1734,1740,1746,1752,2614,2620,2702,2714,2758,2776,3118,3130,3174,3192,3222,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6934 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6934 36 4
  · have he : independentCachedBranchMembers6934.erase 36=independentCachedBranchMembers6932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6932
  · have he : independentCachedBranchMembers6934.filter (independentCachedEdge 36)=independentCachedBranchMembers6933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6933
def independentCachedBranchMembers6935 : Finset ℕ := ([36,48,130,136,1590,1596,1678,1690,2614,2620,2702,2714,3118,3130,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6935 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6935 4 (fun x => (if x<2614 then (if x<1590 then (if x<130 then (if x<48 then 0 else 1) else (if x<136 then 0 else 1)) else (if x<1678 then (if x<1596 then 1 else 0) else (if x<1690 then 1 else 0))) else (if x<3118 then (if x<2702 then (if x<2620 then 2 else 3) else (if x<2714 then 2 else 3)) else (if x<3222 then (if x<3130 then 2 else 3) else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6936 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1642,1652,1678,1690,1734,1740,1746,1752,2614,2620,2702,2714,2758,2776,3118,3130,3174,3192,3222,3228,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound6936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6936 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6936 3284 4
  · have he : independentCachedBranchMembers6936.erase 3284=independentCachedBranchMembers6934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6934
  · have he : independentCachedBranchMembers6936.filter (independentCachedEdge 3284)=independentCachedBranchMembers6935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6935
def independentCachedBranchMembers6937 : Finset ℕ := ([48,136,1590,1642,1652,1678,1740,1746,2620,2714,2758,2776,3130,3174,3192,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6937 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6937 4 (fun x => (if x<2620 then (if x<1652 then (if x<1590 then (if x<136 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1740 then (if x<1678 then 1 else 0) else (if x<1746 then 1 else 1))) else (if x<3130 then (if x<2758 then (if x<2714 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3192 then (if x<3174 then 2 else 3) else (if x<3228 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6938 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1642,1652,1678,1690,1734,1740,1746,1752,2614,2620,2702,2714,2758,2770,2776,3118,3130,3174,3192,3222,3228,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound6938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6938 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6938 2770 4
  · have he : independentCachedBranchMembers6938.erase 2770=independentCachedBranchMembers6936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6936
  · have he : independentCachedBranchMembers6938.filter (independentCachedEdge 2770)=independentCachedBranchMembers6937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6937
def independentCachedBranchMembers6939 : Finset ℕ := ([36,130,1596,1642,1652,1690,1740,1746,2614,2702,2758,2776,3118,3174,3192,3222] : List ℕ).toFinset
theorem independentCachedBranchBound6939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6939 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6939 4 (fun x => (if x<2614 then (if x<1652 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1740 then (if x<1690 then 1 else 0) else (if x<1746 then 1 else 1))) else (if x<3118 then (if x<2758 then (if x<2702 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3192 then (if x<3174 then 2 else 3) else (if x<3222 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6940 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1642,1652,1678,1690,1734,1740,1746,1752,2614,2620,2702,2714,2758,2764,2770,2776,3118,3130,3174,3192,3222,3228,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound6940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6940 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6940 2764 4
  · have he : independentCachedBranchMembers6940.erase 2764=independentCachedBranchMembers6938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6938
  · have he : independentCachedBranchMembers6940.filter (independentCachedEdge 2764)=independentCachedBranchMembers6939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6939
def independentCachedBranchMembers6941 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6941 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6941 3178 5
  · have he : independentCachedBranchMembers6941.erase 3178=independentCachedBranchMembers6923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6923
  · have he : independentCachedBranchMembers6941.filter (independentCachedEdge 3178)=independentCachedBranchMembers6940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6940
def independentCachedBranchMembers6942 : Finset ℕ := ([40,144,192,222,1582,1644,1650,1686,1734,1738,1748,1752,2614,2618,2662,2680,2702,2716,2770,3118,3132,3222,3226,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6942 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6942 5 (fun x => (if x<2614 then (if x<1650 then (if x<222 then (if x<144 then 0 else (if x<192 then 0 else 1)) else (if x<1582 then 1 else (if x<1644 then 0 else 2))) else (if x<1738 then (if x<1686 then 2 else (if x<1734 then 0 else 1)) else (if x<1748 then 2 else (if x<1752 then 2 else 1)))) else (if x<2770 then (if x<2680 then (if x<2618 then 3 else (if x<2662 then 4 else 4)) else (if x<2702 then 3 else (if x<2716 then 4 else 3))) else (if x<3222 then (if x<3118 then 0 else (if x<3132 then 4 else 3)) else (if x<3270 then (if x<3226 then 3 else 4) else (if x<3288 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6943 : Finset ℕ := ([40,192,1644,1686,1738,1752,2614,2680,3118,3132,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound6943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6943 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6943 4 (fun x => (if x<2614 then (if x<1686 then (if x<192 then 0 else (if x<1644 then 0 else 1)) else (if x<1738 then 2 else (if x<1752 then 1 else 2))) else (if x<3132 then (if x<2680 then 2 else (if x<3118 then 2 else 0)) else (if x<3226 then 1 else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
