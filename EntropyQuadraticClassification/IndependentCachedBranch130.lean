/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch129
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6944 : Finset ℕ := ([40,144,192,222,1582,1644,1650,1686,1690,1734,1738,1748,1752,2614,2618,2662,2680,2702,2716,2770,3118,3132,3222,3226,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6944 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6944 1690 4
  · have he : independentCachedBranchMembers6944.erase 1690=independentCachedBranchMembers6942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6942
  · have he : independentCachedBranchMembers6944.filter (independentCachedEdge 1690)=independentCachedBranchMembers6943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6943
def independentCachedBranchMembers6945 : Finset ℕ := ([144,222,1582,1644,1734,1738,2662,2702,3132,3222,3226,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6945 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6945 4 (fun x => (if x<2662 then (if x<1644 then (if x<222 then 0 else (if x<1582 then 0 else 1)) else (if x<1734 then 2 else (if x<1738 then 1 else 2))) else (if x<3222 then (if x<2702 then 1 else (if x<3132 then 1 else 2)) else (if x<3226 then 0 else (if x<3288 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6946 : Finset ℕ := ([40,144,192,222,1582,1596,1644,1650,1686,1690,1734,1738,1748,1752,2614,2618,2662,2680,2702,2716,2770,3118,3132,3222,3226,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6946 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6946 1596 4
  · have he : independentCachedBranchMembers6946.erase 1596=independentCachedBranchMembers6944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6944
  · have he : independentCachedBranchMembers6946.filter (independentCachedEdge 1596)=independentCachedBranchMembers6945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6945
def independentCachedBranchMembers6947 : Finset ℕ := ([144,192,1582,1650,1748,1752,2614,2618,2662,2716,3118,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6947 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6947 4 (fun x => (if x<2614 then (if x<1650 then (if x<192 then 0 else (if x<1582 then 1 else 0)) else (if x<1748 then 2 else (if x<1752 then 1 else 2))) else (if x<2716 then (if x<2618 then 2 else (if x<2662 then 1 else 0)) else (if x<3118 then 2 else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6948 : Finset ℕ := ([40,130,144,192,222,1582,1596,1644,1650,1686,1690,1734,1738,1748,1752,2614,2618,2662,2680,2702,2716,2770,3118,3132,3222,3226,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6948 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6948 130 4
  · have he : independentCachedBranchMembers6948.erase 130=independentCachedBranchMembers6946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6946
  · have he : independentCachedBranchMembers6948.filter (independentCachedEdge 130)=independentCachedBranchMembers6947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6947
def independentCachedBranchMembers6949 : Finset ℕ := ([40,222,1650,1686,1734,1748,2618,2680,2702,2716,3222,3270] : List ℕ).toFinset
theorem independentCachedBranchBound6949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6949 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6949 4 (fun x => (if x<2618 then (if x<1686 then (if x<222 then 0 else (if x<1650 then 1 else 2)) else (if x<1734 then 0 else (if x<1748 then 1 else 2))) else (if x<2716 then (if x<2680 then 2 else (if x<2702 then 0 else 1)) else (if x<3222 then 2 else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6950 : Finset ℕ := ([36,40,130,144,192,222,1582,1596,1644,1650,1686,1690,1734,1738,1748,1752,2614,2618,2662,2680,2702,2716,2770,3118,3132,3222,3226,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6950 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6950 36 4
  · have he : independentCachedBranchMembers6950.erase 36=independentCachedBranchMembers6948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6948
  · have he : independentCachedBranchMembers6950.filter (independentCachedEdge 36)=independentCachedBranchMembers6949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6949
def independentCachedBranchMembers6951 : Finset ℕ := ([36,130,1596,1644,1650,1690,1738,1748,2614,2662,2680,2702,3118,3222,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6951 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6951 4 (fun x => (if x<2614 then (if x<1650 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1738 then (if x<1690 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<3118 then (if x<2680 then (if x<2662 then 2 else 3) else (if x<2702 then 2 else 3)) else (if x<3270 then (if x<3222 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6952 : Finset ℕ := ([36,40,130,144,192,222,1582,1596,1644,1650,1686,1690,1734,1738,1748,1752,2614,2618,2662,2680,2702,2716,2770,3118,3132,3222,3226,3270,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6952 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6952 3284 4
  · have he : independentCachedBranchMembers6952.erase 3284=independentCachedBranchMembers6950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6950
  · have he : independentCachedBranchMembers6952.filter (independentCachedEdge 3284)=independentCachedBranchMembers6951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6951
def independentCachedBranchMembers6953 : Finset ℕ := ([40,144,1582,1644,1650,1686,1738,1748,2618,2662,2680,2716,3132,3226,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6953 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6953 4 (fun x => (if x<2618 then (if x<1650 then (if x<1582 then (if x<144 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1738 then (if x<1686 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<3132 then (if x<2680 then (if x<2662 then 2 else 2) else (if x<2716 then 3 else 3)) else (if x<3270 then (if x<3226 then 3 else 2) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6954 : Finset ℕ := ([36,40,130,144,192,222,1582,1596,1644,1650,1686,1690,1734,1738,1748,1752,2614,2618,2662,2680,2702,2716,2770,3118,3132,3222,3226,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6954 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6954 3274 4
  · have he : independentCachedBranchMembers6954.erase 3274=independentCachedBranchMembers6952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6952
  · have he : independentCachedBranchMembers6954.filter (independentCachedEdge 3274)=independentCachedBranchMembers6953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6953
def independentCachedBranchMembers6955 : Finset ℕ := ([36,40,130,144,1582,1596,1686,1690,2614,2618,2702,2716,3118,3132,3222,3226] : List ℕ).toFinset
theorem independentCachedBranchBound6955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6955 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6955 4 (fun x => (if x<2614 then (if x<1582 then (if x<130 then (if x<40 then 0 else 1) else (if x<144 then 0 else 1)) else (if x<1686 then (if x<1596 then 1 else 0) else (if x<1690 then 1 else 0))) else (if x<3118 then (if x<2702 then (if x<2618 then 2 else 3) else (if x<2716 then 2 else 3)) else (if x<3222 then (if x<3132 then 2 else 3) else (if x<3226 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6956 : Finset ℕ := ([36,40,130,144,192,222,1582,1596,1644,1650,1686,1690,1734,1738,1748,1752,2614,2618,2662,2680,2702,2716,2764,2770,3118,3132,3222,3226,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6956 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6956 2764 4
  · have he : independentCachedBranchMembers6956.erase 2764=independentCachedBranchMembers6954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6954
  · have he : independentCachedBranchMembers6956.filter (independentCachedEdge 2764)=independentCachedBranchMembers6955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6955
def independentCachedBranchMembers6957 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2674,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6957 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6957 2674 5
  · have he : independentCachedBranchMembers6957.erase 2674=independentCachedBranchMembers6941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6941
  · have he : independentCachedBranchMembers6957.filter (independentCachedEdge 2674)=independentCachedBranchMembers6956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6956
def independentCachedBranchMembers6958 : Finset ℕ := ([40,48,130,192,1596,1642,1650,1678,1686,1690,1740,1748,1752,2614,2618,2668,2680,2716,2758,2762,2770,3118,3130,3188,3192,3228,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6958 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6958 5 (fun x => (if x<2618 then (if x<1678 then (if x<192 then (if x<48 then 0 else (if x<130 then 1 else 0)) else (if x<1642 then (if x<1596 then 1 else 0) else (if x<1650 then 2 else 3))) else (if x<1740 then (if x<1686 then 2 else (if x<1690 then 0 else 3)) else (if x<1752 then (if x<1748 then 1 else 3) else (if x<2614 then 2 else 1)))) else (if x<3118 then (if x<2716 then (if x<2668 then 3 else (if x<2680 then 0 else 2)) else (if x<2762 then (if x<2758 then 2 else 0) else (if x<2770 then 2 else 3))) else (if x<3228 then (if x<3188 then (if x<3130 then 4 else 1) else (if x<3192 then 4 else 0)) else (if x<3274 then (if x<3270 then 4 else 4) else (if x<3282 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6959 : Finset ℕ := ([130,1642,1678,1690,1748,2614,2668,2680,2716,2758,2770,3118,3130,3188,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6959 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6959 4 (fun x => (if x<2680 then (if x<1690 then (if x<1642 then 0 else (if x<1678 then 1 else 0)) else (if x<2614 then (if x<1748 then 1 else 2) else (if x<2668 then 3 else 1))) else (if x<3118 then (if x<2758 then (if x<2716 then 0 else 1) else (if x<2770 then 2 else 3)) else (if x<3188 then (if x<3130 then 3 else 2) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6960 : Finset ℕ := ([1678,1690,2614,2716,3188,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6960 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6960 3 (fun x => (if x<2716 then (if x<1690 then 0 else (if x<2614 then 1 else 2)) else (if x<3188 then 0 else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6961 : Finset ℕ := ([40,130,1642,1678,1690,1748,2614,2668,2680,2716,2758,2770,3118,3130,3188,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6961 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6961 40 3
  · have he : independentCachedBranchMembers6961.erase 40=independentCachedBranchMembers6959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6959
  · have he : independentCachedBranchMembers6961.filter (independentCachedEdge 40)=independentCachedBranchMembers6960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6960
def independentCachedBranchMembers6962 : Finset ℕ := ([40,48,130,192,1596,1642,1650,1678,1686,1690,1740,1748,1752,2614,2618,2668,2680,2716,2758,2762,2770,3118,3126,3130,3188,3192,3228,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6962 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6962 3126 4
  · have he : independentCachedBranchMembers6962.erase 3126=independentCachedBranchMembers6958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6958
  · have he : independentCachedBranchMembers6962.filter (independentCachedEdge 3126)=independentCachedBranchMembers6961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6961
def independentCachedBranchMembers6963 : Finset ℕ := ([48,130,1650,1686,1690,1740,2614,2618,2668,2770,3118,3188,3192,3228,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6963 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6963 4 (fun x => (if x<2668 then (if x<1690 then (if x<1650 then (if x<130 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2614 then (if x<1740 then 2 else 2) else (if x<2618 then 1 else 2))) else (if x<3192 then (if x<3118 then (if x<2770 then 2 else 1) else (if x<3188 then 3 else 0)) else (if x<3270 then (if x<3228 then 3 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6964 : Finset ℕ := ([40,48,130,192,1596,1642,1650,1678,1686,1690,1740,1748,1752,2606,2614,2618,2668,2680,2716,2758,2762,2770,3118,3126,3130,3188,3192,3228,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6964 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6964 2606 4
  · have he : independentCachedBranchMembers6964.erase 2606=independentCachedBranchMembers6962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6962
  · have he : independentCachedBranchMembers6964.filter (independentCachedEdge 2606)=independentCachedBranchMembers6963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6963
def independentCachedBranchMembers6965 : Finset ℕ := ([40,48,1642,1650,1678,1686,1740,1748,2618,2680,2716,2758,3130,3192,3228,3270] : List ℕ).toFinset
theorem independentCachedBranchBound6965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6965 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6965 4 (fun x => (if x<2618 then (if x<1678 then (if x<1642 then (if x<48 then 0 else 1) else (if x<1650 then 0 else 1)) else (if x<1740 then (if x<1686 then 2 else 3) else (if x<1748 then 3 else 2))) else (if x<3130 then (if x<2716 then (if x<2680 then 0 else 1) else (if x<2758 then 2 else 2)) else (if x<3228 then (if x<3192 then 1 else 0) else (if x<3270 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6966 : Finset ℕ := ([36,40,48,130,192,1596,1642,1650,1678,1686,1690,1740,1748,1752,2606,2614,2618,2668,2680,2716,2758,2762,2770,3118,3126,3130,3188,3192,3228,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6966 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6966 36 4
  · have he : independentCachedBranchMembers6966.erase 36=independentCachedBranchMembers6964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6964
  · have he : independentCachedBranchMembers6966.filter (independentCachedEdge 36)=independentCachedBranchMembers6965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6965
def independentCachedBranchMembers6967 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1692,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2674,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6967 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6967 1692 5
  · have he : independentCachedBranchMembers6967.erase 1692=independentCachedBranchMembers6957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6957
  · have he : independentCachedBranchMembers6967.filter (independentCachedEdge 1692)=independentCachedBranchMembers6966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6966
def independentCachedBranchMembers6968 : Finset ℕ := ([144,222,1582,1596,1642,1650,1690,1734,1740,1748,2618,2662,2668,2702,2716,2762,2770,2776,3130,3174,3188,3222,3228,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6968 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6968 5 (fun x => (if x<2702 then (if x<1690 then (if x<1596 then (if x<222 then 0 else (if x<1582 then 0 else 1)) else (if x<1642 then 2 else (if x<1650 then 2 else 1))) else (if x<1748 then (if x<1734 then 0 else (if x<1740 then 1 else 2)) else (if x<2662 then (if x<2618 then 0 else 1) else (if x<2668 then 1 else 2)))) else (if x<3174 then (if x<2770 then (if x<2716 then 1 else (if x<2762 then 0 else 2)) else (if x<2776 then 0 else (if x<3130 then 3 else 4))) else (if x<3228 then (if x<3188 then 3 else (if x<3222 then 4 else 0)) else (if x<3282 then (if x<3274 then 4 else 3) else (if x<3288 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6969 : Finset ℕ := ([144,222,1582,1596,1650,1740,2668,2702,2716,2770,3228,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6969 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6969 4 (fun x => (if x<2668 then (if x<1596 then (if x<222 then 0 else (if x<1582 then 0 else 1)) else (if x<1650 then 2 else (if x<1740 then 1 else 2))) else (if x<2770 then (if x<2702 then 2 else (if x<2716 then 1 else 0)) else (if x<3228 then 0 else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6970 : Finset ℕ := ([144,222,1582,1590,1596,1642,1650,1690,1734,1740,1748,2618,2662,2668,2702,2716,2762,2770,2776,3130,3174,3188,3222,3228,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6970 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6970 1590 4
  · have he : independentCachedBranchMembers6970.erase 1590=independentCachedBranchMembers6968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6968
  · have he : independentCachedBranchMembers6970.filter (independentCachedEdge 1590)=independentCachedBranchMembers6969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6969
def independentCachedBranchMembers6971 : Finset ℕ := ([144,1582,1596,1642,1734,1748,2618,2668,2770,3130,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6971 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6971 4 (fun x => (if x<2618 then (if x<1642 then (if x<1582 then 0 else (if x<1596 then 0 else 1)) else (if x<1734 then 1 else (if x<1748 then 2 else 3))) else (if x<3130 then (if x<2668 then 1 else (if x<2770 then 0 else 2)) else (if x<3222 then 3 else (if x<3282 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6972 : Finset ℕ := ([136,144,222,1582,1590,1596,1642,1650,1690,1734,1740,1748,2618,2662,2668,2702,2716,2762,2770,2776,3130,3174,3188,3222,3228,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6972 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6972 136 4
  · have he : independentCachedBranchMembers6972.erase 136=independentCachedBranchMembers6970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6970
  · have he : independentCachedBranchMembers6972.filter (independentCachedEdge 136)=independentCachedBranchMembers6971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6971
def independentCachedBranchMembers6973 : Finset ℕ := ([222,1642,1650,1734,1740,1748,2618,2702,2716,3130,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6973 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6973 4 (fun x => (if x<2618 then (if x<1734 then (if x<1642 then 0 else (if x<1650 then 1 else 2)) else (if x<1740 then 0 else (if x<1748 then 1 else 2))) else (if x<3130 then (if x<2702 then 1 else (if x<2716 then 0 else 1)) else (if x<3222 then 2 else (if x<3228 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6974 : Finset ℕ := ([36,136,144,222,1582,1590,1596,1642,1650,1690,1734,1740,1748,2618,2662,2668,2702,2716,2762,2770,2776,3130,3174,3188,3222,3228,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6974 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6974 36 4
  · have he : independentCachedBranchMembers6974.erase 36=independentCachedBranchMembers6972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6972
  · have he : independentCachedBranchMembers6974.filter (independentCachedEdge 36)=independentCachedBranchMembers6973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6973
def independentCachedBranchMembers6975 : Finset ℕ := ([144,1590,1596,1642,1748,2618,2662,2668,2702,2770,2776,3188,3222,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6975 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6975 4 (fun x => (if x<2668 then (if x<1642 then (if x<1590 then 0 else (if x<1596 then 1 else 2)) else (if x<2618 then (if x<1748 then 0 else 1) else (if x<2662 then 1 else 0))) else (if x<3188 then (if x<2770 then (if x<2702 then 2 else 3) else (if x<2776 then 3 else 1)) else (if x<3228 then (if x<3222 then 2 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
