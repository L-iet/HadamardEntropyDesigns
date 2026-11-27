/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch130
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6976 : Finset ℕ := ([1642,1748,2618,2702,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6976 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6976 3 (fun x => (if x<2702 then (if x<1748 then 0 else (if x<2618 then 1 else 0)) else (if x<3222 then 2 else (if x<3228 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6977 : Finset ℕ := ([36,144,1590,1596,1642,1748,2618,2662,2668,2702,2770,2776,3188,3222,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6977 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6977 36 3
  · have he : independentCachedBranchMembers6977.erase 36=independentCachedBranchMembers6975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6975
  · have he : independentCachedBranchMembers6977.filter (independentCachedEdge 36)=independentCachedBranchMembers6976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6976
def independentCachedBranchMembers6978 : Finset ℕ := ([36,136,144,222,1582,1590,1596,1642,1650,1690,1734,1740,1748,2618,2662,2668,2702,2716,2762,2770,2776,3130,3174,3188,3214,3222,3228,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6978 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6978 3214 4
  · have he : independentCachedBranchMembers6978.erase 3214=independentCachedBranchMembers6974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6974
  · have he : independentCachedBranchMembers6978.filter (independentCachedEdge 3214)=independentCachedBranchMembers6977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6977
def independentCachedBranchMembers6979 : Finset ℕ := ([36,136,1582,1596,1650,1740,2668,2702,2716,2770,3130,3174,3188,3222,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6979 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6979 4 (fun x => (if x<2716 then (if x<1650 then (if x<1582 then (if x<136 then 0 else 0) else (if x<1596 then 1 else 2)) else (if x<2668 then (if x<1740 then 1 else 2) else (if x<2702 then 2 else 1))) else (if x<3188 then (if x<3130 then (if x<2770 then 2 else 1) else (if x<3174 then 3 else 0)) else (if x<3274 then (if x<3222 then 3 else 3) else (if x<3288 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6980 : Finset ℕ := ([36,136,144,222,1582,1590,1596,1642,1650,1690,1734,1740,1748,2618,2662,2668,2702,2710,2716,2762,2770,2776,3130,3174,3188,3214,3222,3228,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6980 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6980 2710 4
  · have he : independentCachedBranchMembers6980.erase 2710=independentCachedBranchMembers6978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6978
  · have he : independentCachedBranchMembers6980.filter (independentCachedEdge 2710)=independentCachedBranchMembers6979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6979
def independentCachedBranchMembers6981 : Finset ℕ := ([136,144,1582,1590,1642,1650,1740,1748,2618,2662,2716,2776,3130,3174,3228,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6981 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6981 4 (fun x => (if x<2618 then (if x<1642 then (if x<1582 then (if x<144 then 0 else 1) else (if x<1590 then 1 else 0)) else (if x<1740 then (if x<1650 then 2 else 3) else (if x<1748 then 2 else 3))) else (if x<3130 then (if x<2716 then (if x<2662 then 2 else 0) else (if x<2776 then 2 else 1)) else (if x<3228 then (if x<3174 then 3 else 1) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6982 : Finset ℕ := ([36,130,136,144,222,1582,1590,1596,1642,1650,1690,1734,1740,1748,2618,2662,2668,2702,2710,2716,2762,2770,2776,3130,3174,3188,3214,3222,3228,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6982 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6982 130 4
  · have he : independentCachedBranchMembers6982.erase 130=independentCachedBranchMembers6980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6980
  · have he : independentCachedBranchMembers6982.filter (independentCachedEdge 130)=independentCachedBranchMembers6981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6981
def independentCachedBranchMembers6983 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1594,1596,1642,1644,1650,1652,1678,1686,1690,1692,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2674,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6983 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6983 1594 5
  · have he : independentCachedBranchMembers6983.erase 1594=independentCachedBranchMembers6967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6967
  · have he : independentCachedBranchMembers6983.filter (independentCachedEdge 1594)=independentCachedBranchMembers6982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6982
def independentCachedBranchMembers6984 : Finset ℕ := ([36,136,144,192,1582,1590,1652,1690,1738,1746,1752,2614,2620,2662,2668,2714,2762,2770,2776,3118,3132,3174,3188,3226,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6984 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6984 5 (fun x => (if x<2662 then (if x<1652 then (if x<192 then (if x<136 then 0 else (if x<144 then 0 else 1)) else (if x<1582 then 2 else (if x<1590 then 1 else 0))) else (if x<1746 then (if x<1690 then 3 else (if x<1738 then 0 else 2)) else (if x<2614 then (if x<1752 then 3 else 4) else (if x<2620 then 2 else 3)))) else (if x<3132 then (if x<2762 then (if x<2668 then 0 else (if x<2714 then 1 else 3)) else (if x<2776 then (if x<2770 then 0 else 2) else (if x<3118 then 1 else 4))) else (if x<3226 then (if x<3174 then 2 else (if x<3188 then 1 else 0)) else (if x<3282 then (if x<3274 then 4 else 3) else (if x<3288 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6985 : Finset ℕ := ([136,192,1582,1652,1690,1746,2614,2668,2762,2776,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6985 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6985 4 (fun x => (if x<2614 then (if x<1652 then (if x<192 then 0 else (if x<1582 then 1 else 1)) else (if x<1690 then 0 else (if x<1746 then 2 else 3))) else (if x<2776 then (if x<2668 then 0 else (if x<2762 then 2 else 2)) else (if x<3274 then 1 else (if x<3288 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6986 : Finset ℕ := ([36,136,144,192,1582,1590,1644,1652,1690,1738,1746,1752,2614,2620,2662,2668,2714,2762,2770,2776,3118,3132,3174,3188,3226,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6986 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6986 1644 4
  · have he : independentCachedBranchMembers6986.erase 1644=independentCachedBranchMembers6984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6984
  · have he : independentCachedBranchMembers6986.filter (independentCachedEdge 1644)=independentCachedBranchMembers6985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6985
def independentCachedBranchMembers6987 : Finset ℕ := ([136,144,192,1582,1590,1752,2614,2662,2776,3118,3174,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6987 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6987 4 (fun x => (if x<2614 then (if x<1582 then (if x<144 then 0 else (if x<192 then 1 else 2)) else (if x<1590 then 1 else (if x<1752 then 0 else 2))) else (if x<3118 then (if x<2662 then 2 else (if x<2776 then 0 else 1)) else (if x<3174 then 2 else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6988 : Finset ℕ := ([36,130,136,144,192,1582,1590,1644,1652,1690,1738,1746,1752,2614,2620,2662,2668,2714,2762,2770,2776,3118,3132,3174,3188,3226,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6988 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6988 130 4
  · have he : independentCachedBranchMembers6988.erase 130=independentCachedBranchMembers6986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6986
  · have he : independentCachedBranchMembers6988.filter (independentCachedEdge 130)=independentCachedBranchMembers6987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6987
def independentCachedBranchMembers6989 : Finset ℕ := ([130,144,1590,1644,1690,1746,2614,2668,2714,2770,3118,3132,3174,3188,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6989 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6989 4 (fun x => (if x<2714 then (if x<1690 then (if x<1590 then (if x<144 then 0 else 1) else (if x<1644 then 2 else 0)) else (if x<2614 then (if x<1746 then 1 else 2) else (if x<2668 then 3 else 1))) else (if x<3174 then (if x<3118 then (if x<2770 then 0 else 3) else (if x<3132 then 2 else 3)) else (if x<3274 then (if x<3188 then 1 else 0) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6990 : Finset ℕ := ([36,130,136,144,192,1582,1590,1644,1652,1690,1738,1746,1752,2614,2620,2662,2668,2714,2762,2770,2776,3118,3126,3132,3174,3188,3226,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6990 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6990 3126 4
  · have he : independentCachedBranchMembers6990.erase 3126=independentCachedBranchMembers6988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6988
  · have he : independentCachedBranchMembers6990.filter (independentCachedEdge 3126)=independentCachedBranchMembers6989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6989
def independentCachedBranchMembers6991 : Finset ℕ := ([130,136,1582,1652,1690,1738,2614,2620,2662,2668,2770,2776,3118,3188,3226,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6991 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6991 4 (fun x => (if x<2662 then (if x<1690 then (if x<1582 then (if x<136 then 0 else 1) else (if x<1652 then 2 else 0)) else (if x<2614 then (if x<1738 then 1 else 2) else (if x<2620 then 2 else 0))) else (if x<3118 then (if x<2770 then (if x<2668 then 1 else 3) else (if x<2776 then 2 else 3)) else (if x<3226 then (if x<3188 then 3 else 1) else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6992 : Finset ℕ := ([36,130,136,144,192,1582,1590,1644,1652,1690,1738,1746,1752,2606,2614,2620,2662,2668,2714,2762,2770,2776,3118,3126,3132,3174,3188,3226,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6992 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6992 2606 4
  · have he : independentCachedBranchMembers6992.erase 2606=independentCachedBranchMembers6990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6990
  · have he : independentCachedBranchMembers6992.filter (independentCachedEdge 2606)=independentCachedBranchMembers6991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6991
def independentCachedBranchMembers6993 : Finset ℕ := ([136,144,1582,1590,1644,1652,1738,1746,2620,2662,2714,2776,3132,3174,3226,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6993 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6993 4 (fun x => (if x<2620 then (if x<1644 then (if x<1582 then (if x<144 then 0 else 1) else (if x<1590 then 1 else 0)) else (if x<1738 then (if x<1652 then 2 else 3) else (if x<1746 then 2 else 3))) else (if x<3132 then (if x<2714 then (if x<2662 then 2 else 0) else (if x<2776 then 2 else 1)) else (if x<3226 then (if x<3174 then 3 else 1) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6994 : Finset ℕ := ([36,130,136,144,192,1582,1590,1596,1644,1652,1690,1738,1746,1752,2606,2614,2620,2662,2668,2714,2762,2770,2776,3118,3126,3132,3174,3188,3226,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6994 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6994 1596 4
  · have he : independentCachedBranchMembers6994.erase 1596=independentCachedBranchMembers6992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6992
  · have he : independentCachedBranchMembers6994.filter (independentCachedEdge 1596)=independentCachedBranchMembers6993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6993
def independentCachedBranchMembers6995 : Finset ℕ := ([36,40,48,130,132,136,144,192,222,1582,1590,1594,1596,1642,1644,1650,1652,1678,1686,1690,1692,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2674,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6995 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6995 132 5
  · have he : independentCachedBranchMembers6995.erase 132=independentCachedBranchMembers6983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6983
  · have he : independentCachedBranchMembers6995.filter (independentCachedEdge 132)=independentCachedBranchMembers6994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6994
def independentCachedBranchMembers6996 : Finset ℕ := ([36,40,48,130,222,1596,1644,1652,1678,1686,1690,1734,1738,1746,2620,2668,2680,2702,2710,2714,2758,2762,2770,3132,3188,3192,3214,3222,3226,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6996 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6996 5 (fun x => (if x<2680 then (if x<1678 then (if x<222 then (if x<48 then (if x<40 then 0 else 1) else (if x<130 then 2 else 0)) else (if x<1644 then (if x<1596 then 3 else 0) else (if x<1652 then 1 else 2))) else (if x<1738 then (if x<1690 then (if x<1686 then 3 else 4) else (if x<1734 then 0 else 1)) else (if x<2620 then (if x<1746 then 4 else 3) else (if x<2668 then 1 else 0)))) else (if x<3188 then (if x<2758 then (if x<2710 then (if x<2702 then 2 else 4) else (if x<2714 then 1 else 3)) else (if x<2770 then (if x<2762 then 3 else 0) else (if x<3132 then 4 else 2))) else (if x<3226 then (if x<3214 then (if x<3192 then 0 else 1) else (if x<3222 then 2 else 3)) else (if x<3274 then (if x<3270 then 4 else 4) else (if x<3282 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6997 : Finset ℕ := ([34,36,40,48,130,132,136,144,192,222,1582,1590,1594,1596,1642,1644,1650,1652,1678,1686,1690,1692,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2674,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6997 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6997 34 5
  · have he : independentCachedBranchMembers6997.erase 34=independentCachedBranchMembers6995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6995
  · have he : independentCachedBranchMembers6997.filter (independentCachedEdge 34)=independentCachedBranchMembers6996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6996
def independentCachedBranchMembers6998 : Finset ℕ := ([144,192,222,1582,1644,1650,1686,1734,1738,1748,1752,2606,2620,2674,2710,2714,2758,2772,2776,3126,3130,3174,3178,3192,3214,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6998 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6998 5 (fun x => (if x<2710 then (if x<1734 then (if x<1582 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1650 then (if x<1644 then 1 else 2) else (if x<1686 then 2 else 0))) else (if x<1752 then (if x<1738 then 1 else (if x<1748 then 2 else 2)) else (if x<2620 then (if x<2606 then 0 else 3) else (if x<2674 then 1 else 3)))) else (if x<3174 then (if x<2772 then (if x<2714 then 3 else (if x<2758 then 0 else 4)) else (if x<3126 then (if x<2776 then 0 else 4) else (if x<3130 then 3 else 1))) else (if x<3214 then (if x<3178 then 4 else (if x<3192 then 2 else 4)) else (if x<3276 then (if x<3228 then 3 else 0) else (if x<3282 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6999 : Finset ℕ := ([222,1650,1738,1752,2674,2714,2776,3126,3174,3214,3228,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6999 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6999 4 (fun x => (if x<2776 then (if x<1752 then (if x<1650 then 0 else (if x<1738 then 1 else 0)) else (if x<2674 then 1 else (if x<2714 then 2 else 0))) else (if x<3214 then (if x<3126 then 2 else (if x<3174 then 1 else 2)) else (if x<3228 then 0 else (if x<3276 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7000 : Finset ℕ := ([40,144,192,222,1582,1644,1650,1686,1734,1738,1748,1752,2606,2620,2674,2710,2714,2758,2772,2776,3126,3130,3174,3178,3192,3214,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7000 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7000 40 4
  · have he : independentCachedBranchMembers7000.erase 40=independentCachedBranchMembers6998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6998
  · have he : independentCachedBranchMembers7000.filter (independentCachedEdge 40)=independentCachedBranchMembers6999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6999
def independentCachedBranchMembers7001 : Finset ℕ := ([40,144,192,222,1582,1686,1734,1752,2606,2710,2758,2776,3126,3174,3192,3214] : List ℕ).toFinset
theorem independentCachedBranchBound7001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7001 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7001 4 (fun x => (if x<2606 then (if x<1582 then (if x<192 then (if x<144 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1734 then (if x<1686 then 0 else 0) else (if x<1752 then 1 else 1))) else (if x<3126 then (if x<2758 then (if x<2710 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3192 then (if x<3174 then 2 else 3) else (if x<3214 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7002 : Finset ℕ := ([40,144,192,222,1582,1644,1650,1686,1734,1738,1748,1752,2606,2620,2674,2710,2714,2758,2772,2776,3126,3130,3174,3178,3188,3192,3214,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7002 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7002 3188 4
  · have he : independentCachedBranchMembers7002.erase 3188=independentCachedBranchMembers7000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7000
  · have he : independentCachedBranchMembers7002.filter (independentCachedEdge 3188)=independentCachedBranchMembers7001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7001
def independentCachedBranchMembers7003 : Finset ℕ := ([40,144,1582,1644,1650,1686,1738,1748,2620,2714,2758,2776,3130,3174,3192,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7003 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7003 4 (fun x => (if x<2620 then (if x<1650 then (if x<1582 then (if x<144 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1738 then (if x<1686 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<3130 then (if x<2758 then (if x<2714 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3192 then (if x<3174 then 2 else 3) else (if x<3228 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7004 : Finset ℕ := ([40,144,192,222,1582,1644,1650,1686,1734,1738,1748,1752,2606,2620,2674,2710,2714,2758,2762,2772,2776,3126,3130,3174,3178,3188,3192,3214,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7004 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7004 2762 4
  · have he : independentCachedBranchMembers7004.erase 2762=independentCachedBranchMembers7002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7002
  · have he : independentCachedBranchMembers7004.filter (independentCachedEdge 2762)=independentCachedBranchMembers7003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7003
def independentCachedBranchMembers7005 : Finset ℕ := ([192,222,1644,1650,1734,1738,1748,1752,2606,2620,2710,2714,3126,3130,3214,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7005 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7005 4 (fun x => (if x<2606 then (if x<1734 then (if x<1644 then (if x<222 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3126 then (if x<2710 then (if x<2620 then 2 else 3) else (if x<2714 then 2 else 3)) else (if x<3214 then (if x<3130 then 2 else 3) else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7006 : Finset ℕ := ([40,144,192,222,1582,1644,1650,1686,1734,1738,1748,1752,2606,2620,2668,2674,2710,2714,2758,2762,2772,2776,3126,3130,3174,3178,3188,3192,3214,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7006 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7006 2668 4
  · have he : independentCachedBranchMembers7006.erase 2668=independentCachedBranchMembers7004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7004
  · have he : independentCachedBranchMembers7006.filter (independentCachedEdge 2668)=independentCachedBranchMembers7005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7005
def independentCachedBranchMembers7007 : Finset ℕ := ([192,1644,1686,1738,1752,2606,2620,2674,2714,2758,2772,3126,3178,3192,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7007 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7007 4 (fun x => (if x<2674 then (if x<1738 then (if x<1644 then 0 else (if x<1686 then 1 else 2)) else (if x<2606 then (if x<1752 then 0 else 1) else (if x<2620 then 1 else 0))) else (if x<3126 then (if x<2758 then (if x<2714 then 3 else 1) else (if x<2772 then 2 else 3)) else (if x<3192 then (if x<3178 then 0 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
