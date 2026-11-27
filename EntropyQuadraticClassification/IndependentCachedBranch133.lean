/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch132
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7040 : Finset ℕ := ([34,48,132,136,192,222,1590,1594,1644,1650,1678,1692,1734,1738,1748,1752,2614,2618,2668,2674,2702,2716,2758,2762,2772,2776,3118,3132,3174,3178,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7040 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7040 34 4
  · have he : independentCachedBranchMembers7040.erase 34=independentCachedBranchMembers7038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7038
  · have he : independentCachedBranchMembers7040.filter (independentCachedEdge 34)=independentCachedBranchMembers7039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7039
def independentCachedBranchMembers7041 : Finset ℕ := ([34,36,40,48,130,132,136,144,192,222,1582,1590,1594,1596,1642,1644,1650,1652,1678,1686,1690,1692,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2674,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7041 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7041 3180 5
  · have he : independentCachedBranchMembers7041.erase 3180=independentCachedBranchMembers7019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7019
  · have he : independentCachedBranchMembers7041.filter (independentCachedEdge 3180)=independentCachedBranchMembers7040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7040
def independentCachedBranchMembers7042 : Finset ℕ := ([40,144,192,222,1582,1642,1652,1686,1734,1740,1746,1752,2614,2620,2662,2668,2674,2680,2702,2714,2762,2772,3118,3130,3178,3188,3222,3228,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7042 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7042 5 (fun x => (if x<2674 then (if x<1734 then (if x<1582 then (if x<192 then (if x<144 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1652 then (if x<1642 then 0 else 2) else (if x<1686 then 2 else 0))) else (if x<2614 then (if x<1746 then (if x<1740 then 1 else 2) else (if x<1752 then 2 else 1)) else (if x<2662 then (if x<2620 then 3 else 4) else (if x<2668 then 4 else 0)))) else (if x<3178 then (if x<2762 then (if x<2702 then (if x<2680 then 2 else 3) else (if x<2714 then 4 else 3)) else (if x<3118 then (if x<2772 then 1 else 0) else (if x<3130 then 4 else 3))) else (if x<3270 then (if x<3222 then (if x<3188 then 0 else 3) else (if x<3228 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 1) else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7043 : Finset ℕ := ([40,192,1642,1686,1740,1752,2614,2668,2680,2762,3118,3130,3188,3228,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7043 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7043 4 (fun x => (if x<2680 then (if x<1740 then (if x<1642 then (if x<192 then 0 else 0) else (if x<1686 then 1 else 2)) else (if x<2614 then (if x<1752 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3188 then (if x<3118 then (if x<2762 then 2 else 1) else (if x<3130 then 0 else 3)) else (if x<3270 then (if x<3228 then 3 else 3) else (if x<3282 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7044 : Finset ℕ := ([40,144,192,222,1582,1642,1652,1686,1692,1734,1740,1746,1752,2614,2620,2662,2668,2674,2680,2702,2714,2762,2772,3118,3130,3178,3188,3222,3228,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7044 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7044 1692 4
  · have he : independentCachedBranchMembers7044.erase 1692=independentCachedBranchMembers7042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7042
  · have he : independentCachedBranchMembers7044.filter (independentCachedEdge 1692)=independentCachedBranchMembers7043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7043
def independentCachedBranchMembers7045 : Finset ℕ := ([144,222,1582,1642,1734,1740,2662,2668,2702,2762,3130,3188,3222,3228,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7045 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7045 4 (fun x => (if x<2702 then (if x<1734 then (if x<1582 then (if x<222 then 0 else 0) else (if x<1642 then 1 else 2)) else (if x<2662 then (if x<1740 then 1 else 2) else (if x<2668 then 1 else 2))) else (if x<3222 then (if x<3130 then (if x<2762 then 1 else 2) else (if x<3188 then 3 else 3)) else (if x<3282 then (if x<3228 then 0 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7046 : Finset ℕ := ([40,144,192,222,1582,1594,1642,1652,1686,1692,1734,1740,1746,1752,2614,2620,2662,2668,2674,2680,2702,2714,2762,2772,3118,3130,3178,3188,3222,3228,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7046 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7046 1594 4
  · have he : independentCachedBranchMembers7046.erase 1594=independentCachedBranchMembers7044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7044
  · have he : independentCachedBranchMembers7046.filter (independentCachedEdge 1594)=independentCachedBranchMembers7045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7045
def independentCachedBranchMembers7047 : Finset ℕ := ([144,192,1582,1652,1746,1752,2614,2620,2662,2668,2714,2762,3118,3188,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7047 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7047 4 (fun x => (if x<2662 then (if x<1746 then (if x<1582 then (if x<192 then 0 else 1) else (if x<1652 then 0 else 2)) else (if x<2614 then (if x<1752 then 1 else 2) else (if x<2620 then 2 else 1))) else (if x<3118 then (if x<2714 then (if x<2668 then 0 else 3) else (if x<2762 then 2 else 3)) else (if x<3282 then (if x<3188 then 1 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7048 : Finset ℕ := ([40,132,144,192,222,1582,1594,1642,1652,1686,1692,1734,1740,1746,1752,2614,2620,2662,2668,2674,2680,2702,2714,2762,2772,3118,3130,3178,3188,3222,3228,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7048 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7048 132 4
  · have he : independentCachedBranchMembers7048.erase 132=independentCachedBranchMembers7046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7046
  · have he : independentCachedBranchMembers7048.filter (independentCachedEdge 132)=independentCachedBranchMembers7047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7047
def independentCachedBranchMembers7049 : Finset ℕ := ([40,222,1652,1686,1734,1746,2620,2668,2680,2702,2714,2762,3188,3222,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7049 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7049 4 (fun x => (if x<2680 then (if x<1734 then (if x<1652 then (if x<222 then 0 else 1) else (if x<1686 then 2 else 0)) else (if x<2620 then (if x<1746 then 1 else 2) else (if x<2668 then 2 else 0))) else (if x<3188 then (if x<2714 then (if x<2702 then 3 else 1) else (if x<2762 then 2 else 3)) else (if x<3270 then (if x<3222 then 3 else 1) else (if x<3282 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7050 : Finset ℕ := ([34,40,132,144,192,222,1582,1594,1642,1652,1686,1692,1734,1740,1746,1752,2614,2620,2662,2668,2674,2680,2702,2714,2762,2772,3118,3130,3178,3188,3222,3228,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7050 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7050 34 4
  · have he : independentCachedBranchMembers7050.erase 34=independentCachedBranchMembers7048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7048
  · have he : independentCachedBranchMembers7050.filter (independentCachedEdge 34)=independentCachedBranchMembers7049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7049
def independentCachedBranchMembers7051 : Finset ℕ := ([34,36,40,48,130,132,136,144,192,222,1582,1590,1594,1596,1642,1644,1650,1652,1678,1686,1690,1692,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2674,2676,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7051 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7051 2676 5
  · have he : independentCachedBranchMembers7051.erase 2676=independentCachedBranchMembers7041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7041
  · have he : independentCachedBranchMembers7051.filter (independentCachedEdge 2676)=independentCachedBranchMembers7050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7050
def independentCachedBranchMembers7052 : Finset ℕ := ([48,136,192,222,1590,1642,1652,1678,1734,1740,1746,1752,2606,2618,2662,2668,2674,2680,2710,2716,2762,2772,3126,3132,3178,3188,3214,3226,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7052 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7052 5 (fun x => (if x<2674 then (if x<1734 then (if x<1590 then (if x<192 then (if x<136 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1652 then (if x<1642 then 0 else 2) else (if x<1678 then 2 else 0))) else (if x<2606 then (if x<1746 then (if x<1740 then 1 else 2) else (if x<1752 then 2 else 1)) else (if x<2662 then (if x<2618 then 3 else 4) else (if x<2668 then 4 else 2)))) else (if x<3178 then (if x<2762 then (if x<2710 then (if x<2680 then 0 else 3) else (if x<2716 then 4 else 3)) else (if x<3126 then (if x<2772 then 0 else 1) else (if x<3132 then 4 else 3))) else (if x<3270 then (if x<3214 then (if x<3188 then 3 else 0) else (if x<3226 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 0) else (if x<3288 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7053 : Finset ℕ := ([48,192,1652,1678,1746,1752,2606,2674,2680,2772,3126,3132,3178,3226,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7053 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7053 4 (fun x => (if x<2680 then (if x<1746 then (if x<1652 then (if x<192 then 0 else 0) else (if x<1678 then 1 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2674 then 2 else 1))) else (if x<3178 then (if x<3126 then (if x<2772 then 2 else 1) else (if x<3132 then 0 else 3)) else (if x<3270 then (if x<3226 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7054 : Finset ℕ := ([48,136,192,222,1590,1642,1652,1678,1690,1734,1740,1746,1752,2606,2618,2662,2668,2674,2680,2710,2716,2762,2772,3126,3132,3178,3188,3214,3226,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7054 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7054 1690 4
  · have he : independentCachedBranchMembers7054.erase 1690=independentCachedBranchMembers7052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7052
  · have he : independentCachedBranchMembers7054.filter (independentCachedEdge 1690)=independentCachedBranchMembers7053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7053
def independentCachedBranchMembers7055 : Finset ℕ := ([136,222,1590,1652,1734,1746,2662,2674,2710,2772,3132,3178,3214,3226,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7055 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7055 4 (fun x => (if x<2710 then (if x<1734 then (if x<1590 then (if x<222 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<2662 then (if x<1746 then 1 else 2) else (if x<2674 then 1 else 2))) else (if x<3214 then (if x<3132 then (if x<2772 then 1 else 2) else (if x<3178 then 3 else 3)) else (if x<3276 then (if x<3226 then 0 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7056 : Finset ℕ := ([48,136,192,222,1590,1596,1642,1652,1678,1690,1734,1740,1746,1752,2606,2618,2662,2668,2674,2680,2710,2716,2762,2772,3126,3132,3178,3188,3214,3226,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7056 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7056 1596 4
  · have he : independentCachedBranchMembers7056.erase 1596=independentCachedBranchMembers7054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7054
  · have he : independentCachedBranchMembers7056.filter (independentCachedEdge 1596)=independentCachedBranchMembers7055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7055
def independentCachedBranchMembers7057 : Finset ℕ := ([136,192,1590,1642,1740,1752,2606,2618,2662,2674,2716,2772,3126,3178,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7057 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7057 4 (fun x => (if x<2662 then (if x<1740 then (if x<1590 then (if x<192 then 0 else 1) else (if x<1642 then 0 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2618 then 2 else 1))) else (if x<3126 then (if x<2716 then (if x<2674 then 0 else 3) else (if x<2772 then 2 else 3)) else (if x<3276 then (if x<3178 then 1 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7058 : Finset ℕ := ([48,130,136,192,222,1590,1596,1642,1652,1678,1690,1734,1740,1746,1752,2606,2618,2662,2668,2674,2680,2710,2716,2762,2772,3126,3132,3178,3188,3214,3226,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7058 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7058 130 4
  · have he : independentCachedBranchMembers7058.erase 130=independentCachedBranchMembers7056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7056
  · have he : independentCachedBranchMembers7058.filter (independentCachedEdge 130)=independentCachedBranchMembers7057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7057
def independentCachedBranchMembers7059 : Finset ℕ := ([48,222,1642,1678,1734,1740,2618,2674,2680,2710,2716,2772,3178,3214,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7059 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7059 4 (fun x => (if x<2680 then (if x<1734 then (if x<1642 then (if x<222 then 0 else 1) else (if x<1678 then 2 else 0)) else (if x<2618 then (if x<1740 then 1 else 2) else (if x<2674 then 2 else 0))) else (if x<3178 then (if x<2716 then (if x<2710 then 3 else 1) else (if x<2772 then 2 else 3)) else (if x<3270 then (if x<3214 then 3 else 1) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7060 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1642,1652,1678,1690,1734,1740,1746,1752,2606,2618,2662,2668,2674,2680,2710,2716,2762,2772,3126,3132,3178,3188,3214,3226,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7060 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7060 36 4
  · have he : independentCachedBranchMembers7060.erase 36=independentCachedBranchMembers7058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7058
  · have he : independentCachedBranchMembers7060.filter (independentCachedEdge 36)=independentCachedBranchMembers7059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7059
def independentCachedBranchMembers7061 : Finset ℕ := ([34,36,40,48,130,132,136,144,192,222,1582,1590,1594,1596,1642,1644,1650,1652,1678,1686,1690,1692,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7061 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7061 2666 5
  · have he : independentCachedBranchMembers7061.erase 2666=independentCachedBranchMembers7051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7051
  · have he : independentCachedBranchMembers7061.filter (independentCachedEdge 2666)=independentCachedBranchMembers7060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7060
def independentCachedBranchMembers7062 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,160,190,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7062 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7062 160 6
  · have he : independentCachedBranchMembers7062.erase 160=independentCachedBranchMembers6836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6836
  · have he : independentCachedBranchMembers7062.filter (independentCachedEdge 160)=independentCachedBranchMembers7061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7061
def independentCachedBranchMembers7063 : Finset ℕ := ([12,18,48,68,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2764,2800,3118,3162,3180,3186,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7063 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7063 6 (fun x => (if x<2662 then (if x<1690 then (if x<1594 then (if x<48 then (if x<18 then 0 else 0) else (if x<68 then 1 else 1)) else (if x<1644 then (if x<1614 then 1 else 1) else (if x<1650 then 0 else 0))) else (if x<1752 then (if x<1714 then (if x<1708 then 2 else 2) else (if x<1734 then 3 else 2)) else (if x<2618 then (if x<1776 then 3 else 2) else (if x<2638 then 4 else 4)))) else (if x<3162 then (if x<2738 then (if x<2714 then (if x<2680 then 5 else 5) else (if x<2732 then 3 else 0)) else (if x<2800 then (if x<2764 then 0 else 1) else (if x<3118 then 3 else 4))) else (if x<3250 then (if x<3186 then (if x<3180 then 4 else 5) else (if x<3214 then 5 else 2)) else (if x<3276 then (if x<3256 then 1 else 2) else (if x<3282 then 0 else (if x<3300 then 0 else 2)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7064 : Finset ℕ := ([12,68,1614,1644,1708,1734,2638,2662,2732,2764,3118,3180,3214,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7064 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7064 5 (fun x => (if x<2662 then (if x<1644 then (if x<68 then 0 else (if x<1614 then 1 else 0)) else (if x<1734 then (if x<1708 then 1 else 0) else (if x<2638 then 1 else 1))) else (if x<3180 then (if x<2764 then (if x<2732 then 2 else 2) else (if x<3118 then 0 else 2)) else (if x<3276 then (if x<3214 then 0 else 0) else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7065 : Finset ℕ := ([12,18,48,68,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2764,2800,3118,3162,3180,3186,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7065 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7065 250 5
  · have he : independentCachedBranchMembers7065.erase 250=independentCachedBranchMembers7063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7063
  · have he : independentCachedBranchMembers7065.filter (independentCachedEdge 250)=independentCachedBranchMembers7064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7064
def independentCachedBranchMembers7066 : Finset ℕ := ([18,48,1594,1650,1708,1734,2618,2680,2732,2764,3162,3186,3214,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7066 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7066 5 (fun x => (if x<2680 then (if x<1650 then (if x<48 then 0 else (if x<1594 then 1 else 0)) else (if x<1734 then (if x<1708 then 1 else 0) else (if x<2618 then 1 else 1))) else (if x<3186 then (if x<2764 then (if x<2732 then 2 else 2) else (if x<3162 then 0 else 2)) else (if x<3276 then (if x<3214 then 0 else 2) else (if x<3300 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7067 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2764,2800,3118,3162,3180,3186,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7067 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7067 144 5
  · have he : independentCachedBranchMembers7067.erase 144=independentCachedBranchMembers7065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7065
  · have he : independentCachedBranchMembers7067.filter (independentCachedEdge 144)=independentCachedBranchMembers7066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7066
def independentCachedBranchMembers7068 : Finset ℕ := ([12,18,68,144,1614,1690,1708,1714,2638,2662,2680,2714,2732,2738,2764,3162,3180,3186,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7068 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7068 5 (fun x => (if x<2680 then (if x<1690 then (if x<68 then (if x<18 then 0 else 0) else (if x<144 then 1 else (if x<1614 then 1 else 1))) else (if x<1714 then (if x<1708 then 1 else 0) else (if x<2638 then 0 else (if x<2662 then 2 else 1)))) else (if x<3162 then (if x<2732 then (if x<2714 then 2 else 2) else (if x<2738 then 2 else (if x<2764 then 1 else 0))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3214 then 0 else (if x<3256 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7069 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2764,2800,3118,3162,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7069 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7069 3192 5
  · have he : independentCachedBranchMembers7069.erase 3192=independentCachedBranchMembers7067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7067
  · have he : independentCachedBranchMembers7069.filter (independentCachedEdge 3192)=independentCachedBranchMembers7068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7068
def independentCachedBranchMembers7070 : Finset ℕ := ([12,18,48,250,1594,1708,1714,1776,2618,2662,2680,2732,2738,2764,2800,3118,3180,3186,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7070 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7070 5 (fun x => (if x<2680 then (if x<1708 then (if x<48 then (if x<18 then 0 else 0) else (if x<250 then 1 else (if x<1594 then 1 else 1))) else (if x<1776 then (if x<1714 then 0 else 0) else (if x<2618 then 1 else (if x<2662 then 2 else 2)))) else (if x<3118 then (if x<2738 then (if x<2732 then 1 else 2) else (if x<2764 then 1 else (if x<2800 then 0 else 2))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3256 then 0 else (if x<3300 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7071 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2764,2800,3118,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7071 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7071 3174 5
  · have he : independentCachedBranchMembers7071.erase 3174=independentCachedBranchMembers7069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7069
  · have he : independentCachedBranchMembers7071.filter (independentCachedEdge 3174)=independentCachedBranchMembers7070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7070
end EntropyDesigns.QuadraticRefinement
