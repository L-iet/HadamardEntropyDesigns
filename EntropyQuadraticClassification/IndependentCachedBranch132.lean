/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch131
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7008 : Finset ℕ := ([1738,1752,2674,2714,3126,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7008 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7008 3 (fun x => (if x<2714 then (if x<1752 then 0 else (if x<2674 then 1 else 2)) else (if x<3126 then 0 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7009 : Finset ℕ := ([40,192,1644,1686,1738,1752,2606,2620,2674,2714,2758,2772,3126,3178,3192,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7009 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7009 40 3
  · have he : independentCachedBranchMembers7009.erase 40=independentCachedBranchMembers7007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7007
  · have he : independentCachedBranchMembers7009.filter (independentCachedEdge 40)=independentCachedBranchMembers7008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7008
def independentCachedBranchMembers7010 : Finset ℕ := ([40,144,192,222,1582,1644,1650,1686,1690,1734,1738,1748,1752,2606,2620,2668,2674,2710,2714,2758,2762,2772,2776,3126,3130,3174,3178,3188,3192,3214,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7010 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7010 1690 4
  · have he : independentCachedBranchMembers7010.erase 1690=independentCachedBranchMembers7006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7006
  · have he : independentCachedBranchMembers7010.filter (independentCachedEdge 1690)=independentCachedBranchMembers7009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7009
def independentCachedBranchMembers7011 : Finset ℕ := ([222,1582,1644,1734,1738,2620,2674,2710,2714,2772,2776,3174,3178,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7011 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7011 4 (fun x => (if x<2710 then (if x<1734 then (if x<1582 then 0 else (if x<1644 then 1 else 2)) else (if x<2620 then (if x<1738 then 0 else 1) else (if x<2674 then 1 else 3))) else (if x<3174 then (if x<2772 then (if x<2714 then 0 else 2) else (if x<2776 then 3 else 1)) else (if x<3214 then (if x<3178 then 2 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7012 : Finset ℕ := ([1734,1738,2620,2674,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7012 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7012 3 (fun x => (if x<2674 then (if x<1738 then 0 else (if x<2620 then 1 else 0)) else (if x<3214 then 2 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7013 : Finset ℕ := ([144,222,1582,1644,1734,1738,2620,2674,2710,2714,2772,2776,3174,3178,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7013 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7013 144 3
  · have he : independentCachedBranchMembers7013.erase 144=independentCachedBranchMembers7011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7011
  · have he : independentCachedBranchMembers7013.filter (independentCachedEdge 144)=independentCachedBranchMembers7012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7012
def independentCachedBranchMembers7014 : Finset ℕ := ([40,144,192,222,1582,1596,1644,1650,1686,1690,1734,1738,1748,1752,2606,2620,2668,2674,2710,2714,2758,2762,2772,2776,3126,3130,3174,3178,3188,3192,3214,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7014 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7014 1596 4
  · have he : independentCachedBranchMembers7014.erase 1596=independentCachedBranchMembers7010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7010
  · have he : independentCachedBranchMembers7014.filter (independentCachedEdge 1596)=independentCachedBranchMembers7013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7013
def independentCachedBranchMembers7015 : Finset ℕ := ([144,192,1582,1650,1748,1752,2606,2674,2772,2776,3126,3130,3174,3178,3228,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7015 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7015 4 (fun x => (if x<2772 then (if x<1748 then (if x<1582 then (if x<192 then 0 else 1) else (if x<1650 then 0 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2674 then 1 else 3))) else (if x<3174 then (if x<3126 then (if x<2776 then 0 else 3) else (if x<3130 then 2 else 1)) else (if x<3228 then (if x<3178 then 3 else 0) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7016 : Finset ℕ := ([40,130,144,192,222,1582,1596,1644,1650,1686,1690,1734,1738,1748,1752,2606,2620,2668,2674,2710,2714,2758,2762,2772,2776,3126,3130,3174,3178,3188,3192,3214,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7016 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7016 130 4
  · have he : independentCachedBranchMembers7016.erase 130=independentCachedBranchMembers7014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7014
  · have he : independentCachedBranchMembers7016.filter (independentCachedEdge 130)=independentCachedBranchMembers7015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7015
def independentCachedBranchMembers7017 : Finset ℕ := ([40,222,1650,1686,1734,1748,2674,2710,2758,2772,3130,3178,3192,3214,3228,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7017 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7017 4 (fun x => (if x<2758 then (if x<1734 then (if x<1650 then (if x<222 then 0 else 1) else (if x<1686 then 2 else 0)) else (if x<2674 then (if x<1748 then 1 else 2) else (if x<2710 then 3 else 1))) else (if x<3192 then (if x<3130 then (if x<2772 then 0 else 3) else (if x<3178 then 2 else 3)) else (if x<3228 then (if x<3214 then 0 else 1) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7018 : Finset ℕ := ([36,40,130,144,192,222,1582,1596,1644,1650,1686,1690,1734,1738,1748,1752,2606,2620,2668,2674,2710,2714,2758,2762,2772,2776,3126,3130,3174,3178,3188,3192,3214,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7018 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7018 36 4
  · have he : independentCachedBranchMembers7018.erase 36=independentCachedBranchMembers7016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7016
  · have he : independentCachedBranchMembers7018.filter (independentCachedEdge 36)=independentCachedBranchMembers7017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7017
def independentCachedBranchMembers7019 : Finset ℕ := ([34,36,40,48,130,132,136,144,192,222,1582,1590,1594,1596,1642,1644,1650,1652,1678,1686,1690,1692,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2662,2668,2674,2680,2702,2710,2714,2716,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3174,3178,3186,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7019 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7019 3186 5
  · have he : independentCachedBranchMembers7019.erase 3186=independentCachedBranchMembers6997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6997
  · have he : independentCachedBranchMembers7019.filter (independentCachedEdge 3186)=independentCachedBranchMembers7018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7018
def independentCachedBranchMembers7020 : Finset ℕ := ([136,192,222,1590,1644,1650,1678,1734,1738,1748,1752,2614,2618,2668,2702,2716,2758,2762,2776,3118,3132,3174,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7020 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7020 5 (fun x => (if x<2702 then (if x<1734 then (if x<1590 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1650 then (if x<1644 then 1 else 2) else (if x<1678 then 2 else 0))) else (if x<1752 then (if x<1738 then 1 else (if x<1748 then 2 else 2)) else (if x<2618 then (if x<2614 then 0 else 3) else (if x<2668 then 1 else 3)))) else (if x<3174 then (if x<2762 then (if x<2716 then 3 else (if x<2758 then 0 else 4)) else (if x<3118 then (if x<2776 then 0 else 4) else (if x<3132 then 3 else 1))) else (if x<3222 then (if x<3188 then 4 else (if x<3192 then 2 else 4)) else (if x<3276 then (if x<3226 then 3 else 0) else (if x<3282 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7021 : Finset ℕ := ([222,1644,1748,1752,2668,2716,2776,3118,3174,3222,3226,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7021 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7021 4 (fun x => (if x<2776 then (if x<1752 then (if x<1644 then 0 else (if x<1748 then 1 else 0)) else (if x<2668 then 1 else (if x<2716 then 2 else 0))) else (if x<3222 then (if x<3118 then 2 else (if x<3174 then 1 else 2)) else (if x<3226 then 0 else (if x<3282 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7022 : Finset ℕ := ([48,136,192,222,1590,1644,1650,1678,1734,1738,1748,1752,2614,2618,2668,2702,2716,2758,2762,2776,3118,3132,3174,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7022 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7022 48 4
  · have he : independentCachedBranchMembers7022.erase 48=independentCachedBranchMembers7020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7020
  · have he : independentCachedBranchMembers7022.filter (independentCachedEdge 48)=independentCachedBranchMembers7021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7021
def independentCachedBranchMembers7023 : Finset ℕ := ([48,136,192,222,1590,1678,1734,1752,2614,2702,2758,2776,3118,3174,3192,3222] : List ℕ).toFinset
theorem independentCachedBranchBound7023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7023 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7023 4 (fun x => (if x<2614 then (if x<1590 then (if x<192 then (if x<136 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1734 then (if x<1678 then 0 else 0) else (if x<1752 then 1 else 1))) else (if x<3118 then (if x<2758 then (if x<2702 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3192 then (if x<3174 then 2 else 3) else (if x<3222 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7024 : Finset ℕ := ([48,136,192,222,1590,1644,1650,1678,1734,1738,1748,1752,2614,2618,2668,2702,2716,2758,2762,2776,3118,3132,3174,3178,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7024 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7024 3178 4
  · have he : independentCachedBranchMembers7024.erase 3178=independentCachedBranchMembers7022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7022
  · have he : independentCachedBranchMembers7024.filter (independentCachedEdge 3178)=independentCachedBranchMembers7023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7023
def independentCachedBranchMembers7025 : Finset ℕ := ([48,136,1590,1644,1650,1678,1738,1748,2618,2716,2758,2776,3132,3174,3192,3226] : List ℕ).toFinset
theorem independentCachedBranchBound7025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7025 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7025 4 (fun x => (if x<2618 then (if x<1650 then (if x<1590 then (if x<136 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1738 then (if x<1678 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<3132 then (if x<2758 then (if x<2716 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3192 then (if x<3174 then 2 else 3) else (if x<3226 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7026 : Finset ℕ := ([48,136,192,222,1590,1644,1650,1678,1734,1738,1748,1752,2614,2618,2668,2702,2716,2758,2762,2772,2776,3118,3132,3174,3178,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7026 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7026 2772 4
  · have he : independentCachedBranchMembers7026.erase 2772=independentCachedBranchMembers7024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7024
  · have he : independentCachedBranchMembers7026.filter (independentCachedEdge 2772)=independentCachedBranchMembers7025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7025
def independentCachedBranchMembers7027 : Finset ℕ := ([192,222,1644,1650,1734,1738,1748,1752,2614,2618,2702,2716,3118,3132,3222,3226] : List ℕ).toFinset
theorem independentCachedBranchBound7027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7027 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7027 4 (fun x => (if x<2614 then (if x<1734 then (if x<1644 then (if x<222 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3118 then (if x<2702 then (if x<2618 then 2 else 3) else (if x<2716 then 2 else 3)) else (if x<3222 then (if x<3132 then 2 else 3) else (if x<3226 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7028 : Finset ℕ := ([48,136,192,222,1590,1644,1650,1678,1734,1738,1748,1752,2614,2618,2668,2674,2702,2716,2758,2762,2772,2776,3118,3132,3174,3178,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7028 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7028 2674 4
  · have he : independentCachedBranchMembers7028.erase 2674=independentCachedBranchMembers7026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7026
  · have he : independentCachedBranchMembers7028.filter (independentCachedEdge 2674)=independentCachedBranchMembers7027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7027
def independentCachedBranchMembers7029 : Finset ℕ := ([192,1650,1678,1748,1752,2614,2618,2668,2716,2758,2762,3118,3188,3192,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7029 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7029 4 (fun x => (if x<2668 then (if x<1748 then (if x<1650 then 0 else (if x<1678 then 1 else 2)) else (if x<2614 then (if x<1752 then 0 else 1) else (if x<2618 then 1 else 0))) else (if x<3118 then (if x<2758 then (if x<2716 then 3 else 1) else (if x<2762 then 2 else 3)) else (if x<3192 then (if x<3188 then 0 else 3) else (if x<3282 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7030 : Finset ℕ := ([1748,1752,2668,2716,3118,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7030 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7030 3 (fun x => (if x<2716 then (if x<1752 then 0 else (if x<2668 then 1 else 2)) else (if x<3118 then 0 else (if x<3282 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7031 : Finset ℕ := ([48,192,1650,1678,1748,1752,2614,2618,2668,2716,2758,2762,3118,3188,3192,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7031 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7031 48 3
  · have he : independentCachedBranchMembers7031.erase 48=independentCachedBranchMembers7029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7029
  · have he : independentCachedBranchMembers7031.filter (independentCachedEdge 48)=independentCachedBranchMembers7030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7030
def independentCachedBranchMembers7032 : Finset ℕ := ([48,136,192,222,1590,1644,1650,1678,1692,1734,1738,1748,1752,2614,2618,2668,2674,2702,2716,2758,2762,2772,2776,3118,3132,3174,3178,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7032 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7032 1692 4
  · have he : independentCachedBranchMembers7032.erase 1692=independentCachedBranchMembers7028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7028
  · have he : independentCachedBranchMembers7032.filter (independentCachedEdge 1692)=independentCachedBranchMembers7031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7031
def independentCachedBranchMembers7033 : Finset ℕ := ([222,1590,1650,1734,1748,2618,2668,2702,2716,2762,2776,3174,3188,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7033 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7033 4 (fun x => (if x<2702 then (if x<1734 then (if x<1590 then 0 else (if x<1650 then 1 else 2)) else (if x<2618 then (if x<1748 then 0 else 1) else (if x<2668 then 1 else 3))) else (if x<3174 then (if x<2762 then (if x<2716 then 0 else 2) else (if x<2776 then 3 else 1)) else (if x<3222 then (if x<3188 then 2 else 3) else (if x<3282 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7034 : Finset ℕ := ([1734,1748,2618,2668,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7034 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7034 3 (fun x => (if x<2668 then (if x<1748 then 0 else (if x<2618 then 1 else 0)) else (if x<3222 then 2 else (if x<3282 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7035 : Finset ℕ := ([136,222,1590,1650,1734,1748,2618,2668,2702,2716,2762,2776,3174,3188,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7035 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7035 136 3
  · have he : independentCachedBranchMembers7035.erase 136=independentCachedBranchMembers7033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7033
  · have he : independentCachedBranchMembers7035.filter (independentCachedEdge 136)=independentCachedBranchMembers7034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7034
def independentCachedBranchMembers7036 : Finset ℕ := ([48,136,192,222,1590,1594,1644,1650,1678,1692,1734,1738,1748,1752,2614,2618,2668,2674,2702,2716,2758,2762,2772,2776,3118,3132,3174,3178,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7036 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7036 1594 4
  · have he : independentCachedBranchMembers7036.erase 1594=independentCachedBranchMembers7032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7032
  · have he : independentCachedBranchMembers7036.filter (independentCachedEdge 1594)=independentCachedBranchMembers7035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7035
def independentCachedBranchMembers7037 : Finset ℕ := ([136,192,1590,1644,1738,1752,2614,2668,2762,2776,3118,3132,3174,3188,3226,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7037 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7037 4 (fun x => (if x<2762 then (if x<1738 then (if x<1590 then (if x<192 then 0 else 1) else (if x<1644 then 0 else 2)) else (if x<2614 then (if x<1752 then 1 else 2) else (if x<2668 then 1 else 3))) else (if x<3174 then (if x<3118 then (if x<2776 then 0 else 3) else (if x<3132 then 2 else 1)) else (if x<3226 then (if x<3188 then 3 else 0) else (if x<3282 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7038 : Finset ℕ := ([48,132,136,192,222,1590,1594,1644,1650,1678,1692,1734,1738,1748,1752,2614,2618,2668,2674,2702,2716,2758,2762,2772,2776,3118,3132,3174,3178,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7038 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7038 132 4
  · have he : independentCachedBranchMembers7038.erase 132=independentCachedBranchMembers7036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7036
  · have he : independentCachedBranchMembers7038.filter (independentCachedEdge 132)=independentCachedBranchMembers7037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7037
def independentCachedBranchMembers7039 : Finset ℕ := ([48,222,1644,1678,1734,1738,2668,2702,2758,2762,3132,3188,3192,3222,3226,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7039 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7039 4 (fun x => (if x<2758 then (if x<1734 then (if x<1644 then (if x<222 then 0 else 1) else (if x<1678 then 2 else 0)) else (if x<2668 then (if x<1738 then 1 else 2) else (if x<2702 then 3 else 1))) else (if x<3192 then (if x<3132 then (if x<2762 then 0 else 3) else (if x<3188 then 2 else 3)) else (if x<3226 then (if x<3222 then 0 else 1) else (if x<3282 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
