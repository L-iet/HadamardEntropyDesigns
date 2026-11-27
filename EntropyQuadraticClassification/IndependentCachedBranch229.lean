/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch228
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10112 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2702,2732,2738,2762,2772,2792,3118,3158,3178,3188,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10112 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10112 2732 4
  · have he : independentCachedBranchMembers10112.erase 2732=independentCachedBranchMembers10110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10110
  · have he : independentCachedBranchMembers10112.filter (independentCachedEdge 2732)=independentCachedBranchMembers10111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10111
def independentCachedBranchMembers10113 : Finset ℕ := ([238,1590,1678,1708,1714,2638,2668,2674,2762,2772,2792,3118,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10113 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10113 4 (fun x => (if x<2674 then (if x<1708 then (if x<1590 then 0 else (if x<1678 then 1 else 0)) else (if x<2638 then (if x<1714 then 1 else 2) else (if x<2668 then 0 else 2))) else (if x<3118 then (if x<2772 then (if x<2762 then 1 else 3) else (if x<2792 then 3 else 1)) else (if x<3242 then (if x<3222 then 0 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10114 : Finset ℕ := ([1678,1708,2674,2772,3118,3242] : List ℕ).toFinset
theorem independentCachedBranchBound10114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10114 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10114 3 (fun x => (if x<2772 then (if x<1708 then 0 else (if x<2674 then 1 else 0)) else (if x<3118 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10115 : Finset ℕ := ([72,238,1590,1678,1708,1714,2638,2668,2674,2762,2772,2792,3118,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10115 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10115 72 3
  · have he : independentCachedBranchMembers10115.erase 72=independentCachedBranchMembers10113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10113
  · have he : independentCachedBranchMembers10115.filter (independentCachedEdge 72)=independentCachedBranchMembers10114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10114
def independentCachedBranchMembers10116 : Finset ℕ := ([48,72,136,238,1590,1614,1650,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2702,2732,2738,2762,2772,2792,3118,3158,3178,3188,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10116 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10116 1650 4
  · have he : independentCachedBranchMembers10116.erase 1650=independentCachedBranchMembers10112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10112
  · have he : independentCachedBranchMembers10116.filter (independentCachedEdge 1650)=independentCachedBranchMembers10115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10115
def independentCachedBranchMembers10117 : Finset ℕ := ([136,1614,1708,1714,1768,2614,2668,2674,2702,2762,2772,3158,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10117 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10117 4 (fun x => (if x<2674 then (if x<1714 then (if x<1614 then 0 else (if x<1708 then 1 else 0)) else (if x<2614 then (if x<1768 then 2 else 1) else (if x<2668 then 2 else 1))) else (if x<3158 then (if x<2762 then (if x<2702 then 0 else 3) else (if x<2772 then 1 else 3)) else (if x<3252 then (if x<3242 then 0 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10118 : Finset ℕ := ([1708,1768,2668,2772,3158,3242] : List ℕ).toFinset
theorem independentCachedBranchBound10118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10118 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10118 3 (fun x => (if x<2772 then (if x<1768 then 0 else (if x<2668 then 1 else 0)) else (if x<3158 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10119 : Finset ℕ := ([48,136,1614,1708,1714,1768,2614,2668,2674,2702,2762,2772,3158,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10119 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10119 48 3
  · have he : independentCachedBranchMembers10119.erase 48=independentCachedBranchMembers10117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10117
  · have he : independentCachedBranchMembers10119.filter (independentCachedEdge 48)=independentCachedBranchMembers10118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10118
def independentCachedBranchMembers10120 : Finset ℕ := ([48,72,136,238,1590,1614,1644,1650,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2702,2732,2738,2762,2772,2792,3118,3158,3178,3188,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10120 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10120 1644 4
  · have he : independentCachedBranchMembers10120.erase 1644=independentCachedBranchMembers10116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10116
  · have he : independentCachedBranchMembers10120.filter (independentCachedEdge 1644)=independentCachedBranchMembers10119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10119
def independentCachedBranchMembers10121 : Finset ℕ := ([48,238,1614,1678,1738,1748,2638,2702,2762,2772,3118,3178,3188,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10121 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10121 4 (fun x => (if x<2762 then (if x<1738 then (if x<1614 then (if x<238 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<2638 then (if x<1748 then 2 else 2) else (if x<2702 then 1 else 0))) else (if x<3188 then (if x<3118 then (if x<2772 then 3 else 3) else (if x<3178 then 1 else 2)) else (if x<3252 then (if x<3242 then 2 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10122 : Finset ℕ := ([18,48,72,136,238,1590,1614,1644,1650,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2702,2732,2738,2762,2772,2792,3118,3158,3178,3188,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10122 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10122 18 4
  · have he : independentCachedBranchMembers10122.erase 18=independentCachedBranchMembers10120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10120
  · have he : independentCachedBranchMembers10122.filter (independentCachedEdge 18)=independentCachedBranchMembers10121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10121
def independentCachedBranchMembers10123 : Finset ℕ := ([72,136,1590,1738,1748,1768,2614,2762,2772,2792,3158,3178,3188,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10123 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10123 4 (fun x => (if x<2772 then (if x<1748 then (if x<1590 then (if x<136 then 0 else 1) else (if x<1738 then 0 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2762 then 1 else 0))) else (if x<3188 then (if x<3158 then (if x<2792 then 3 else 3) else (if x<3178 then 2 else 2)) else (if x<3242 then (if x<3222 then 1 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10124 : Finset ℕ := ([12,18,48,72,136,238,1590,1614,1644,1650,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2702,2732,2738,2762,2772,2792,3118,3158,3178,3188,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10124 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10124 12 4
  · have he : independentCachedBranchMembers10124.erase 12=independentCachedBranchMembers10122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10122
  · have he : independentCachedBranchMembers10124.filter (independentCachedEdge 12)=independentCachedBranchMembers10123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10123
def independentCachedBranchMembers10125 : Finset ℕ := ([12,18,40,48,72,80,136,144,238,246,1582,1590,1614,1622,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10125 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10125 3284 5
  · have he : independentCachedBranchMembers10125.erase 3284=independentCachedBranchMembers10103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10103
  · have he : independentCachedBranchMembers10125.filter (independentCachedEdge 3284)=independentCachedBranchMembers10124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10124
def independentCachedBranchMembers10126 : Finset ℕ := ([80,144,246,1582,1622,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2710,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10126 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10126 5 (fun x => (if x<2674 then (if x<1714 then (if x<1582 then (if x<144 then 0 else (if x<246 then 1 else 0)) else (if x<1686 then (if x<1622 then 1 else 0) else (if x<1708 then 1 else 2))) else (if x<1776 then (if x<1738 then 2 else (if x<1748 then 2 else 2)) else (if x<2646 then (if x<2606 then 0 else 3) else (if x<2668 then 3 else 1)))) else (if x<3178 then (if x<2772 then (if x<2710 then 0 else (if x<2762 then 4 else 3)) else (if x<3126 then (if x<2800 then 0 else 4) else (if x<3150 then 3 else 3))) else (if x<3242 then (if x<3188 then 1 else (if x<3214 then 0 else 4)) else (if x<3282 then (if x<3252 then 2 else 2) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10127 : Finset ℕ := ([246,1714,1738,1776,2674,2762,2800,3126,3150,3188,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10127 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10127 4 (fun x => (if x<2800 then (if x<1776 then (if x<1714 then 0 else (if x<1738 then 0 else 1)) else (if x<2674 then 1 else (if x<2762 then 0 else 2))) else (if x<3188 then (if x<3126 then 2 else (if x<3150 then 0 else 1)) else (if x<3214 then 1 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10128 : Finset ℕ := ([40,80,144,246,1582,1622,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2710,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10128 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10128 40 4
  · have he : independentCachedBranchMembers10128.erase 40=independentCachedBranchMembers10126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10126
  · have he : independentCachedBranchMembers10128.filter (independentCachedEdge 40)=independentCachedBranchMembers10127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10127
def independentCachedBranchMembers10129 : Finset ℕ := ([40,80,144,246,1582,1622,1686,1776,2606,2646,2710,2800,3126,3150,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10129 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10129 4 (fun x => (if x<2606 then (if x<1582 then (if x<144 then (if x<80 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1686 then (if x<1622 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2646 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3150 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10130 : Finset ℕ := ([40,80,144,246,1582,1622,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2710,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10130 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10130 3276 4
  · have he : independentCachedBranchMembers10130.erase 3276=independentCachedBranchMembers10128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10128
  · have he : independentCachedBranchMembers10130.filter (independentCachedEdge 3276)=independentCachedBranchMembers10129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10129
def independentCachedBranchMembers10131 : Finset ℕ := ([40,80,1582,1622,1708,1714,1738,1748,2668,2674,2710,2800,3178,3188,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10131 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10131 4 (fun x => (if x<2668 then (if x<1708 then (if x<1582 then (if x<80 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2710 then (if x<2674 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3188 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10132 : Finset ℕ := ([40,80,144,246,1582,1622,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2710,2738,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10132 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10132 2738 4
  · have he : independentCachedBranchMembers10132.erase 2738=independentCachedBranchMembers10130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10130
  · have he : independentCachedBranchMembers10132.filter (independentCachedEdge 2738)=independentCachedBranchMembers10131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10131
def independentCachedBranchMembers10133 : Finset ℕ := ([144,246,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,3126,3150,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10133 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10133 4 (fun x => (if x<2606 then (if x<1714 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3126 then (if x<2668 then (if x<2646 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3178 then (if x<3150 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10134 : Finset ℕ := ([40,80,144,246,1582,1622,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2710,2732,2738,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10134 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10134 2732 4
  · have he : independentCachedBranchMembers10134.erase 2732=independentCachedBranchMembers10132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10132
  · have he : independentCachedBranchMembers10134.filter (independentCachedEdge 2732)=independentCachedBranchMembers10133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10133
def independentCachedBranchMembers10135 : Finset ℕ := ([144,1622,1708,1714,1776,2606,2668,2674,2710,2762,2772,3150,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10135 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10135 4 (fun x => (if x<2674 then (if x<1714 then (if x<1622 then 0 else (if x<1708 then 1 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2668 then 2 else 0))) else (if x<3150 then (if x<2762 then (if x<2710 then 1 else 3) else (if x<2772 then 3 else 1)) else (if x<3252 then (if x<3242 then 0 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10136 : Finset ℕ := ([1714,1776,2674,2762,3150,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10136 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10136 3 (fun x => (if x<2762 then (if x<1776 then 0 else (if x<2674 then 1 else 0)) else (if x<3150 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10137 : Finset ℕ := ([40,144,1622,1708,1714,1776,2606,2668,2674,2710,2762,2772,3150,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10137 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10137 40 3
  · have he : independentCachedBranchMembers10137.erase 40=independentCachedBranchMembers10135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10135
  · have he : independentCachedBranchMembers10137.filter (independentCachedEdge 40)=independentCachedBranchMembers10136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10136
def independentCachedBranchMembers10138 : Finset ℕ := ([40,80,144,246,1582,1622,1650,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2710,2732,2738,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10138 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10138 1650 4
  · have he : independentCachedBranchMembers10138.erase 1650=independentCachedBranchMembers10134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10134
  · have he : independentCachedBranchMembers10138.filter (independentCachedEdge 1650)=independentCachedBranchMembers10137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10137
def independentCachedBranchMembers10139 : Finset ℕ := ([246,1582,1686,1708,1714,2646,2668,2674,2762,2772,2800,3126,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10139 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10139 4 (fun x => (if x<2674 then (if x<1708 then (if x<1582 then 0 else (if x<1686 then 1 else 0)) else (if x<2646 then (if x<1714 then 2 else 1) else (if x<2668 then 0 else 1))) else (if x<3126 then (if x<2772 then (if x<2762 then 2 else 3) else (if x<2800 then 3 else 1)) else (if x<3242 then (if x<3214 then 0 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10140 : Finset ℕ := ([1686,1714,2668,2762,3126,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10140 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10140 3 (fun x => (if x<2762 then (if x<1714 then 0 else (if x<2668 then 1 else 0)) else (if x<3126 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10141 : Finset ℕ := ([80,246,1582,1686,1708,1714,2646,2668,2674,2762,2772,2800,3126,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10141 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10141 80 3
  · have he : independentCachedBranchMembers10141.erase 80=independentCachedBranchMembers10139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10139
  · have he : independentCachedBranchMembers10141.filter (independentCachedEdge 80)=independentCachedBranchMembers10140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10140
def independentCachedBranchMembers10142 : Finset ℕ := ([40,80,144,246,1582,1622,1644,1650,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2710,2732,2738,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10142 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10142 1644 4
  · have he : independentCachedBranchMembers10142.erase 1644=independentCachedBranchMembers10138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10138
  · have he : independentCachedBranchMembers10142.filter (independentCachedEdge 1644)=independentCachedBranchMembers10141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10141
def independentCachedBranchMembers10143 : Finset ℕ := ([80,144,1582,1738,1748,1776,2606,2762,2772,2800,3150,3178,3188,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10143 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10143 4 (fun x => (if x<2772 then (if x<1748 then (if x<1582 then (if x<144 then 0 else 1) else (if x<1738 then 0 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2762 then 1 else 3))) else (if x<3188 then (if x<3150 then (if x<2800 then 0 else 3) else (if x<3178 then 2 else 1)) else (if x<3242 then (if x<3214 then 2 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
