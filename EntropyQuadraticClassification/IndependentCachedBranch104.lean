/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch103
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6112 : Finset ℕ := ([130,238,1596,1614,1642,1652,1692,1702,1738,1748,1776,2606,2652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6112 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6112 1748 4
  · have he : independentCachedBranchMembers6112.erase 1748=independentCachedBranchMembers6110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6110
  · have he : independentCachedBranchMembers6112.filter (independentCachedEdge 1748)=independentCachedBranchMembers6111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6111
def independentCachedBranchMembers6113 : Finset ℕ := ([238,1596,1614,1642,1692,1738,2740,2758,2786,3174,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6113 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6113 4 (fun x => (if x<2740 then (if x<1642 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1692 then 1 else (if x<1738 then 2 else 2))) else (if x<3174 then (if x<2758 then 1 else (if x<2786 then 0 else 1)) else (if x<3252 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6114 : Finset ℕ := ([80,130,238,1596,1614,1642,1652,1692,1702,1738,1748,1776,2606,2652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6114 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6114 80 4
  · have he : independentCachedBranchMembers6114.erase 80=independentCachedBranchMembers6112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6112
  · have he : independentCachedBranchMembers6114.filter (independentCachedEdge 80)=independentCachedBranchMembers6113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6113
def independentCachedBranchMembers6115 : Finset ℕ := ([130,1596,1614,1652,1738,1776,2702,2740,2758,3192,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6115 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6115 4 (fun x => (if x<2702 then (if x<1652 then (if x<1596 then 0 else (if x<1614 then 0 else 1)) else (if x<1738 then 1 else (if x<1776 then 2 else 2))) else (if x<3192 then (if x<2740 then 1 else (if x<2758 then 1 else 0)) else (if x<3214 then 0 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6116 : Finset ℕ := ([34,80,130,238,1596,1614,1642,1652,1692,1702,1738,1748,1776,2606,2652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6116 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6116 34 4
  · have he : independentCachedBranchMembers6116.erase 34=independentCachedBranchMembers6114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6114
  · have he : independentCachedBranchMembers6116.filter (independentCachedEdge 34)=independentCachedBranchMembers6115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6115
def independentCachedBranchMembers6117 : Finset ℕ := ([238,1596,1614,1642,1652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6117 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6117 4 (fun x => (if x<2740 then (if x<1642 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<2702 then (if x<1652 then 1 else 2) else (if x<2730 then 0 else 2))) else (if x<3118 then (if x<2776 then (if x<2758 then 1 else 3) else (if x<2786 then 3 else 1)) else (if x<3174 then (if x<3164 then 0 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6118 : Finset ℕ := ([1614,1642,2740,2776,3118,3174] : List ℕ).toFinset
theorem independentCachedBranchBound6118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6118 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6118 3 (fun x => (if x<2776 then (if x<1642 then 0 else (if x<2740 then 1 else 0)) else (if x<3118 then 2 else (if x<3174 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6119 : Finset ℕ := ([130,238,1596,1614,1642,1652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6119 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6119 130 3
  · have he : independentCachedBranchMembers6119.erase 130=independentCachedBranchMembers6117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6117
  · have he : independentCachedBranchMembers6119.filter (independentCachedEdge 130)=independentCachedBranchMembers6118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6118
def independentCachedBranchMembers6120 : Finset ℕ := ([34,80,130,238,1596,1614,1642,1652,1692,1702,1738,1748,1776,2606,2652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3242,3252,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6120 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6120 3288 4
  · have he : independentCachedBranchMembers6120.erase 3288=independentCachedBranchMembers6116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6116
  · have he : independentCachedBranchMembers6120.filter (independentCachedEdge 3288)=independentCachedBranchMembers6119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6119
def independentCachedBranchMembers6121 : Finset ℕ := ([80,1642,1652,1692,1776,2606,2652,2730,2740,2758,2776,3174,3192,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6121 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6121 4 (fun x => (if x<2730 then (if x<1692 then (if x<1642 then 0 else (if x<1652 then 1 else 0)) else (if x<2606 then (if x<1776 then 2 else 1) else (if x<2652 then 1 else 0))) else (if x<3174 then (if x<2758 then (if x<2740 then 3 else 1) else (if x<2776 then 3 else 2)) else (if x<3214 then (if x<3192 then 2 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6122 : Finset ℕ := ([1652,1776,2740,2758,3192,3214] : List ℕ).toFinset
theorem independentCachedBranchBound6122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6122 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6122 3 (fun x => (if x<2758 then (if x<1776 then 0 else (if x<2740 then 1 else 0)) else (if x<3192 then 2 else (if x<3214 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6123 : Finset ℕ := ([34,80,1642,1652,1692,1776,2606,2652,2730,2740,2758,2776,3174,3192,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6123 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6123 34 3
  · have he : independentCachedBranchMembers6123.erase 34=independentCachedBranchMembers6121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6121
  · have he : independentCachedBranchMembers6123.filter (independentCachedEdge 34)=independentCachedBranchMembers6122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6122
def independentCachedBranchMembers6124 : Finset ℕ := ([34,80,130,238,1596,1614,1642,1652,1692,1702,1738,1748,1776,2606,2652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3242,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6124 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6124 3270 4
  · have he : independentCachedBranchMembers6124.erase 3270=independentCachedBranchMembers6120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6120
  · have he : independentCachedBranchMembers6124.filter (independentCachedEdge 3270)=independentCachedBranchMembers6123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6123
def independentCachedBranchMembers6125 : Finset ℕ := ([34,80,130,238,1596,1614,1692,1776,2606,2652,2702,2786,3118,3164,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6125 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6125 4 (fun x => (if x<2606 then (if x<1596 then (if x<130 then (if x<80 then 0 else 0) else (if x<238 then 1 else 1)) else (if x<1692 then (if x<1614 then 2 else 2) else (if x<1776 then 3 else 3))) else (if x<3118 then (if x<2702 then (if x<2652 then 0 else 0) else (if x<2786 then 1 else 1)) else (if x<3214 then (if x<3164 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6126 : Finset ℕ := ([34,80,130,238,1596,1614,1642,1652,1692,1702,1720,1738,1748,1776,2606,2652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3242,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6126 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6126 1720 4
  · have he : independentCachedBranchMembers6126.erase 1720=independentCachedBranchMembers6124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6124
  · have he : independentCachedBranchMembers6126.filter (independentCachedEdge 1720)=independentCachedBranchMembers6125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6125
def independentCachedBranchMembers6127 : Finset ℕ := ([18,34,40,68,80,130,136,192,222,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2764,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6127 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6127 18 5
  · have he : independentCachedBranchMembers6127.erase 18=independentCachedBranchMembers6101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6101
  · have he : independentCachedBranchMembers6127.filter (independentCachedEdge 18)=independentCachedBranchMembers6126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6126
def independentCachedBranchMembers6128 : Finset ℕ := ([250,1590,1626,1642,1652,1686,1720,1738,1764,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6128 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6128 5 (fun x => (if x<2740 then (if x<1686 then (if x<1626 then (if x<1590 then 0 else 1) else (if x<1642 then 0 else (if x<1652 then 1 else 2))) else (if x<1764 then (if x<1720 then 2 else (if x<1738 then 0 else 3)) else (if x<2714 then 1 else (if x<2730 then 0 else 3)))) else (if x<3158 then (if x<2776 then (if x<2758 then 1 else 3) else (if x<2792 then 3 else (if x<3130 then 1 else 0))) else (if x<3226 then (if x<3174 then 2 else (if x<3192 then 4 else 2)) else (if x<3252 then 2 else (if x<3304 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6129 : Finset ℕ := ([1626,1642,1686,1764,2740,2758,3130,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6129 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6129 4 (fun x => (if x<2740 then (if x<1686 then (if x<1642 then 0 else 1) else (if x<1764 then 0 else 1)) else (if x<3130 then (if x<2758 then 0 else 2) else (if x<3192 then 1 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6130 : Finset ℕ := ([136,250,1590,1626,1642,1652,1686,1720,1738,1764,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6130 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6130 136 4
  · have he : independentCachedBranchMembers6130.erase 136=independentCachedBranchMembers6128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6128
  · have he : independentCachedBranchMembers6130.filter (independentCachedEdge 136)=independentCachedBranchMembers6129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6129
def independentCachedBranchMembers6131 : Finset ℕ := ([1590,1626,1686,1764,2730,2740,2758,2776,3130,3158,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6131 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6131 4 (fun x => (if x<2758 then (if x<1764 then (if x<1626 then 0 else (if x<1686 then 0 else 1)) else (if x<2730 then 1 else (if x<2740 then 2 else 0))) else (if x<3158 then (if x<2776 then 1 else (if x<3130 then 0 else 2)) else (if x<3226 then 2 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6132 : Finset ℕ := ([136,250,1590,1626,1642,1652,1686,1720,1738,1764,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6132 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6132 3242 4
  · have he : independentCachedBranchMembers6132.erase 3242=independentCachedBranchMembers6130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6130
  · have he : independentCachedBranchMembers6132.filter (independentCachedEdge 3242)=independentCachedBranchMembers6131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6131
def independentCachedBranchMembers6133 : Finset ℕ := ([250,1642,1738,1764,2730,2758,2792,3130,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6133 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6133 4 (fun x => (if x<2792 then (if x<1764 then (if x<1642 then 0 else (if x<1738 then 0 else 1)) else (if x<2730 then 1 else (if x<2758 then 0 else 1))) else (if x<3192 then (if x<3130 then 1 else (if x<3158 then 0 else 2)) else (if x<3226 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6134 : Finset ℕ := ([136,250,1590,1626,1642,1652,1686,1720,1738,1764,2646,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6134 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6134 2646 4
  · have he : independentCachedBranchMembers6134.erase 2646=independentCachedBranchMembers6132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6132
  · have he : independentCachedBranchMembers6134.filter (independentCachedEdge 2646)=independentCachedBranchMembers6133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6133
def independentCachedBranchMembers6135 : Finset ℕ := ([136,1652,1686,1738,2714,2730,2758,3130,3158,3174,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6135 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6135 4 (fun x => (if x<2758 then (if x<1738 then (if x<1652 then 0 else (if x<1686 then 0 else 1)) else (if x<2714 then 1 else (if x<2730 then 0 else 2))) else (if x<3174 then (if x<3130 then 1 else (if x<3158 then 2 else 2)) else (if x<3252 then 0 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6136 : Finset ℕ := ([136,250,1590,1626,1642,1652,1686,1720,1738,1764,2618,2646,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6136 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6136 2618 4
  · have he : independentCachedBranchMembers6136.erase 2618=independentCachedBranchMembers6134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6134
  · have he : independentCachedBranchMembers6136.filter (independentCachedEdge 2618)=independentCachedBranchMembers6135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6135
def independentCachedBranchMembers6137 : Finset ℕ := ([136,250,1642,1652,1686,1764,2714,2792,3174,3192,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6137 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6137 4 (fun x => (if x<2714 then (if x<1652 then (if x<250 then 0 else (if x<1642 then 0 else 1)) else (if x<1686 then 1 else (if x<1764 then 2 else 2))) else (if x<3192 then (if x<2792 then 0 else (if x<3174 then 0 else 1)) else (if x<3226 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6138 : Finset ℕ := ([136,250,1590,1626,1642,1652,1686,1720,1738,1748,1764,2618,2646,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6138 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6138 1748 4
  · have he : independentCachedBranchMembers6138.erase 1748=independentCachedBranchMembers6136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6136
  · have he : independentCachedBranchMembers6138.filter (independentCachedEdge 1748)=independentCachedBranchMembers6137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6137
def independentCachedBranchMembers6139 : Finset ℕ := ([250,1590,1626,1642,1686,1738,2740,2776,2792,3192,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6139 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6139 4 (fun x => (if x<2740 then (if x<1642 then (if x<1590 then 0 else (if x<1626 then 1 else 0)) else (if x<1686 then 1 else (if x<1738 then 2 else 2))) else (if x<3192 then (if x<2776 then 1 else (if x<2792 then 0 else 1)) else (if x<3252 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6140 : Finset ℕ := ([68,136,250,1590,1626,1642,1652,1686,1720,1738,1748,1764,2618,2646,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6140 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6140 68 4
  · have he : independentCachedBranchMembers6140.erase 68=independentCachedBranchMembers6138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6138
  · have he : independentCachedBranchMembers6140.filter (independentCachedEdge 68)=independentCachedBranchMembers6139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6139
def independentCachedBranchMembers6141 : Finset ℕ := ([136,1590,1626,1652,1738,1764,2714,2740,2776,3174,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6141 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6141 4 (fun x => (if x<2714 then (if x<1652 then (if x<1590 then 0 else (if x<1626 then 0 else 1)) else (if x<1738 then 1 else (if x<1764 then 2 else 2))) else (if x<3174 then (if x<2740 then 1 else (if x<2776 then 1 else 0)) else (if x<3226 then 0 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6142 : Finset ℕ := ([40,68,136,250,1590,1626,1642,1652,1686,1720,1738,1748,1764,2618,2646,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6142 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6142 40 4
  · have he : independentCachedBranchMembers6142.erase 40=independentCachedBranchMembers6140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6140
  · have he : independentCachedBranchMembers6142.filter (independentCachedEdge 40)=independentCachedBranchMembers6141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6141
def independentCachedBranchMembers6143 : Finset ℕ := ([68,1642,1652,1686,1764,2618,2646,2730,2740,2758,2776,3174,3192,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6143 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6143 4 (fun x => (if x<2730 then (if x<1686 then (if x<1642 then 0 else (if x<1652 then 1 else 0)) else (if x<2618 then (if x<1764 then 2 else 1) else (if x<2646 then 1 else 0))) else (if x<3174 then (if x<2758 then (if x<2740 then 3 else 1) else (if x<2776 then 2 else 3)) else (if x<3226 then (if x<3192 then 0 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
