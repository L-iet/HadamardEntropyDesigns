/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch101
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6048 : Finset ℕ := ([34,68,136,238,1590,1614,1642,1652,1692,1702,1720,1764,2606,2646,2668,2674,2714,2758,2776,2786,3130,3164,3174,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6048 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6048 34 4
  · have he : independentCachedBranchMembers6048.erase 34=independentCachedBranchMembers6046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6046
  · have he : independentCachedBranchMembers6048.filter (independentCachedEdge 34)=independentCachedBranchMembers6047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6047
def independentCachedBranchMembers6049 : Finset ℕ := ([34,68,136,238,1590,1614,1692,1764,2606,2646,2714,2786,3130,3164,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6049 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6049 4 (fun x => (if x<2606 then (if x<1590 then (if x<136 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3130 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6050 : Finset ℕ := ([34,68,136,238,1590,1614,1642,1652,1692,1702,1720,1764,2606,2646,2668,2674,2714,2758,2776,2786,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6050 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6050 3192 4
  · have he : independentCachedBranchMembers6050.erase 3192=independentCachedBranchMembers6048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6048
  · have he : independentCachedBranchMembers6050.filter (independentCachedEdge 3192)=independentCachedBranchMembers6049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6049
def independentCachedBranchMembers6051 : Finset ℕ := ([34,68,136,238,1642,1652,1702,1720,2668,2674,2758,2776,3130,3164,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6051 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6051 4 (fun x => (if x<2668 then (if x<1642 then (if x<136 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3130 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6052 : Finset ℕ := ([34,68,136,238,1590,1614,1642,1652,1692,1702,1720,1764,2606,2646,2668,2674,2714,2758,2776,2786,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6052 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6052 3102 4
  · have he : independentCachedBranchMembers6052.erase 3102=independentCachedBranchMembers6050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6050
  · have he : independentCachedBranchMembers6052.filter (independentCachedEdge 3102)=independentCachedBranchMembers6051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6051
def independentCachedBranchMembers6053 : Finset ℕ := ([1590,1614,1642,1652,1692,1702,1720,1764,2606,2646,2668,2674,2714,2758,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound6053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6053 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6053 4 (fun x => (if x<2606 then (if x<1692 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1764 then 1 else 0))) else (if x<2714 then (if x<2668 then (if x<2646 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2776 then (if x<2758 then 2 else 3) else (if x<2786 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6054 : Finset ℕ := ([34,68,136,238,1590,1614,1642,1652,1692,1702,1720,1764,2606,2646,2668,2674,2714,2758,2776,2786,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6054 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6054 3072 4
  · have he : independentCachedBranchMembers6054.erase 3072=independentCachedBranchMembers6052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6052
  · have he : independentCachedBranchMembers6054.filter (independentCachedEdge 3072)=independentCachedBranchMembers6053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6053
def independentCachedBranchMembers6055 : Finset ℕ := ([34,40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6055 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6055 2770 5
  · have he : independentCachedBranchMembers6055.erase 2770=independentCachedBranchMembers6041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6041
  · have he : independentCachedBranchMembers6055.filter (independentCachedEdge 2770)=independentCachedBranchMembers6054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6054
def independentCachedBranchMembers6056 : Finset ℕ := ([250,1596,1626,1642,1652,1686,1702,1720,1776,2618,2652,2668,2674,2702,2758,2776,2792,3118,3158,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6056 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6056 5 (fun x => (if x<2702 then (if x<1702 then (if x<1642 then (if x<1596 then 0 else (if x<1626 then 1 else 0)) else (if x<1652 then 1 else (if x<1686 then 2 else 2))) else (if x<2618 then (if x<1720 then 1 else (if x<1776 then 0 else 1)) else (if x<2668 then (if x<2652 then 0 else 3) else (if x<2674 then 2 else 3)))) else (if x<3192 then (if x<2792 then (if x<2758 then 2 else (if x<2776 then 3 else 0)) else (if x<3118 then 3 else (if x<3158 then 1 else 3))) else (if x<3252 then (if x<3226 then 0 else (if x<3242 then 0 else 4)) else (if x<3282 then (if x<3276 then 1 else 3) else (if x<3298 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6057 : Finset ℕ := ([1626,1642,1720,1776,2618,2674,2776,2792,3118,3158,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6057 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6057 4 (fun x => (if x<2776 then (if x<1776 then (if x<1642 then 0 else (if x<1720 then 1 else 0)) else (if x<2618 then 1 else (if x<2674 then 0 else 1))) else (if x<3158 then (if x<2792 then 0 else (if x<3118 then 1 else 2)) else (if x<3252 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6058 : Finset ℕ := ([130,250,1596,1626,1642,1652,1686,1702,1720,1776,2618,2652,2668,2674,2702,2758,2776,2792,3118,3158,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6058 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6058 130 4
  · have he : independentCachedBranchMembers6058.erase 130=independentCachedBranchMembers6056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6056
  · have he : independentCachedBranchMembers6058.filter (independentCachedEdge 130)=independentCachedBranchMembers6057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6057
def independentCachedBranchMembers6059 : Finset ℕ := ([1596,1642,1686,1720,2618,2668,2758,2792,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6059 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6059 4 (fun x => (if x<2758 then (if x<1720 then (if x<1642 then 0 else (if x<1686 then 0 else 1)) else (if x<2618 then 1 else (if x<2668 then 0 else 0))) else (if x<3252 then (if x<2792 then 1 else (if x<3226 then 1 else 2)) else (if x<3276 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6060 : Finset ℕ := ([80,130,250,1596,1626,1642,1652,1686,1702,1720,1776,2618,2652,2668,2674,2702,2758,2776,2792,3118,3158,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6060 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6060 80 4
  · have he : independentCachedBranchMembers6060.erase 80=independentCachedBranchMembers6058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6058
  · have he : independentCachedBranchMembers6060.filter (independentCachedEdge 80)=independentCachedBranchMembers6059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6059
def independentCachedBranchMembers6061 : Finset ℕ := ([1626,1652,1702,1776,2652,2674,2702,2776,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6061 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6061 4 (fun x => (if x<2702 then (if x<1776 then (if x<1652 then 0 else (if x<1702 then 0 else 1)) else (if x<2652 then 1 else (if x<2674 then 0 else 0))) else (if x<3252 then (if x<2776 then 1 else (if x<3226 then 1 else 2)) else (if x<3276 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6062 : Finset ℕ := ([40,80,130,250,1596,1626,1642,1652,1686,1702,1720,1776,2618,2652,2668,2674,2702,2758,2776,2792,3118,3158,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6062 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6062 40 4
  · have he : independentCachedBranchMembers6062.erase 40=independentCachedBranchMembers6060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6060
  · have he : independentCachedBranchMembers6062.filter (independentCachedEdge 40)=independentCachedBranchMembers6061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6061
def independentCachedBranchMembers6063 : Finset ℕ := ([40,80,130,250,1596,1626,1686,1776,2618,2652,2702,2792,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6063 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6063 4 (fun x => (if x<2618 then (if x<1596 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3118 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6064 : Finset ℕ := ([40,80,130,250,1596,1626,1642,1652,1686,1702,1720,1776,2618,2652,2668,2674,2702,2758,2776,2792,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6064 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6064 3174 4
  · have he : independentCachedBranchMembers6064.erase 3174=independentCachedBranchMembers6062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6062
  · have he : independentCachedBranchMembers6064.filter (independentCachedEdge 3174)=independentCachedBranchMembers6063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6063
def independentCachedBranchMembers6065 : Finset ℕ := ([40,80,130,250,1642,1652,1702,1720,2668,2674,2758,2776,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6065 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6065 4 (fun x => (if x<2668 then (if x<1642 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3118 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6066 : Finset ℕ := ([40,80,130,250,1596,1626,1642,1652,1686,1702,1720,1776,2618,2652,2668,2674,2702,2758,2776,2792,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6066 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6066 3102 4
  · have he : independentCachedBranchMembers6066.erase 3102=independentCachedBranchMembers6064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6064
  · have he : independentCachedBranchMembers6066.filter (independentCachedEdge 3102)=independentCachedBranchMembers6065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6065
def independentCachedBranchMembers6067 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1776,2618,2652,2668,2674,2702,2758,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6067 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6067 4 (fun x => (if x<2618 then (if x<1686 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<2702 then (if x<2668 then (if x<2652 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2776 then (if x<2758 then 2 else 3) else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6068 : Finset ℕ := ([40,80,130,250,1596,1626,1642,1652,1686,1702,1720,1776,2618,2652,2668,2674,2702,2758,2776,2792,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6068 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6068 3072 4
  · have he : independentCachedBranchMembers6068.erase 3072=independentCachedBranchMembers6066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6066
  · have he : independentCachedBranchMembers6068.filter (independentCachedEdge 3072)=independentCachedBranchMembers6067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6067
def independentCachedBranchMembers6069 : Finset ℕ := ([34,40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2764,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6069 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6069 2764 5
  · have he : independentCachedBranchMembers6069.erase 2764=independentCachedBranchMembers6055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6055
  · have he : independentCachedBranchMembers6069.filter (independentCachedEdge 2764)=independentCachedBranchMembers6068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6068
def independentCachedBranchMembers6070 : Finset ℕ := ([40,250,1590,1596,1642,1708,1714,1720,1764,1776,2606,2618,2668,2674,2730,2740,2786,2792,3118,3130,3174,3192,3242,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6070 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6070 5 (fun x => (if x<2674 then (if x<1714 then (if x<1596 then (if x<250 then 0 else (if x<1590 then 0 else 1)) else (if x<1642 then 2 else (if x<1708 then 0 else 1))) else (if x<1776 then (if x<1720 then 2 else (if x<1764 then 0 else 2)) else (if x<2618 then (if x<2606 then 1 else 1) else (if x<2668 then 0 else 2)))) else (if x<3130 then (if x<2786 then (if x<2730 then 1 else (if x<2740 then 3 else 1)) else (if x<2792 then 2 else (if x<3118 then 0 else 3))) else (if x<3242 then (if x<3174 then 4 else (if x<3192 then 4 else 0)) else (if x<3298 then (if x<3252 then 0 else 4) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6071 : Finset ℕ := ([40,250,1590,1708,1714,1764,2618,2668,2674,2792,3130,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6071 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6071 4 (fun x => (if x<2618 then (if x<1708 then (if x<250 then 0 else (if x<1590 then 0 else 1)) else (if x<1714 then 1 else (if x<1764 then 2 else 2))) else (if x<2792 then (if x<2668 then 0 else (if x<2674 then 2 else 1)) else (if x<3130 then 0 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6072 : Finset ℕ := ([40,250,1590,1596,1642,1702,1708,1714,1720,1764,1776,2606,2618,2668,2674,2730,2740,2786,2792,3118,3130,3174,3192,3242,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6072 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6072 1702 4
  · have he : independentCachedBranchMembers6072.erase 1702=independentCachedBranchMembers6070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6070
  · have he : independentCachedBranchMembers6072.filter (independentCachedEdge 1702)=independentCachedBranchMembers6071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6071
def independentCachedBranchMembers6073 : Finset ℕ := ([250,1590,1596,1714,1720,1776,2618,2674,2740,3130,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6073 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6073 4 (fun x => (if x<2618 then (if x<1714 then (if x<1590 then 0 else (if x<1596 then 1 else 2)) else (if x<1720 then 0 else (if x<1776 then 1 else 2))) else (if x<3130 then (if x<2674 then 0 else (if x<2740 then 3 else 1)) else (if x<3192 then 3 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6074 : Finset ℕ := ([40,238,250,1590,1596,1642,1702,1708,1714,1720,1764,1776,2606,2618,2668,2674,2730,2740,2786,2792,3118,3130,3174,3192,3242,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6074 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6074 238 4
  · have he : independentCachedBranchMembers6074.erase 238=independentCachedBranchMembers6072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6072
  · have he : independentCachedBranchMembers6074.filter (independentCachedEdge 238)=independentCachedBranchMembers6073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6073
def independentCachedBranchMembers6075 : Finset ℕ := ([40,1596,1708,1720,1764,1776,2668,2740,2792,3192,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6075 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6075 4 (fun x => (if x<2668 then (if x<1720 then (if x<1596 then 0 else (if x<1708 then 0 else 1)) else (if x<1764 then 2 else (if x<1776 then 2 else 1))) else (if x<3192 then (if x<2740 then 0 else (if x<2792 then 1 else 1)) else (if x<3252 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6076 : Finset ℕ := ([34,40,238,250,1590,1596,1642,1702,1708,1714,1720,1764,1776,2606,2618,2668,2674,2730,2740,2786,2792,3118,3130,3174,3192,3242,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6076 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6076 34 4
  · have he : independentCachedBranchMembers6076.erase 34=independentCachedBranchMembers6074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6074
  · have he : independentCachedBranchMembers6076.filter (independentCachedEdge 34)=independentCachedBranchMembers6075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6075
def independentCachedBranchMembers6077 : Finset ℕ := ([238,1596,1702,1720,1764,2606,2668,2674,2730,2740,2792,3130,3174,3192,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6077 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6077 4 (fun x => (if x<2674 then (if x<1720 then (if x<1596 then 0 else (if x<1702 then 1 else 0)) else (if x<2606 then (if x<1764 then 2 else 1) else (if x<2668 then 0 else 1))) else (if x<3130 then (if x<2740 then (if x<2730 then 3 else 2) else (if x<2792 then 1 else 3)) else (if x<3192 then (if x<3174 then 2 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6078 : Finset ℕ := ([1702,1764,2674,2740,3174,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6078 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6078 3 (fun x => (if x<2740 then (if x<1764 then 0 else (if x<2674 then 1 else 2)) else (if x<3174 then 0 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6079 : Finset ℕ := ([40,238,1596,1702,1720,1764,2606,2668,2674,2730,2740,2792,3130,3174,3192,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6079 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6079 40 3
  · have he : independentCachedBranchMembers6079.erase 40=independentCachedBranchMembers6077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6077
  · have he : independentCachedBranchMembers6079.filter (independentCachedEdge 40)=independentCachedBranchMembers6078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6078
end EntropyDesigns.QuadraticRefinement
