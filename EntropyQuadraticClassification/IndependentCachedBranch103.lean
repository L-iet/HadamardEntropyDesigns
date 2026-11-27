/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch102
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6080 : Finset ℕ := ([34,40,238,250,1590,1596,1642,1702,1708,1714,1720,1764,1776,2606,2618,2668,2674,2730,2740,2786,2792,3118,3130,3174,3186,3192,3242,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6080 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6080 3186 4
  · have he : independentCachedBranchMembers6080.erase 3186=independentCachedBranchMembers6076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6076
  · have he : independentCachedBranchMembers6080.filter (independentCachedEdge 3186)=independentCachedBranchMembers6079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6079
def independentCachedBranchMembers6081 : Finset ℕ := ([250,1590,1702,1720,1776,2618,2668,2674,2730,2740,2786,3118,3174,3192,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6081 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6081 4 (fun x => (if x<2674 then (if x<1720 then (if x<1590 then 0 else (if x<1702 then 1 else 2)) else (if x<2618 then (if x<1776 then 0 else 1) else (if x<2668 then 0 else 3))) else (if x<3118 then (if x<2740 then (if x<2730 then 1 else 2) else (if x<2786 then 1 else 3)) else (if x<3192 then (if x<3174 then 2 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6082 : Finset ℕ := ([1720,1776,2668,2740,3192,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6082 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6082 3 (fun x => (if x<2740 then (if x<1776 then 0 else (if x<2668 then 1 else 2)) else (if x<3192 then 0 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6083 : Finset ℕ := ([34,250,1590,1702,1720,1776,2618,2668,2674,2730,2740,2786,3118,3174,3192,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6083 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6083 34 3
  · have he : independentCachedBranchMembers6083.erase 34=independentCachedBranchMembers6081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6081
  · have he : independentCachedBranchMembers6083.filter (independentCachedEdge 34)=independentCachedBranchMembers6082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6082
def independentCachedBranchMembers6084 : Finset ℕ := ([34,40,238,250,1590,1596,1642,1702,1708,1714,1720,1764,1776,2606,2618,2668,2674,2730,2740,2786,2792,3118,3130,3174,3180,3186,3192,3242,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6084 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6084 3180 4
  · have he : independentCachedBranchMembers6084.erase 3180=independentCachedBranchMembers6080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6080
  · have he : independentCachedBranchMembers6084.filter (independentCachedEdge 3180)=independentCachedBranchMembers6083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6083
def independentCachedBranchMembers6085 : Finset ℕ := ([34,40,238,250,1590,1596,1764,1776,2606,2618,2786,2792,3118,3130,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6085 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6085 4 (fun x => (if x<2606 then (if x<1590 then (if x<238 then (if x<40 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1764 then (if x<1596 then 2 else 3) else (if x<1776 then 2 else 3))) else (if x<3118 then (if x<2786 then (if x<2618 then 0 else 1) else (if x<2792 then 0 else 1)) else (if x<3298 then (if x<3130 then 3 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6086 : Finset ℕ := ([34,40,238,250,1590,1596,1642,1652,1702,1708,1714,1720,1764,1776,2606,2618,2668,2674,2730,2740,2786,2792,3118,3130,3174,3180,3186,3192,3242,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6086 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6086 1652 4
  · have he : independentCachedBranchMembers6086.erase 1652=independentCachedBranchMembers6084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6084
  · have he : independentCachedBranchMembers6086.filter (independentCachedEdge 1652)=independentCachedBranchMembers6085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6085
def independentCachedBranchMembers6087 : Finset ℕ := ([34,40,68,80,130,136,222,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2764,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6087 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6087 222 5
  · have he : independentCachedBranchMembers6087.erase 222=independentCachedBranchMembers6069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6069
  · have he : independentCachedBranchMembers6087.filter (independentCachedEdge 222)=independentCachedBranchMembers6086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6086
def independentCachedBranchMembers6088 : Finset ℕ := ([80,130,136,1614,1626,1652,1686,1692,1702,1708,1714,1720,2646,2652,2668,2674,2702,2714,2730,2740,3158,3164,3174,3192,3214,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6088 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6088 5 (fun x => (if x<2668 then (if x<1692 then (if x<1614 then (if x<130 then 0 else (if x<136 then 0 else 1)) else (if x<1652 then (if x<1626 then 2 else 3) else (if x<1686 then 0 else 2))) else (if x<1714 then (if x<1702 then 1 else (if x<1708 then 0 else 2)) else (if x<2646 then (if x<1720 then 3 else 4) else (if x<2652 then 2 else 0)))) else (if x<3164 then (if x<2714 then (if x<2674 then 2 else (if x<2702 then 1 else 0)) else (if x<2740 then (if x<2730 then 1 else 4) else (if x<3158 then 2 else 4))) else (if x<3214 then (if x<3174 then 3 else (if x<3192 then 1 else 0)) else (if x<3242 then (if x<3226 then 1 else 3) else (if x<3252 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6089 : Finset ℕ := ([80,1626,1686,1692,1702,1708,2674,2702,2740,3192,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6089 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6089 4 (fun x => (if x<2674 then (if x<1692 then (if x<1626 then 0 else (if x<1686 then 0 else 1)) else (if x<1702 then 2 else (if x<1708 then 2 else 1))) else (if x<3192 then (if x<2702 then 0 else (if x<2740 then 1 else 1)) else (if x<3214 then 0 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6090 : Finset ℕ := ([68,80,130,136,1614,1626,1652,1686,1692,1702,1708,1714,1720,2646,2652,2668,2674,2702,2714,2730,2740,3158,3164,3174,3192,3214,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6090 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6090 68 4
  · have he : independentCachedBranchMembers6090.erase 68=independentCachedBranchMembers6088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6088
  · have he : independentCachedBranchMembers6090.filter (independentCachedEdge 68)=independentCachedBranchMembers6089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6089
def independentCachedBranchMembers6091 : Finset ℕ := ([130,1614,1686,1702,1720,2652,2668,2674,2714,2730,2740,3158,3174,3192,3214] : List ℕ).toFinset
theorem independentCachedBranchBound6091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6091 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6091 4 (fun x => (if x<2674 then (if x<1702 then (if x<1614 then 0 else (if x<1686 then 1 else 0)) else (if x<2652 then (if x<1720 then 1 else 2) else (if x<2668 then 1 else 0))) else (if x<3158 then (if x<2730 then (if x<2714 then 3 else 2) else (if x<2740 then 3 else 1)) else (if x<3192 then (if x<3174 then 3 else 2) else (if x<3214 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6092 : Finset ℕ := ([1686,1702,2674,2740,3192,3214] : List ℕ).toFinset
theorem independentCachedBranchBound6092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6092 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6092 3 (fun x => (if x<2740 then (if x<1702 then 0 else (if x<2674 then 1 else 2)) else (if x<3192 then 0 else (if x<3214 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6093 : Finset ℕ := ([68,130,1614,1686,1702,1720,2652,2668,2674,2714,2730,2740,3158,3174,3192,3214] : List ℕ).toFinset
theorem independentCachedBranchBound6093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6093 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6093 68 3
  · have he : independentCachedBranchMembers6093.erase 68=independentCachedBranchMembers6091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6091
  · have he : independentCachedBranchMembers6093.filter (independentCachedEdge 68)=independentCachedBranchMembers6092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6092
def independentCachedBranchMembers6094 : Finset ℕ := ([68,80,130,136,1614,1626,1652,1686,1692,1702,1708,1714,1720,2646,2652,2668,2674,2702,2714,2730,2740,3158,3164,3174,3186,3192,3214,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6094 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6094 3186 4
  · have he : independentCachedBranchMembers6094.erase 3186=independentCachedBranchMembers6090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6090
  · have he : independentCachedBranchMembers6094.filter (independentCachedEdge 3186)=independentCachedBranchMembers6093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6093
def independentCachedBranchMembers6095 : Finset ℕ := ([136,1626,1692,1702,1720,2646,2668,2674,2702,2730,2740,3164,3174,3192,3226] : List ℕ).toFinset
theorem independentCachedBranchBound6095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6095 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6095 4 (fun x => (if x<2674 then (if x<1702 then (if x<1626 then 0 else (if x<1692 then 1 else 0)) else (if x<2646 then (if x<1720 then 2 else 1) else (if x<2668 then 1 else 3))) else (if x<3164 then (if x<2730 then (if x<2702 then 0 else 2) else (if x<2740 then 3 else 1)) else (if x<3192 then (if x<3174 then 3 else 0) else (if x<3226 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6096 : Finset ℕ := ([1692,1720,2668,2740,3174,3226] : List ℕ).toFinset
theorem independentCachedBranchBound6096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6096 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6096 3 (fun x => (if x<2740 then (if x<1720 then 0 else (if x<2668 then 1 else 2)) else (if x<3174 then 0 else (if x<3226 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6097 : Finset ℕ := ([80,136,1626,1692,1702,1720,2646,2668,2674,2702,2730,2740,3164,3174,3192,3226] : List ℕ).toFinset
theorem independentCachedBranchBound6097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6097 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6097 80 3
  · have he : independentCachedBranchMembers6097.erase 80=independentCachedBranchMembers6095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6095
  · have he : independentCachedBranchMembers6097.filter (independentCachedEdge 80)=independentCachedBranchMembers6096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6096
def independentCachedBranchMembers6098 : Finset ℕ := ([68,80,130,136,1614,1626,1652,1686,1692,1702,1708,1714,1720,2646,2652,2668,2674,2702,2714,2730,2740,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6098 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6098 3180 4
  · have he : independentCachedBranchMembers6098.erase 3180=independentCachedBranchMembers6094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6094
  · have he : independentCachedBranchMembers6098.filter (independentCachedEdge 3180)=independentCachedBranchMembers6097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6097
def independentCachedBranchMembers6099 : Finset ℕ := ([68,80,130,136,1614,1626,1686,1692,2646,2652,2702,2714,3158,3164,3214,3226] : List ℕ).toFinset
theorem independentCachedBranchBound6099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6099 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6099 4 (fun x => (if x<2646 then (if x<1614 then (if x<130 then (if x<80 then 0 else 1) else (if x<136 then 0 else 1)) else (if x<1686 then (if x<1626 then 2 else 3) else (if x<1692 then 2 else 3))) else (if x<3158 then (if x<2702 then (if x<2652 then 1 else 0) else (if x<2714 then 1 else 0)) else (if x<3214 then (if x<3164 then 2 else 3) else (if x<3226 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6100 : Finset ℕ := ([68,80,130,136,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,2646,2652,2668,2674,2702,2714,2730,2740,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6100 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6100 1642 4
  · have he : independentCachedBranchMembers6100.erase 1642=independentCachedBranchMembers6098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6098
  · have he : independentCachedBranchMembers6100.filter (independentCachedEdge 1642)=independentCachedBranchMembers6099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6099
def independentCachedBranchMembers6101 : Finset ℕ := ([34,40,68,80,130,136,192,222,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2764,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6101 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6101 192 5
  · have he : independentCachedBranchMembers6101.erase 192=independentCachedBranchMembers6087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6087
  · have he : independentCachedBranchMembers6101.filter (independentCachedEdge 192)=independentCachedBranchMembers6100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6100
def independentCachedBranchMembers6102 : Finset ℕ := ([238,1596,1614,1642,1652,1692,1702,1738,1776,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6102 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6102 5 (fun x => (if x<2740 then (if x<1692 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1642 then 0 else (if x<1652 then 1 else 2))) else (if x<1776 then (if x<1702 then 2 else (if x<1738 then 0 else 3)) else (if x<2702 then 1 else (if x<2730 then 0 else 3)))) else (if x<3164 then (if x<2776 then (if x<2758 then 1 else 3) else (if x<2786 then 3 else (if x<3118 then 1 else 0))) else (if x<3214 then (if x<3174 then 2 else (if x<3192 then 2 else 4)) else (if x<3252 then 2 else (if x<3298 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6103 : Finset ℕ := ([1614,1642,1692,1776,2740,2776,3118,3174,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6103 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6103 4 (fun x => (if x<2740 then (if x<1692 then (if x<1642 then 0 else 1) else (if x<1776 then 0 else 1)) else (if x<3118 then (if x<2776 then 0 else 2) else (if x<3174 then 1 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6104 : Finset ℕ := ([130,238,1596,1614,1642,1652,1692,1702,1738,1776,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6104 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6104 130 4
  · have he : independentCachedBranchMembers6104.erase 130=independentCachedBranchMembers6102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6102
  · have he : independentCachedBranchMembers6104.filter (independentCachedEdge 130)=independentCachedBranchMembers6103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6103
def independentCachedBranchMembers6105 : Finset ℕ := ([1596,1614,1692,1776,2730,2740,2758,2776,3118,3164,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6105 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6105 4 (fun x => (if x<2758 then (if x<1776 then (if x<1614 then 0 else (if x<1692 then 0 else 1)) else (if x<2730 then 1 else (if x<2740 then 2 else 0))) else (if x<3164 then (if x<2776 then 0 else (if x<3118 then 1 else 2)) else (if x<3214 then 2 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6106 : Finset ℕ := ([130,238,1596,1614,1642,1652,1692,1702,1738,1776,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6106 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6106 3242 4
  · have he : independentCachedBranchMembers6106.erase 3242=independentCachedBranchMembers6104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6104
  · have he : independentCachedBranchMembers6106.filter (independentCachedEdge 3242)=independentCachedBranchMembers6105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6105
def independentCachedBranchMembers6107 : Finset ℕ := ([238,1642,1738,1776,2730,2776,2786,3118,3164,3174,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6107 4 (fun x => (if x<2786 then (if x<1776 then (if x<1642 then 0 else (if x<1738 then 0 else 1)) else (if x<2730 then 1 else (if x<2776 then 0 else 1))) else (if x<3174 then (if x<3118 then 1 else (if x<3164 then 0 else 2)) else (if x<3214 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6108 : Finset ℕ := ([130,238,1596,1614,1642,1652,1692,1702,1738,1776,2652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6108 2652 4
  · have he : independentCachedBranchMembers6108.erase 2652=independentCachedBranchMembers6106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6106
  · have he : independentCachedBranchMembers6108.filter (independentCachedEdge 2652)=independentCachedBranchMembers6107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6107
def independentCachedBranchMembers6109 : Finset ℕ := ([130,1652,1692,1738,2702,2730,2776,3118,3164,3192,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6109 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6109 4 (fun x => (if x<2776 then (if x<1738 then (if x<1652 then 0 else (if x<1692 then 0 else 1)) else (if x<2702 then 1 else (if x<2730 then 0 else 2))) else (if x<3192 then (if x<3118 then 1 else (if x<3164 then 2 else 2)) else (if x<3252 then 0 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6110 : Finset ℕ := ([130,238,1596,1614,1642,1652,1692,1702,1738,1776,2606,2652,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3214,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6110 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6110 2606 4
  · have he : independentCachedBranchMembers6110.erase 2606=independentCachedBranchMembers6108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6108
  · have he : independentCachedBranchMembers6110.filter (independentCachedEdge 2606)=independentCachedBranchMembers6109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6109
def independentCachedBranchMembers6111 : Finset ℕ := ([130,238,1642,1652,1692,1776,2702,2786,3174,3192,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6111 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6111 4 (fun x => (if x<2702 then (if x<1652 then (if x<238 then 0 else (if x<1642 then 0 else 1)) else (if x<1692 then 1 else (if x<1776 then 2 else 2))) else (if x<3192 then (if x<2786 then 0 else (if x<3174 then 0 else 1)) else (if x<3214 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
