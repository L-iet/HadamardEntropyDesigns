/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch41
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4128 : Finset ℕ := ([12,36,66,80,1590,1642,1708,1738,1752,1762,1776,2606,2620,2650,2674,2716,2740,2770,2792,3118,3132,3162,3186,3214,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4128 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4128 3214 4
  · have he : independentCachedBranchMembers4128.erase 3214=independentCachedBranchMembers4122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4122
  · have he : independentCachedBranchMembers4128.filter (independentCachedEdge 3214)=independentCachedBranchMembers4127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4127
def independentCachedBranchMembers4129 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1650,1678,1702,1708,1738,1746,1752,1762,1768,1776,2606,2620,2650,2674,2680,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4129 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4129 1768 5
  · have he : independentCachedBranchMembers4129.erase 1768=independentCachedBranchMembers4119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4119
  · have he : independentCachedBranchMembers4129.filter (independentCachedEdge 1768)=independentCachedBranchMembers4128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4128
def independentCachedBranchMembers4130 : Finset ℕ := ([36,80,192,250,1596,1642,1650,1678,1708,1752,1762,2606,2650,2680,2716,2762,2770,2800,3118,3162,3192,3228,3238,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4130 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4130 5 (fun x => (if x<2680 then (if x<1650 then (if x<250 then (if x<80 then 0 else (if x<192 then 0 else 1)) else (if x<1596 then 1 else (if x<1642 then 2 else 2))) else (if x<1752 then (if x<1678 then 3 else (if x<1708 then 2 else 0)) else (if x<2606 then (if x<1762 then 0 else 1) else (if x<2650 then 0 else 0)))) else (if x<3192 then (if x<2770 then (if x<2716 then 2 else (if x<2762 then 2 else 1)) else (if x<3118 then (if x<2800 then 3 else 1) else (if x<3162 then 4 else 3))) else (if x<3274 then (if x<3228 then 4 else (if x<3238 then 4 else 0)) else (if x<3304 then (if x<3282 then 4 else 0) else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4131 : Finset ℕ := ([36,80,1596,1650,1678,2680,2762,2800,3118,3162,3228,3238,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4131 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4131 4 (fun x => (if x<2800 then (if x<1650 then (if x<80 then 0 else (if x<1596 then 0 else 1)) else (if x<2680 then (if x<1678 then 1 else 2) else (if x<2762 then 1 else 2))) else (if x<3228 then (if x<3118 then 2 else (if x<3162 then 0 else 0)) else (if x<3282 then (if x<3238 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4132 : Finset ℕ := ([36,80,192,250,1596,1642,1650,1678,1708,1752,1762,2606,2650,2680,2716,2762,2770,2792,2800,3118,3162,3192,3228,3238,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4132 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4132 2792 4
  · have he : independentCachedBranchMembers4132.erase 2792=independentCachedBranchMembers4130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4130
  · have he : independentCachedBranchMembers4132.filter (independentCachedEdge 2792)=independentCachedBranchMembers4131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4131
def independentCachedBranchMembers4133 : Finset ℕ := ([80,250,1642,1678,1708,1762,2680,2770,2800,3118,3238,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4133 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4133 4 (fun x => (if x<2680 then (if x<1678 then (if x<250 then 0 else (if x<1642 then 0 else 1)) else (if x<1708 then 1 else (if x<1762 then 2 else 2))) else (if x<3118 then (if x<2770 then 0 else (if x<2800 then 0 else 3)) else (if x<3274 then (if x<3238 then 1 else 2) else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4134 : Finset ℕ := ([80,250,3118,3238,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4134 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4134 3 (fun x => (if x<3238 then (if x<250 then 0 else (if x<3118 then 0 else 1)) else (if x<3274 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4135 : Finset ℕ := ([80,250,1642,1678,1708,1762,2680,2716,2770,2800,3118,3238,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4135 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4135 2716 3
  · have he : independentCachedBranchMembers4135.erase 2716=independentCachedBranchMembers4133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4133
  · have he : independentCachedBranchMembers4135.filter (independentCachedEdge 2716)=independentCachedBranchMembers4134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4134
def independentCachedBranchMembers4136 : Finset ℕ := ([1678,1762,2680,2770,3118,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4136 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4136 3 (fun x => (if x<2770 then (if x<1762 then 0 else (if x<2680 then 0 else 1)) else (if x<3118 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4137 : Finset ℕ := ([80,250,1642,1678,1708,1762,2650,2680,2716,2770,2800,3118,3238,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4137 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4137 2650 3
  · have he : independentCachedBranchMembers4137.erase 2650=independentCachedBranchMembers4135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4135
  · have he : independentCachedBranchMembers4137.filter (independentCachedEdge 2650)=independentCachedBranchMembers4136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4136
def independentCachedBranchMembers4138 : Finset ℕ := ([36,80,192,250,1596,1642,1650,1678,1708,1752,1762,2606,2650,2680,2716,2762,2770,2792,2800,3118,3126,3162,3192,3228,3238,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4138 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4138 3126 4
  · have he : independentCachedBranchMembers4138.erase 3126=independentCachedBranchMembers4132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4132
  · have he : independentCachedBranchMembers4138.filter (independentCachedEdge 3126)=independentCachedBranchMembers4137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4137
def independentCachedBranchMembers4139 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1650,1678,1692,1702,1708,1738,1746,1752,1762,1768,1776,2606,2620,2650,2674,2680,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4139 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4139 1692 5
  · have he : independentCachedBranchMembers4139.erase 1692=independentCachedBranchMembers4129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4129
  · have he : independentCachedBranchMembers4139.filter (independentCachedEdge 1692)=independentCachedBranchMembers4138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4138
def independentCachedBranchMembers4140 : Finset ℕ := ([1590,1596,1642,1678,1708,1746,1752,1776,2606,2674,2680,2740,2762,2786,3118,3162,3186,3228,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4140 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4140 5 (fun x => (if x<2680 then (if x<1746 then (if x<1642 then (if x<1596 then 0 else 1) else (if x<1678 then 0 else (if x<1708 then 0 else 2))) else (if x<1776 then (if x<1752 then 0 else 1) else (if x<2606 then 2 else (if x<2674 then 0 else 0)))) else (if x<3162 then (if x<2762 then (if x<2740 then 1 else 2) else (if x<2786 then 0 else (if x<3118 then 3 else 4))) else (if x<3228 then (if x<3186 then 4 else 3) else (if x<3274 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4141 : Finset ℕ := ([1590,1596,1678,1708,2606,2740,3118,3228] : List ℕ).toFinset
theorem independentCachedBranchBound4141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4141 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4141 4 (fun x => (if x<2606 then (if x<1678 then (if x<1596 then 0 else 1) else (if x<1708 then 0 else 2)) else (if x<3118 then (if x<2740 then 0 else 1) else (if x<3228 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4142 : Finset ℕ := ([250,1590,1596,1642,1678,1708,1746,1752,1776,2606,2674,2680,2740,2762,2786,3118,3162,3186,3228,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4142 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4142 250 4
  · have he : independentCachedBranchMembers4142.erase 250=independentCachedBranchMembers4140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4140
  · have he : independentCachedBranchMembers4142.filter (independentCachedEdge 250)=independentCachedBranchMembers4141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4141
def independentCachedBranchMembers4143 : Finset ℕ := ([1590,1678,1752,1776,2606,2680,3118,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4143 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4143 4 (fun x => (if x<2606 then (if x<1752 then (if x<1678 then 0 else 0) else (if x<1776 then 1 else 2)) else (if x<3118 then (if x<2680 then 0 else 1) else (if x<3304 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4144 : Finset ℕ := ([66,250,1590,1596,1642,1678,1708,1746,1752,1776,2606,2674,2680,2740,2762,2786,3118,3162,3186,3228,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4144 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4144 66 4
  · have he : independentCachedBranchMembers4144.erase 66=independentCachedBranchMembers4142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4142
  · have he : independentCachedBranchMembers4144.filter (independentCachedEdge 66)=independentCachedBranchMembers4143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4143
def independentCachedBranchMembers4145 : Finset ℕ := ([1590,1678,1708,1752,2606,2680,2740,2786,3186,3228,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4145 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4145 4 (fun x => (if x<2740 then (if x<1752 then (if x<1678 then 0 else (if x<1708 then 0 else 1)) else (if x<2606 then 1 else (if x<2680 then 0 else 2))) else (if x<3228 then (if x<2786 then 2 else (if x<3186 then 2 else 3)) else (if x<3274 then 1 else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4146 : Finset ℕ := ([66,250,1590,1596,1642,1678,1708,1746,1752,1776,2606,2674,2680,2740,2762,2786,3118,3162,3186,3228,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4146 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4146 3298 4
  · have he : independentCachedBranchMembers4146.erase 3298=independentCachedBranchMembers4144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4144
  · have he : independentCachedBranchMembers4146.filter (independentCachedEdge 3298)=independentCachedBranchMembers4145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4145
def independentCachedBranchMembers4147 : Finset ℕ := ([250,1678,1746,1752,2606,2674,2680,2740,2786,3162,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4147 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4147 4 (fun x => (if x<2680 then (if x<1752 then (if x<1678 then 0 else (if x<1746 then 1 else 0)) else (if x<2606 then 1 else (if x<2674 then 1 else 0))) else (if x<3162 then (if x<2740 then 1 else (if x<2786 then 2 else 2)) else (if x<3228 then 0 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4148 : Finset ℕ := ([66,250,1590,1596,1642,1678,1708,1746,1752,1776,2606,2674,2680,2740,2762,2786,3118,3162,3186,3228,3252,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4148 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4148 3252 4
  · have he : independentCachedBranchMembers4148.erase 3252=independentCachedBranchMembers4146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4146
  · have he : independentCachedBranchMembers4148.filter (independentCachedEdge 3252)=independentCachedBranchMembers4147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4147
def independentCachedBranchMembers4149 : Finset ℕ := ([66,1590,1708,1746,2606,2680,2740,2762,2786,3162,3186,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4149 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4149 4 (fun x => (if x<2740 then (if x<1746 then (if x<1590 then 0 else (if x<1708 then 1 else 0)) else (if x<2606 then 1 else (if x<2680 then 1 else 2))) else (if x<3162 then (if x<2762 then 0 else (if x<2786 then 1 else 2)) else (if x<3186 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4150 : Finset ℕ := ([66,250,1590,1596,1642,1678,1708,1746,1752,1776,2606,2674,2680,2740,2762,2786,3118,3162,3186,3192,3228,3252,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4150 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4150 3192 4
  · have he : independentCachedBranchMembers4150.erase 3192=independentCachedBranchMembers4148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4148
  · have he : independentCachedBranchMembers4150.filter (independentCachedEdge 3192)=independentCachedBranchMembers4149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4149
def independentCachedBranchMembers4151 : Finset ℕ := ([66,1596,1678,1746,2680,2762,2786,3118,3162,3186,3228,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4151 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4151 4 (fun x => (if x<2786 then (if x<1746 then (if x<1596 then 0 else (if x<1678 then 0 else 1)) else (if x<2680 then 1 else (if x<2762 then 2 else 0))) else (if x<3186 then (if x<3118 then 2 else (if x<3162 then 1 else 3)) else (if x<3252 then (if x<3228 then 1 else 3) else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4152 : Finset ℕ := ([66,250,1590,1596,1642,1678,1708,1746,1752,1776,2606,2674,2680,2740,2762,2786,2792,3118,3162,3186,3192,3228,3252,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4152 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4152 2792 4
  · have he : independentCachedBranchMembers4152.erase 2792=independentCachedBranchMembers4150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4150
  · have he : independentCachedBranchMembers4152.filter (independentCachedEdge 2792)=independentCachedBranchMembers4151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4151
def independentCachedBranchMembers4153 : Finset ℕ := ([250,1590,1746,1776,2674,2740,2786,3118,3162,3228,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4153 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4153 4 (fun x => (if x<2786 then (if x<1776 then (if x<1590 then 0 else (if x<1746 then 1 else 0)) else (if x<2674 then 1 else (if x<2740 then 0 else 1))) else (if x<3228 then (if x<3118 then 2 else (if x<3162 then 3 else 0)) else (if x<3274 then 2 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4154 : Finset ℕ := ([1590,1746,2740,2786,3162,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4154 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4154 3 (fun x => (if x<2786 then (if x<1746 then 0 else (if x<2740 then 0 else 1)) else (if x<3162 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4155 : Finset ℕ := ([250,1590,1746,1776,2674,2740,2786,3118,3162,3192,3228,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4155 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4155 3192 3
  · have he : independentCachedBranchMembers4155.erase 3192=independentCachedBranchMembers4153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4153
  · have he : independentCachedBranchMembers4155.filter (independentCachedEdge 3192)=independentCachedBranchMembers4154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4154
def independentCachedBranchMembers4156 : Finset ℕ := ([66,250,1590,1596,1642,1678,1708,1746,1752,1776,2606,2674,2680,2716,2740,2762,2786,2792,3118,3162,3186,3192,3228,3252,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4156 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4156 2716 4
  · have he : independentCachedBranchMembers4156.erase 2716=independentCachedBranchMembers4152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4152
  · have he : independentCachedBranchMembers4156.filter (independentCachedEdge 2716)=independentCachedBranchMembers4155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4155
def independentCachedBranchMembers4157 : Finset ℕ := ([1590,1596,1678,1776,2674,2680,2740,2762,3118,3162,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4157 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4157 4 (fun x => (if x<2740 then (if x<1776 then (if x<1596 then 0 else (if x<1678 then 1 else 0)) else (if x<2674 then 1 else (if x<2680 then 0 else 1))) else (if x<3162 then (if x<2762 then 1 else (if x<3118 then 0 else 2)) else (if x<3298 then (if x<3228 then 2 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4158 : Finset ℕ := ([66,250,1590,1596,1642,1678,1708,1746,1752,1776,2606,2650,2674,2680,2716,2740,2762,2786,2792,3118,3162,3186,3192,3228,3252,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4158 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4158 2650 4
  · have he : independentCachedBranchMembers4158.erase 2650=independentCachedBranchMembers4156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4156
  · have he : independentCachedBranchMembers4158.filter (independentCachedEdge 2650)=independentCachedBranchMembers4157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4157
def independentCachedBranchMembers4159 : Finset ℕ := ([66,250,1590,1678,1708,1752,2674,2716,2762,2792,3186,3228,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4159 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4159 4 (fun x => (if x<2716 then (if x<1678 then (if x<250 then 0 else (if x<1590 then 0 else 1)) else (if x<1752 then (if x<1708 then 1 else 2) else (if x<2674 then 2 else 0))) else (if x<3186 then (if x<2762 then 2 else (if x<2792 then 0 else 2)) else (if x<3274 then (if x<3228 then 1 else 3) else (if x<3304 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
