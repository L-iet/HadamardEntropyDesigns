/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch39
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4064 : Finset ℕ := ([36,80,192,250,1590,1626,1746,1776,2606,2650,2680,2716,2762,2770,2792,2800,3102,3132,3186,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound4064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4064 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4064 5 (fun x => (if x<2716 then (if x<1626 then (if x<192 then (if x<80 then 0 else 0) else (if x<250 then 1 else (if x<1590 then 1 else 2))) else (if x<2606 then (if x<1746 then 0 else (if x<1776 then 1 else 2)) else (if x<2650 then 2 else (if x<2680 then 3 else 4)))) else (if x<3102 then (if x<2770 then (if x<2762 then 3 else 1) else (if x<2792 then 0 else (if x<2800 then 2 else 1))) else (if x<3244 then (if x<3132 then 2 else (if x<3186 then 4 else 3)) else (if x<3252 then 0 else (if x<3288 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4065 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2650,2674,2680,2716,2732,2740,2762,2770,2786,2792,2800,3102,3118,3132,3186,3228,3238,3244,3252,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4065 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4065 3228 5
  · have he : independentCachedBranchMembers4065.erase 3228=independentCachedBranchMembers4063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4063
  · have he : independentCachedBranchMembers4065.filter (independentCachedEdge 3228)=independentCachedBranchMembers4064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4064
def independentCachedBranchMembers4066 : Finset ℕ := ([12,36,66,192,1590,1708,1746,1762,2606,2680,2716,2732,2740,2762,2770,2786,3132,3186,3238,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4066 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4066 5 (fun x => (if x<2732 then (if x<1708 then (if x<66 then (if x<36 then 0 else 1) else (if x<192 then 0 else (if x<1590 then 1 else 1))) else (if x<2606 then (if x<1746 then 0 else (if x<1762 then 1 else 0)) else (if x<2680 then 1 else (if x<2716 then 2 else 0)))) else (if x<3132 then (if x<2762 then (if x<2740 then 2 else 3) else (if x<2770 then 1 else (if x<2786 then 0 else 2))) else (if x<3288 then (if x<3186 then 0 else (if x<3238 then 0 else 2)) else (if x<3304 then 1 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4067 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2650,2674,2680,2716,2732,2740,2762,2770,2786,2792,2800,3102,3118,3132,3186,3192,3228,3238,3244,3252,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4067 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4067 3192 5
  · have he : independentCachedBranchMembers4067.erase 3192=independentCachedBranchMembers4065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4065
  · have he : independentCachedBranchMembers4067.filter (independentCachedEdge 3192)=independentCachedBranchMembers4066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4066
def independentCachedBranchMembers4068 : Finset ℕ := ([12,66,1596,1642,1678,1708,1752,1762,2606,2650,2680,2716,2762,2770,2792,2800,3102,3132,3186,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound4068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4068 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4068 5 (fun x => (if x<2716 then (if x<1708 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1642 then 0 else (if x<1678 then 1 else 1))) else (if x<2606 then (if x<1752 then 2 else (if x<1762 then 1 else 2)) else (if x<2650 then 1 else (if x<2680 then 3 else 1)))) else (if x<3102 then (if x<2770 then (if x<2762 then 0 else 1) else (if x<2792 then 0 else (if x<2800 then 2 else 3))) else (if x<3244 then (if x<3132 then 3 else (if x<3186 then 4 else 3)) else (if x<3252 then 0 else (if x<3288 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4069 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3132,3186,3192,3228,3238,3244,3252,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4069 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4069 2776 5
  · have he : independentCachedBranchMembers4069.erase 2776=independentCachedBranchMembers4067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4067
  · have he : independentCachedBranchMembers4069.filter (independentCachedEdge 2776)=independentCachedBranchMembers4068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4068
def independentCachedBranchMembers4070 : Finset ℕ := ([80,250,1596,1626,1642,1678,1752,1776,2606,2680,2716,2732,2740,2762,2770,2786,3132,3186,3238,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4070 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4070 5 (fun x => (if x<2732 then (if x<1678 then (if x<1596 then (if x<250 then 0 else 0) else (if x<1626 then 1 else (if x<1642 then 0 else 1))) else (if x<2606 then (if x<1752 then 1 else (if x<1776 then 1 else 0)) else (if x<2680 then 1 else (if x<2716 then 0 else 1)))) else (if x<3132 then (if x<2762 then (if x<2740 then 2 else 3) else (if x<2770 then 1 else (if x<2786 then 0 else 2))) else (if x<3288 then (if x<3186 then 2 else (if x<3238 then 0 else 2)) else (if x<3304 then 0 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4071 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2620,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3132,3186,3192,3228,3238,3244,3252,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4071 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4071 2620 5
  · have he : independentCachedBranchMembers4071.erase 2620=independentCachedBranchMembers4069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4069
  · have he : independentCachedBranchMembers4071.filter (independentCachedEdge 2620)=independentCachedBranchMembers4070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4070
def independentCachedBranchMembers4072 : Finset ℕ := ([36,80,1590,1626,1678,1708,1752,1762,2606,2650,2680,2732,2740,2776,2786,3102,3132,3186,3228,3238,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4072 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4072 5 (fun x => (if x<2740 then (if x<1752 then (if x<1626 then (if x<80 then 0 else (if x<1590 then 0 else 1)) else (if x<1678 then 0 else (if x<1708 then 1 else 2))) else (if x<2650 then (if x<1762 then 2 else (if x<2606 then 1 else 2)) else (if x<2680 then 2 else (if x<2732 then 3 else 0)))) else (if x<3228 then (if x<3102 then (if x<2776 then 3 else (if x<2786 then 0 else 3)) else (if x<3132 then 1 else (if x<3186 then 3 else 1))) else (if x<3282 then (if x<3238 then 4 else (if x<3274 then 0 else 1)) else (if x<3304 then 0 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4073 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2620,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3132,3186,3192,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4073 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4073 3298 5
  · have he : independentCachedBranchMembers4073.erase 3298=independentCachedBranchMembers4071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4071
  · have he : independentCachedBranchMembers4073.filter (independentCachedEdge 3298)=independentCachedBranchMembers4072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4072
def independentCachedBranchMembers4074 : Finset ℕ := ([12,192,1590,1596,1626,1678,1762,1776,2606,2620,2650,2716,2786,2792,2800,3102,3186,3192,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound4074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4074 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4074 5 (fun x => (if x<2786 then (if x<1762 then (if x<1596 then (if x<192 then 0 else (if x<1590 then 0 else 1)) else (if x<1626 then 0 else (if x<1678 then 1 else 1))) else (if x<2620 then (if x<1776 then 1 else (if x<2606 then 0 else 0)) else (if x<2650 then 2 else (if x<2716 then 2 else 3)))) else (if x<3238 then (if x<3102 then (if x<2792 then 0 else (if x<2800 then 2 else 3)) else (if x<3186 then 0 else (if x<3192 then 1 else 2))) else (if x<3274 then (if x<3244 then 1 else (if x<3252 then 2 else 3)) else (if x<3282 then 1 else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4075 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2620,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3132,3162,3186,3192,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4075 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4075 3162 5
  · have he : independentCachedBranchMembers4075.erase 3162=independentCachedBranchMembers4073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4073
  · have he : independentCachedBranchMembers4075.filter (independentCachedEdge 3162)=independentCachedBranchMembers4074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4074
def independentCachedBranchMembers4076 : Finset ℕ := ([12,36,80,192,1590,1596,1642,1678,1708,1746,1752,1776,2620,2732,2776,2800,3118,3162,3186,3192,3228,3252,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4076 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4076 5 (fun x => (if x<2620 then (if x<1642 then (if x<192 then (if x<36 then 0 else (if x<80 then 1 else 0)) else (if x<1590 then 1 else (if x<1596 then 1 else 2))) else (if x<1746 then (if x<1678 then 2 else (if x<1708 then 0 else 3)) else (if x<1752 then 0 else (if x<1776 then 2 else 3)))) else (if x<3186 then (if x<2800 then (if x<2732 then 1 else (if x<2776 then 0 else 1)) else (if x<3118 then 0 else (if x<3162 then 0 else 4))) else (if x<3252 then (if x<3192 then 0 else (if x<3228 then 2 else 2)) else (if x<3298 then (if x<3274 then 3 else 1) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4077 : Finset ℕ := ([1590,1642,1678,1746,2620,2732,2776,2800,3192,3228,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4077 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4077 4 (fun x => (if x<2776 then (if x<1746 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<2620 then 0 else (if x<2732 then 1 else 2))) else (if x<3228 then (if x<2800 then 1 else (if x<3192 then 2 else 1)) else (if x<3252 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4078 : Finset ℕ := ([12,36,80,192,1590,1596,1642,1678,1708,1746,1752,1776,2620,2732,2770,2776,2800,3118,3162,3186,3192,3228,3252,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4078 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4078 2770 4
  · have he : independentCachedBranchMembers4078.erase 2770=independentCachedBranchMembers4076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4076
  · have he : independentCachedBranchMembers4078.filter (independentCachedEdge 2770)=independentCachedBranchMembers4077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4077
def independentCachedBranchMembers4079 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2620,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3132,3162,3178,3186,3192,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4079 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4079 3178 5
  · have he : independentCachedBranchMembers4079.erase 3178=independentCachedBranchMembers4075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4075
  · have he : independentCachedBranchMembers4079.filter (independentCachedEdge 3178)=independentCachedBranchMembers4078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4078
def independentCachedBranchMembers4080 : Finset ℕ := ([12,80,1596,1642,1678,1746,1752,2606,2680,2716,2732,2800,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4080 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4080 5 (fun x => (if x<2732 then (if x<1746 then (if x<1596 then (if x<80 then 0 else 0) else (if x<1642 then 1 else (if x<1678 then 1 else 0))) else (if x<2606 then (if x<1752 then 0 else 1) else (if x<2680 then 0 else (if x<2716 then 1 else 1)))) else (if x<3192 then (if x<3102 then (if x<2800 then 2 else 2) else (if x<3118 then 3 else (if x<3186 then 2 else 2))) else (if x<3244 then (if x<3228 then 3 else (if x<3238 then 4 else 4)) else (if x<3274 then 0 else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4081 : Finset ℕ := ([80,1596,1642,1746,2606,2680,2732,3118,3192,3244] : List ℕ).toFinset
theorem independentCachedBranchBound4081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4081 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4081 4 (fun x => (if x<2680 then (if x<1642 then (if x<1596 then 0 else 1) else (if x<1746 then 1 else (if x<2606 then 0 else 0))) else (if x<3118 then (if x<2732 then 1 else 2) else (if x<3192 then 2 else (if x<3244 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4082 : Finset ℕ := ([12,80,1596,1642,1678,1746,1752,1762,2606,2680,2716,2732,2800,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4082 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4082 1762 4
  · have he : independentCachedBranchMembers4082.erase 1762=independentCachedBranchMembers4080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4080
  · have he : independentCachedBranchMembers4082.filter (independentCachedEdge 1762)=independentCachedBranchMembers4081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4081
def independentCachedBranchMembers4083 : Finset ℕ := ([12,1642,1746,1752,2606,2716,2800,3118,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4083 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4083 4 (fun x => (if x<2716 then (if x<1746 then (if x<1642 then 0 else 1) else (if x<1752 then 0 else (if x<2606 then 1 else 0))) else (if x<3118 then (if x<2800 then 1 else 2) else (if x<3228 then 2 else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4084 : Finset ℕ := ([12,80,1596,1626,1642,1678,1746,1752,1762,2606,2680,2716,2732,2800,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4084 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4084 1626 4
  · have he : independentCachedBranchMembers4084.erase 1626=independentCachedBranchMembers4082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4082
  · have he : independentCachedBranchMembers4084.filter (independentCachedEdge 1626)=independentCachedBranchMembers4083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4083
def independentCachedBranchMembers4085 : Finset ℕ := ([12,80,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4085 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4085 4 (fun x => (if x<3192 then (if x<3102 then (if x<80 then 0 else 0) else (if x<3118 then 1 else (if x<3186 then 0 else 0))) else (if x<3244 then (if x<3228 then 1 else (if x<3238 then 2 else 2)) else (if x<3274 then 1 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4086 : Finset ℕ := ([12,80,1596,1626,1642,1678,1746,1752,1762,2606,2680,2716,2732,2762,2800,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4086 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4086 2762 4
  · have he : independentCachedBranchMembers4086.erase 2762=independentCachedBranchMembers4084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4084
  · have he : independentCachedBranchMembers4086.filter (independentCachedEdge 2762)=independentCachedBranchMembers4085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4085
def independentCachedBranchMembers4087 : Finset ℕ := ([1596,1752,2680,2716,2732,2800,3102,3118,3186,3238,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4087 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4087 4 (fun x => (if x<2800 then (if x<2680 then (if x<1752 then 0 else 0) else (if x<2716 then 0 else (if x<2732 then 0 else 1))) else (if x<3186 then (if x<3102 then 1 else (if x<3118 then 2 else 1)) else (if x<3238 then 1 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4088 : Finset ℕ := ([12,80,1596,1626,1642,1678,1746,1752,1762,2606,2674,2680,2716,2732,2762,2800,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4088 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4088 2674 4
  · have he : independentCachedBranchMembers4088.erase 2674=independentCachedBranchMembers4086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4086
  · have he : independentCachedBranchMembers4088.filter (independentCachedEdge 2674)=independentCachedBranchMembers4087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4087
def independentCachedBranchMembers4089 : Finset ℕ := ([12,80,1596,1752,2680,2716,2732,2800,3192,3228,3244,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4089 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4089 4 (fun x => (if x<2732 then (if x<1752 then (if x<80 then 0 else (if x<1596 then 0 else 1)) else (if x<2680 then 1 else (if x<2716 then 1 else 1))) else (if x<3228 then (if x<2800 then 0 else (if x<3192 then 0 else 2)) else (if x<3244 then 2 else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4090 : Finset ℕ := ([12,80,1590,1596,1626,1642,1678,1746,1752,1762,2606,2674,2680,2716,2732,2762,2800,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4090 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4090 1590 4
  · have he : independentCachedBranchMembers4090.erase 1590=independentCachedBranchMembers4088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4088
  · have he : independentCachedBranchMembers4090.filter (independentCachedEdge 1590)=independentCachedBranchMembers4089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4089
def independentCachedBranchMembers4091 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1738,1746,1752,1762,1776,2606,2620,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3132,3162,3178,3186,3192,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4091 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4091 1738 5
  · have he : independentCachedBranchMembers4091.erase 1738=independentCachedBranchMembers4079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4079
  · have he : independentCachedBranchMembers4091.filter (independentCachedEdge 1738)=independentCachedBranchMembers4090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4090
def independentCachedBranchMembers4092 : Finset ℕ := ([36,192,1590,1626,1642,1708,1746,1762,1776,2606,2740,2762,2776,2792,3102,3118,3132,3186,3238,3252,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4092 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4092 5 (fun x => (if x<2762 then (if x<1708 then (if x<1590 then (if x<192 then 0 else 0) else (if x<1626 then 0 else (if x<1642 then 1 else 2))) else (if x<1776 then (if x<1746 then 2 else (if x<1762 then 0 else 1)) else (if x<2606 then 2 else (if x<2740 then 0 else 2)))) else (if x<3186 then (if x<3102 then (if x<2776 then 0 else (if x<2792 then 3 else 2)) else (if x<3118 then 1 else (if x<3132 then 3 else 0))) else (if x<3274 then (if x<3238 then 1 else (if x<3252 then 1 else 4)) else (if x<3288 then 1 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4093 : Finset ℕ := ([36,192,3102,3118,3132,3186,3238,3252,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4093 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4093 4 (fun x => (if x<3186 then (if x<3102 then (if x<192 then 0 else 0) else (if x<3118 then 1 else (if x<3132 then 0 else 2))) else (if x<3274 then (if x<3238 then 1 else (if x<3252 then 1 else 3)) else (if x<3288 then 0 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4094 : Finset ℕ := ([36,192,1590,1626,1642,1708,1746,1762,1776,2606,2674,2740,2762,2776,2792,3102,3118,3132,3186,3238,3252,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4094 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4094 2674 4
  · have he : independentCachedBranchMembers4094.erase 2674=independentCachedBranchMembers4092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4092
  · have he : independentCachedBranchMembers4094.filter (independentCachedEdge 2674)=independentCachedBranchMembers4093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4093
def independentCachedBranchMembers4095 : Finset ℕ := ([1626,1642,1776,2606,2740,2762,3132,3186,3238,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4095 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4095 4 (fun x => (if x<2762 then (if x<1776 then (if x<1642 then 0 else 1) else (if x<2606 then 0 else (if x<2740 then 1 else 0))) else (if x<3238 then (if x<3132 then 1 else (if x<3186 then 2 else 2)) else (if x<3288 then 2 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
