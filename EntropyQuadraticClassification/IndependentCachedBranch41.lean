/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch40
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4096 : Finset ℕ := ([36,192,1590,1626,1642,1708,1746,1762,1776,2606,2620,2674,2740,2762,2776,2792,3102,3118,3132,3186,3238,3252,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4096 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4096 2620 4
  · have he : independentCachedBranchMembers4096.erase 2620=independentCachedBranchMembers4094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4094
  · have he : independentCachedBranchMembers4096.filter (independentCachedEdge 2620)=independentCachedBranchMembers4095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4095
def independentCachedBranchMembers4097 : Finset ℕ := ([36,192,1708,1776,2620,2740,2776,2792,3132,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4097 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4097 4 (fun x => (if x<2776 then (if x<1776 then (if x<192 then 0 else (if x<1708 then 0 else 1)) else (if x<2620 then 1 else (if x<2740 then 0 else 1))) else (if x<3252 then (if x<2792 then 0 else (if x<3132 then 1 else 2)) else (if x<3288 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4098 : Finset ℕ := ([36,192,1590,1626,1642,1678,1708,1746,1762,1776,2606,2620,2674,2740,2762,2776,2792,3102,3118,3132,3186,3238,3252,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4098 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4098 1678 4
  · have he : independentCachedBranchMembers4098.erase 1678=independentCachedBranchMembers4096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4096
  · have he : independentCachedBranchMembers4098.filter (independentCachedEdge 1678)=independentCachedBranchMembers4097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4097
def independentCachedBranchMembers4099 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1650,1678,1708,1738,1746,1752,1762,1776,2606,2620,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3132,3162,3178,3186,3192,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4099 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4099 1650 5
  · have he : independentCachedBranchMembers4099.erase 1650=independentCachedBranchMembers4091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4091
  · have he : independentCachedBranchMembers4099.filter (independentCachedEdge 1650)=independentCachedBranchMembers4098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4098
def independentCachedBranchMembers4100 : Finset ℕ := ([12,66,192,250,1590,1626,1678,1708,1752,1762,2620,2674,2716,2762,2770,2792,2800,3102,3132,3178,3186,3228,3238,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4100 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4100 5 (fun x => (if x<2762 then (if x<1678 then (if x<250 then (if x<66 then 0 else (if x<192 then 0 else 1)) else (if x<1590 then 1 else (if x<1626 then 2 else 2))) else (if x<1762 then (if x<1708 then 2 else (if x<1752 then 0 else 1)) else (if x<2674 then (if x<2620 then 0 else 0) else (if x<2716 then 0 else 3)))) else (if x<3186 then (if x<2800 then (if x<2770 then 1 else (if x<2792 then 3 else 3)) else (if x<3132 then (if x<3102 then 1 else 2) else (if x<3178 then 4 else 4))) else (if x<3274 then (if x<3228 then 2 else (if x<3238 then 0 else 2)) else (if x<3304 then (if x<3282 then 2 else 0) else (if x<3312 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4101 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1650,1678,1702,1708,1738,1746,1752,1762,1776,2606,2620,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3132,3162,3178,3186,3192,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4101 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4101 1702 5
  · have he : independentCachedBranchMembers4101.erase 1702=independentCachedBranchMembers4099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4099
  · have he : independentCachedBranchMembers4101.filter (independentCachedEdge 1702)=independentCachedBranchMembers4100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4100
def independentCachedBranchMembers4102 : Finset ℕ := ([36,66,192,250,1590,1596,1626,1642,1678,1746,1752,1762,2740,2770,2776,2786,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4102 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4102 5 (fun x => (if x<2740 then (if x<1626 then (if x<250 then (if x<66 then 0 else (if x<192 then 0 else 1)) else (if x<1590 then 1 else (if x<1596 then 2 else 0))) else (if x<1746 then (if x<1642 then 0 else (if x<1678 then 2 else 2)) else (if x<1752 then 1 else (if x<1762 then 3 else 3)))) else (if x<3186 then (if x<2786 then (if x<2770 then 0 else (if x<2776 then 0 else 1)) else (if x<3102 then 1 else (if x<3118 then 4 else 2))) else (if x<3238 then (if x<3192 then 2 else (if x<3228 then 4 else 3)) else (if x<3274 then (if x<3244 then 3 else 0) else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4103 : Finset ℕ := ([36,66,1596,1626,1678,1746,2776,2786,3118,3186,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4103 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4103 4 (fun x => (if x<2776 then (if x<1626 then (if x<66 then 0 else (if x<1596 then 0 else 0)) else (if x<1678 then 0 else (if x<1746 then 1 else 1))) else (if x<3186 then (if x<2786 then 2 else (if x<3118 then 2 else 1)) else (if x<3228 then 1 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4104 : Finset ℕ := ([36,66,192,250,1590,1596,1626,1642,1678,1746,1752,1762,2740,2770,2776,2786,2792,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4104 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4104 2792 4
  · have he : independentCachedBranchMembers4104.erase 2792=independentCachedBranchMembers4102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4102
  · have he : independentCachedBranchMembers4104.filter (independentCachedEdge 2792)=independentCachedBranchMembers4103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4103
def independentCachedBranchMembers4105 : Finset ℕ := ([192,1590,1596,1626,1678,1762,2740,2770,2776,3118,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4105 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4105 4 (fun x => (if x<2740 then (if x<1626 then (if x<1590 then 0 else (if x<1596 then 0 else 1)) else (if x<1678 then 1 else (if x<1762 then 1 else 0))) else (if x<3118 then (if x<2770 then 2 else (if x<2776 then 2 else 3)) else (if x<3228 then 3 else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4106 : Finset ℕ := ([36,66,192,250,1590,1596,1626,1642,1678,1746,1752,1762,2650,2740,2770,2776,2786,2792,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4106 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4106 2650 4
  · have he : independentCachedBranchMembers4106.erase 2650=independentCachedBranchMembers4104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4104
  · have he : independentCachedBranchMembers4106.filter (independentCachedEdge 2650)=independentCachedBranchMembers4105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4105
def independentCachedBranchMembers4107 : Finset ℕ := ([250,1596,1626,1642,1678,1752,2740,2770,2786,3186,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4107 4 (fun x => (if x<2740 then (if x<1642 then (if x<1596 then 0 else (if x<1626 then 1 else 0)) else (if x<1678 then 1 else (if x<1752 then 1 else 1))) else (if x<3186 then (if x<2770 then 2 else (if x<2786 then 0 else 2)) else (if x<3238 then 0 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4108 : Finset ℕ := ([36,66,192,250,1590,1596,1626,1642,1678,1746,1752,1762,2620,2650,2740,2770,2776,2786,2792,3102,3118,3186,3192,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4108 2620 4
  · have he : independentCachedBranchMembers4108.erase 2620=independentCachedBranchMembers4106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4106
  · have he : independentCachedBranchMembers4108.filter (independentCachedEdge 2620)=independentCachedBranchMembers4107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4107
def independentCachedBranchMembers4109 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1650,1678,1702,1708,1738,1746,1752,1762,1776,2606,2620,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4109 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4109 3214 5
  · have he : independentCachedBranchMembers4109.erase 3214=independentCachedBranchMembers4101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4101
  · have he : independentCachedBranchMembers4109.filter (independentCachedEdge 3214)=independentCachedBranchMembers4108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4108
def independentCachedBranchMembers4110 : Finset ℕ := ([12,66,80,250,1590,1626,1642,1678,1708,1746,1762,1776,2650,2680,2716,2732,2770,2786,2800,3102,3118,3132,3186,3238,3252,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4110 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4110 5 (fun x => (if x<2716 then (if x<1678 then (if x<250 then (if x<66 then 0 else (if x<80 then 0 else 1)) else (if x<1626 then (if x<1590 then 1 else 2) else (if x<1642 then 1 else 2))) else (if x<1762 then (if x<1708 then 2 else (if x<1746 then 0 else 2)) else (if x<2650 then (if x<1776 then 0 else 1) else (if x<2680 then 3 else 1)))) else (if x<3132 then (if x<2786 then (if x<2732 then 0 else (if x<2770 then 4 else 0)) else (if x<3102 then (if x<2800 then 3 else 4) else (if x<3118 then 3 else 2))) else (if x<3252 then (if x<3186 then 0 else (if x<3238 then 0 else 3)) else (if x<3288 then (if x<3274 then 4 else 2) else (if x<3304 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4111 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1650,1678,1702,1708,1738,1746,1752,1762,1776,2606,2620,2650,2674,2680,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4111 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4111 3126 5
  · have he : independentCachedBranchMembers4111.erase 3126=independentCachedBranchMembers4109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4109
  · have he : independentCachedBranchMembers4111.filter (independentCachedEdge 3126)=independentCachedBranchMembers4110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4110
def independentCachedBranchMembers4112 : Finset ℕ := ([12,36,66,80,192,250,1596,1650,1708,1738,1752,1776,2680,2716,2740,2770,2792,3132,3162,3186,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4112 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4112 5 (fun x => (if x<2680 then (if x<1596 then (if x<80 then (if x<36 then 0 else (if x<66 then 1 else 0)) else (if x<192 then 1 else (if x<250 then 2 else 2))) else (if x<1738 then (if x<1650 then 0 else (if x<1708 then 0 else 1)) else (if x<1752 then 2 else (if x<1776 then 1 else 2)))) else (if x<3162 then (if x<2770 then (if x<2716 then 3 else (if x<2740 then 0 else 3)) else (if x<2792 then 0 else (if x<3132 then 2 else 3))) else (if x<3274 then (if x<3186 then 1 else (if x<3244 then 4 else 0)) else (if x<3298 then (if x<3288 then 4 else 2) else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4113 : Finset ℕ := ([36,80,1596,1650,1738,1776,2680,2740,3162,3244,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4113 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4113 4 (fun x => (if x<2680 then (if x<1650 then (if x<80 then 0 else (if x<1596 then 0 else 1)) else (if x<1738 then 1 else (if x<1776 then 2 else 2))) else (if x<3244 then (if x<2740 then 1 else (if x<3162 then 2 else 0)) else (if x<3288 then 3 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4114 : Finset ℕ := ([12,36,66,80,192,250,1596,1650,1708,1738,1752,1762,1776,2680,2716,2740,2770,2792,3132,3162,3186,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4114 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4114 1762 4
  · have he : independentCachedBranchMembers4114.erase 1762=independentCachedBranchMembers4112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4112
  · have he : independentCachedBranchMembers4114.filter (independentCachedEdge 1762)=independentCachedBranchMembers4113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4113
def independentCachedBranchMembers4115 : Finset ℕ := ([12,192,1650,1708,1738,1752,2716,2792,3132,3162,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4115 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4115 4 (fun x => (if x<2716 then (if x<1708 then (if x<192 then 0 else (if x<1650 then 0 else 1)) else (if x<1738 then 2 else (if x<1752 then 1 else 2))) else (if x<3162 then (if x<2792 then 2 else (if x<3132 then 2 else 0)) else (if x<3298 then 1 else (if x<3312 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4116 : Finset ℕ := ([12,36,66,80,192,250,1596,1626,1650,1708,1738,1752,1762,1776,2680,2716,2740,2770,2792,3132,3162,3186,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4116 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4116 1626 4
  · have he : independentCachedBranchMembers4116.erase 1626=independentCachedBranchMembers4114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4114
  · have he : independentCachedBranchMembers4116.filter (independentCachedEdge 1626)=independentCachedBranchMembers4115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4115
def independentCachedBranchMembers4117 : Finset ℕ := ([66,250,1626,1650,1738,1762,2680,2716,2740,2792,3132,3244,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4117 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4117 4 (fun x => (if x<2716 then (if x<1650 then (if x<250 then 0 else (if x<1626 then 0 else 0)) else (if x<1762 then (if x<1738 then 1 else 1) else (if x<2680 then 0 else 2))) else (if x<3132 then (if x<2740 then 2 else (if x<2792 then 3 else 3)) else (if x<3288 then (if x<3244 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4118 : Finset ℕ := ([12,36,66,80,192,250,1596,1626,1650,1708,1738,1752,1762,1776,2680,2716,2740,2770,2792,3118,3132,3162,3186,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4118 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4118 3118 4
  · have he : independentCachedBranchMembers4118.erase 3118=independentCachedBranchMembers4116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4116
  · have he : independentCachedBranchMembers4118.filter (independentCachedEdge 3118)=independentCachedBranchMembers4117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4117
def independentCachedBranchMembers4119 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1650,1678,1702,1708,1738,1746,1752,1762,1776,2606,2620,2650,2674,2680,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4119 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4119 2710 5
  · have he : independentCachedBranchMembers4119.erase 2710=independentCachedBranchMembers4111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4111
  · have he : independentCachedBranchMembers4119.filter (independentCachedEdge 2710)=independentCachedBranchMembers4118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4118
def independentCachedBranchMembers4120 : Finset ℕ := ([12,36,66,80,1590,1642,1708,1738,1752,1762,1776,2606,2620,2650,2674,2740,2770,2792,3118,3132,3162,3186,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4120 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4120 5 (fun x => (if x<2650 then (if x<1708 then (if x<80 then (if x<36 then 0 else (if x<66 then 1 else 0)) else (if x<1590 then 1 else (if x<1642 then 2 else 2))) else (if x<1762 then (if x<1738 then 0 else (if x<1752 then 3 else 1)) else (if x<2606 then (if x<1776 then 0 else 2) else (if x<2620 then 1 else 0)))) else (if x<3162 then (if x<2770 then (if x<2674 then 1 else (if x<2740 then 0 else 2)) else (if x<3118 then (if x<2792 then 3 else 2) else (if x<3132 then 4 else 3))) else (if x<3238 then (if x<3186 then 3 else (if x<3228 then 4 else 0)) else (if x<3282 then (if x<3252 then 1 else 4) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4121 : Finset ℕ := ([36,80,1590,1738,1776,2620,2674,2740,3118,3162,3228,3238,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4121 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4121 4 (fun x => (if x<2740 then (if x<1738 then (if x<80 then 0 else (if x<1590 then 0 else 1)) else (if x<2620 then (if x<1776 then 2 else 1) else (if x<2674 then 2 else 1))) else (if x<3228 then (if x<3118 then 1 else (if x<3162 then 0 else 0)) else (if x<3282 then (if x<3238 then 3 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4122 : Finset ℕ := ([12,36,66,80,1590,1642,1708,1738,1752,1762,1776,2606,2620,2650,2674,2716,2740,2770,2792,3118,3132,3162,3186,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4122 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4122 2716 4
  · have he : independentCachedBranchMembers4122.erase 2716=independentCachedBranchMembers4120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4120
  · have he : independentCachedBranchMembers4122.filter (independentCachedEdge 2716)=independentCachedBranchMembers4121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4121
def independentCachedBranchMembers4123 : Finset ℕ := ([36,66,1590,1642,1752,1762,2740,2770,2792,3118,3186,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4123 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4123 4 (fun x => (if x<2740 then (if x<1642 then (if x<66 then 0 else (if x<1590 then 0 else 1)) else (if x<1752 then 1 else (if x<1762 then 2 else 2))) else (if x<3118 then (if x<2770 then 0 else (if x<2792 then 0 else 1)) else (if x<3228 then (if x<3186 then 3 else 3) else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4124 : Finset ℕ := ([1590,1762,2740,2770,3118,3228] : List ℕ).toFinset
theorem independentCachedBranchBound4124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4124 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4124 3 (fun x => (if x<2770 then (if x<1762 then 0 else (if x<2740 then 0 else 1)) else (if x<3118 then 1 else (if x<3228 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4125 : Finset ℕ := ([36,66,1590,1642,1752,1762,2650,2740,2770,2792,3118,3186,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4125 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4125 2650 3
  · have he : independentCachedBranchMembers4125.erase 2650=independentCachedBranchMembers4123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4123
  · have he : independentCachedBranchMembers4125.filter (independentCachedEdge 2650)=independentCachedBranchMembers4124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4124
def independentCachedBranchMembers4126 : Finset ℕ := ([1642,1752,2740,2770,3186,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4126 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4126 3 (fun x => (if x<2770 then (if x<1752 then 0 else (if x<2740 then 0 else 1)) else (if x<3186 then 1 else (if x<3238 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4127 : Finset ℕ := ([36,66,1590,1642,1752,1762,2620,2650,2740,2770,2792,3118,3186,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4127 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4127 2620 3
  · have he : independentCachedBranchMembers4127.erase 2620=independentCachedBranchMembers4125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4125
  · have he : independentCachedBranchMembers4127.filter (independentCachedEdge 2620)=independentCachedBranchMembers4126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4126
end EntropyDesigns.QuadraticRefinement
