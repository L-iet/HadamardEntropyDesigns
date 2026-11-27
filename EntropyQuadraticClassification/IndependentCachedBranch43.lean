/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch42
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4160 : Finset ℕ := ([66,250,1590,1596,1642,1678,1702,1708,1746,1752,1776,2606,2650,2674,2680,2716,2740,2762,2786,2792,3118,3162,3186,3192,3228,3252,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4160 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4160 1702 4
  · have he : independentCachedBranchMembers4160.erase 1702=independentCachedBranchMembers4158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4158
  · have he : independentCachedBranchMembers4160.filter (independentCachedEdge 1702)=independentCachedBranchMembers4159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4159
def independentCachedBranchMembers4161 : Finset ℕ := ([66,250,1596,1708,1752,1776,2680,2716,2740,2792,3118,3162,3186,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4161 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4161 4 (fun x => (if x<2716 then (if x<1708 then (if x<250 then 0 else (if x<1596 then 0 else 1)) else (if x<1776 then (if x<1752 then 2 else 1) else (if x<2680 then 2 else 1))) else (if x<3162 then (if x<2792 then (if x<2740 then 1 else 2) else (if x<3118 then 2 else 3)) else (if x<3274 then (if x<3186 then 0 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4162 : Finset ℕ := ([66,250,1590,1596,1642,1678,1702,1708,1746,1752,1776,2606,2650,2674,2680,2710,2716,2740,2762,2786,2792,3118,3162,3186,3192,3228,3252,3274,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4162 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4162 2710 4
  · have he : independentCachedBranchMembers4162.erase 2710=independentCachedBranchMembers4160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4160
  · have he : independentCachedBranchMembers4162.filter (independentCachedEdge 2710)=independentCachedBranchMembers4161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4161
def independentCachedBranchMembers4163 : Finset ℕ := ([12,36,66,80,192,250,1582,1590,1596,1626,1642,1650,1678,1692,1702,1708,1738,1746,1752,1762,1768,1776,2606,2620,2650,2674,2680,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4163 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4163 1582 5
  · have he : independentCachedBranchMembers4163.erase 1582=independentCachedBranchMembers4139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4139
  · have he : independentCachedBranchMembers4163.filter (independentCachedEdge 1582)=independentCachedBranchMembers4162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4162
def independentCachedBranchMembers4164 : Finset ℕ := ([36,66,192,250,1590,1596,1626,1642,1678,1746,1752,1762,2606,2674,2680,2716,2732,2762,2800,3132,3162,3214,3252,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4164 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4164 5 (fun x => (if x<2674 then (if x<1626 then (if x<250 then (if x<66 then 0 else (if x<192 then 0 else 1)) else (if x<1590 then 1 else (if x<1596 then 2 else 0))) else (if x<1746 then (if x<1642 then 0 else (if x<1678 then 2 else 2)) else (if x<1762 then (if x<1752 then 1 else 3) else (if x<2606 then 3 else 2)))) else (if x<3162 then (if x<2732 then (if x<2680 then 2 else (if x<2716 then 4 else 3)) else (if x<2800 then (if x<2762 then 0 else 0) else (if x<3132 then 1 else 4))) else (if x<3282 then (if x<3214 then 4 else (if x<3252 then 4 else 0)) else (if x<3298 then (if x<3288 then 0 else 1) else (if x<3304 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4165 : Finset ℕ := ([36,192,1590,1596,1642,1678,1746,1752,2732,2800,3162,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4165 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4165 4 (fun x => (if x<1752 then (if x<1596 then (if x<192 then 0 else (if x<1590 then 0 else 0)) else (if x<1678 then (if x<1642 then 1 else 1) else (if x<1746 then 1 else 0))) else (if x<3162 then (if x<2732 then 1 else (if x<2800 then 2 else 2)) else (if x<3298 then (if x<3252 then 3 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4166 : Finset ℕ := ([36,66,192,250,1590,1596,1626,1642,1678,1746,1752,1762,2606,2674,2680,2716,2732,2762,2800,3132,3162,3178,3214,3252,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4166 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4166 3178 4
  · have he : independentCachedBranchMembers4166.erase 3178=independentCachedBranchMembers4164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4164
  · have he : independentCachedBranchMembers4166.filter (independentCachedEdge 3178)=independentCachedBranchMembers4165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4165
def independentCachedBranchMembers4167 : Finset ℕ := ([36,66,192,250,1596,1626,1752,1762,2680,2716,3132,3162,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4167 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4167 4 (fun x => (if x<1762 then (if x<250 then (if x<66 then 0 else (if x<192 then 0 else 1)) else (if x<1626 then (if x<1596 then 1 else 0) else (if x<1752 then 0 else 1))) else (if x<3132 then (if x<2680 then 1 else (if x<2716 then 2 else 2)) else (if x<3288 then (if x<3162 then 2 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4168 : Finset ℕ := ([36,66,192,250,1590,1596,1626,1642,1678,1746,1752,1762,2606,2674,2680,2710,2716,2732,2762,2800,3132,3162,3178,3214,3252,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4168 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4168 2710 4
  · have he : independentCachedBranchMembers4168.erase 2710=independentCachedBranchMembers4166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4166
  · have he : independentCachedBranchMembers4168.filter (independentCachedEdge 2710)=independentCachedBranchMembers4167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4167
def independentCachedBranchMembers4169 : Finset ℕ := ([36,66,1590,1642,1752,1762,2606,2674,2716,3132,3162,3214,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4169 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4169 4 (fun x => (if x<2674 then (if x<1642 then (if x<66 then 0 else (if x<1590 then 0 else 1)) else (if x<1762 then (if x<1752 then 1 else 2) else (if x<2606 then 2 else 1))) else (if x<3214 then (if x<3132 then (if x<2716 then 1 else 2) else (if x<3162 then 0 else 0)) else (if x<3282 then (if x<3252 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4170 : Finset ℕ := ([36,66,192,250,1590,1596,1626,1642,1678,1746,1752,1762,1768,2606,2674,2680,2710,2716,2732,2762,2800,3132,3162,3178,3214,3252,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4170 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4170 1768 4
  · have he : independentCachedBranchMembers4170.erase 1768=independentCachedBranchMembers4168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4168
  · have he : independentCachedBranchMembers4170.filter (independentCachedEdge 1768)=independentCachedBranchMembers4169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4169
def independentCachedBranchMembers4171 : Finset ℕ := ([66,250,1590,1626,1642,1678,1746,1762,2680,2716,2732,2800,3132,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4171 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4171 4 (fun x => (if x<2680 then (if x<1642 then (if x<1590 then (if x<250 then 0 else 0) else (if x<1626 then 1 else 0)) else (if x<1746 then (if x<1678 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3132 then (if x<2732 then (if x<2716 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3288 then (if x<3252 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4172 : Finset ℕ := ([36,66,192,250,1590,1596,1626,1642,1678,1746,1752,1762,1768,2606,2674,2680,2710,2716,2732,2762,2800,3126,3132,3162,3178,3214,3252,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4172 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4172 3126 4
  · have he : independentCachedBranchMembers4172.erase 3126=independentCachedBranchMembers4170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4170
  · have he : independentCachedBranchMembers4172.filter (independentCachedEdge 3126)=independentCachedBranchMembers4171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4171
def independentCachedBranchMembers4173 : Finset ℕ := ([12,36,66,80,192,250,1582,1590,1596,1626,1642,1650,1678,1692,1702,1708,1738,1746,1752,1762,1768,1776,2606,2620,2650,2674,2680,2702,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4173 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4173 2702 5
  · have he : independentCachedBranchMembers4173.erase 2702=independentCachedBranchMembers4163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4163
  · have he : independentCachedBranchMembers4173.filter (independentCachedEdge 2702)=independentCachedBranchMembers4172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4172
def independentCachedBranchMembers4174 : Finset ℕ := ([12,66,80,250,1590,1626,1642,1678,1708,1746,1762,1776,2606,2620,2674,2710,2740,2762,2776,2792,3126,3162,3178,3192,3228,3244,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4174 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4174 5 (fun x => (if x<2674 then (if x<1678 then (if x<250 then (if x<66 then 0 else (if x<80 then 0 else 1)) else (if x<1626 then (if x<1590 then 1 else 2) else (if x<1642 then 1 else 2))) else (if x<1762 then (if x<1708 then 2 else (if x<1746 then 0 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2620 then 2 else 0)))) else (if x<3162 then (if x<2762 then (if x<2710 then 0 else (if x<2740 then 2 else 3)) else (if x<2792 then (if x<2776 then 2 else 1) else (if x<3126 then 3 else 3))) else (if x<3244 then (if x<3192 then (if x<3178 then 4 else 3) else (if x<3228 then 1 else 0)) else (if x<3298 then (if x<3282 then 3 else 0) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4175 : Finset ℕ := ([80,250,1642,1678,1708,1762,2606,2762,2792,3126,3162,3192,3228,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4175 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4175 4 (fun x => (if x<2762 then (if x<1678 then (if x<250 then 0 else (if x<1642 then 0 else 1)) else (if x<1762 then (if x<1708 then 1 else 2) else (if x<2606 then 2 else 1))) else (if x<3192 then (if x<3126 then (if x<2792 then 1 else 2) else (if x<3162 then 3 else 0)) else (if x<3282 then (if x<3228 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4176 : Finset ℕ := ([12,66,80,250,1590,1626,1642,1678,1692,1708,1746,1762,1776,2606,2620,2674,2710,2740,2762,2776,2792,3126,3162,3178,3192,3228,3244,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4176 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4176 1692 4
  · have he : independentCachedBranchMembers4176.erase 1692=independentCachedBranchMembers4174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4174
  · have he : independentCachedBranchMembers4176.filter (independentCachedEdge 1692)=independentCachedBranchMembers4175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4175
def independentCachedBranchMembers4177 : Finset ℕ := ([66,250,1590,1626,1642,1678,1746,1762,2620,2740,2776,2792,3192,3228,3244,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4177 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4177 4 (fun x => (if x<2620 then (if x<1642 then (if x<1590 then (if x<250 then 0 else 0) else (if x<1626 then 1 else 0)) else (if x<1746 then (if x<1678 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3192 then (if x<2776 then (if x<2740 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3244 then (if x<3228 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4178 : Finset ℕ := ([12,66,80,250,1590,1626,1642,1678,1692,1708,1746,1762,1776,2606,2620,2674,2710,2740,2762,2776,2792,3126,3162,3178,3192,3214,3228,3244,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4178 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4178 3214 4
  · have he : independentCachedBranchMembers4178.erase 3214=independentCachedBranchMembers4176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4176
  · have he : independentCachedBranchMembers4178.filter (independentCachedEdge 3214)=independentCachedBranchMembers4177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4177
def independentCachedBranchMembers4179 : Finset ℕ := ([12,36,66,80,192,250,1582,1590,1596,1626,1642,1650,1678,1692,1702,1708,1738,1746,1752,1762,1768,1776,2606,2614,2620,2650,2674,2680,2702,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4179 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4179 2614 5
  · have he : independentCachedBranchMembers4179.erase 2614=independentCachedBranchMembers4173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4173
  · have he : independentCachedBranchMembers4179.filter (independentCachedEdge 2614)=independentCachedBranchMembers4178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4178
def independentCachedBranchMembers4180 : Finset ℕ := ([36,80,192,250,1590,1642,1678,1702,1746,1768,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3118,3186,3244,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4180 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4180 5 (fun x => (if x<2674 then (if x<1678 then (if x<250 then (if x<80 then 0 else (if x<192 then 0 else 1)) else (if x<1590 then 1 else (if x<1642 then 2 else 2))) else (if x<1768 then (if x<1702 then 2 else (if x<1746 then 0 else 0)) else (if x<2620 then (if x<2606 then 1 else 0) else (if x<2650 then 3 else 0)))) else (if x<2800 then (if x<2762 then (if x<2710 then 2 else (if x<2732 then 2 else 4)) else (if x<2776 then 1 else (if x<2786 then 3 else 4))) else (if x<3244 then (if x<3118 then 1 else (if x<3186 then 3 else 4)) else (if x<3288 then (if x<3274 then 0 else 3) else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4181 : Finset ℕ := ([36,80,192,250,1642,1678,2606,2650,2762,2800,3118,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4181 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4181 4 (fun x => (if x<2606 then (if x<250 then (if x<80 then 0 else (if x<192 then 0 else 1)) else (if x<1642 then 1 else (if x<1678 then 2 else 2))) else (if x<2800 then (if x<2650 then 0 else (if x<2762 then 0 else 1)) else (if x<3118 then 1 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4182 : Finset ℕ := ([36,80,192,250,1590,1642,1678,1692,1702,1746,1768,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3118,3186,3244,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4182 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4182 1692 4
  · have he : independentCachedBranchMembers4182.erase 1692=independentCachedBranchMembers4180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4180
  · have he : independentCachedBranchMembers4182.filter (independentCachedEdge 1692)=independentCachedBranchMembers4181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4181
def independentCachedBranchMembers4183 : Finset ℕ := ([80,192,1590,1678,1702,1768,2606,2710,2776,2800,3118,3288] : List ℕ).toFinset
theorem independentCachedBranchBound4183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4183 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4183 4 (fun x => (if x<2606 then (if x<1678 then (if x<192 then 0 else (if x<1590 then 1 else 1)) else (if x<1702 then 0 else (if x<1768 then 2 else 2))) else (if x<2800 then (if x<2710 then 0 else (if x<2776 then 2 else 1)) else (if x<3118 then 3 else (if x<3288 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4184 : Finset ℕ := ([36,66,80,192,250,1590,1642,1678,1692,1702,1746,1768,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3118,3186,3244,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4184 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4184 66 4
  · have he : independentCachedBranchMembers4184.erase 66=independentCachedBranchMembers4182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4182
  · have he : independentCachedBranchMembers4184.filter (independentCachedEdge 66)=independentCachedBranchMembers4183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4183
def independentCachedBranchMembers4185 : Finset ℕ := ([36,250,1590,1642,1702,1768,2650,2710,2762,2776,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound4185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4185 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4185 4 (fun x => (if x<2650 then (if x<1642 then (if x<250 then 0 else (if x<1590 then 1 else 0)) else (if x<1702 then 1 else (if x<1768 then 2 else 2))) else (if x<2776 then (if x<2710 then 1 else (if x<2762 then 2 else 0)) else (if x<3274 then 2 else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4186 : Finset ℕ := ([12,36,66,80,192,250,1590,1642,1678,1692,1702,1746,1768,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3118,3186,3244,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4186 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4186 12 4
  · have he : independentCachedBranchMembers4186.erase 12=independentCachedBranchMembers4184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4184
  · have he : independentCachedBranchMembers4186.filter (independentCachedEdge 12)=independentCachedBranchMembers4185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4185
def independentCachedBranchMembers4187 : Finset ℕ := ([66,1590,1642,1692,1702,2620,2650,2710,2732,2762,2800,3118,3186,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4187 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4187 4 (fun x => (if x<2710 then (if x<1692 then (if x<1590 then 0 else (if x<1642 then 1 else 0)) else (if x<2620 then (if x<1702 then 1 else 2) else (if x<2650 then 1 else 0))) else (if x<3118 then (if x<2762 then (if x<2732 then 1 else 2) else (if x<2800 then 3 else 3)) else (if x<3288 then (if x<3186 then 2 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4188 : Finset ℕ := ([1642,1692,2710,2800,3186,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4188 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4188 3 (fun x => (if x<2800 then (if x<1692 then 0 else (if x<2710 then 1 else 0)) else (if x<3186 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4189 : Finset ℕ := ([36,66,1590,1642,1692,1702,2620,2650,2710,2732,2762,2800,3118,3186,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4189 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4189 36 3
  · have he : independentCachedBranchMembers4189.erase 36=independentCachedBranchMembers4187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4187
  · have he : independentCachedBranchMembers4189.filter (independentCachedEdge 36)=independentCachedBranchMembers4188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4188
def independentCachedBranchMembers4190 : Finset ℕ := ([12,36,66,80,192,250,1590,1642,1678,1692,1702,1746,1768,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3118,3186,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4190 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4190 3312 4
  · have he : independentCachedBranchMembers4190.erase 3312=independentCachedBranchMembers4186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4186
  · have he : independentCachedBranchMembers4190.filter (independentCachedEdge 3312)=independentCachedBranchMembers4189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4189
def independentCachedBranchMembers4191 : Finset ℕ := ([192,1590,1678,1692,1768,2606,2620,2650,2710,2786,2800,3186,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound4191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4191 4 (fun x => (if x<2650 then (if x<1692 then (if x<1590 then 0 else (if x<1678 then 0 else 1)) else (if x<2606 then (if x<1768 then 2 else 1) else (if x<2620 then 0 else 2))) else (if x<3186 then (if x<2786 then (if x<2710 then 3 else 1) else (if x<2800 then 3 else 1)) else (if x<3274 then (if x<3244 then 3 else 2) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
