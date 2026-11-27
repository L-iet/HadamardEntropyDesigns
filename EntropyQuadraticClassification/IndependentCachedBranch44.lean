/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch43
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4192 : Finset ℕ := ([1590,1768,2650,2710,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound4192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4192 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4192 3 (fun x => (if x<2710 then (if x<1768 then 0 else (if x<2650 then 1 else 2)) else (if x<3274 then 0 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4193 : Finset ℕ := ([12,192,1590,1678,1692,1768,2606,2620,2650,2710,2786,2800,3186,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound4193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4193 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4193 12 3
  · have he : independentCachedBranchMembers4193.erase 12=independentCachedBranchMembers4191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4191
  · have he : independentCachedBranchMembers4193.filter (independentCachedEdge 12)=independentCachedBranchMembers4192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4192
def independentCachedBranchMembers4194 : Finset ℕ := ([12,36,66,80,192,250,1590,1642,1678,1692,1702,1746,1768,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3118,3162,3186,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4194 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4194 3162 4
  · have he : independentCachedBranchMembers4194.erase 3162=independentCachedBranchMembers4190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4190
  · have he : independentCachedBranchMembers4194.filter (independentCachedEdge 3162)=independentCachedBranchMembers4193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4193
def independentCachedBranchMembers4195 : Finset ℕ := ([250,1642,1678,1702,1768,2620,2650,2674,2710,2776,2800,3118,3244,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4195 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4195 4 (fun x => (if x<2674 then (if x<1702 then (if x<1642 then 0 else (if x<1678 then 0 else 1)) else (if x<2620 then (if x<1768 then 2 else 1) else (if x<2650 then 3 else 0))) else (if x<3118 then (if x<2776 then (if x<2710 then 3 else 1) else (if x<2800 then 2 else 1)) else (if x<3274 then (if x<3244 then 2 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4196 : Finset ℕ := ([1642,1768,2620,2710,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4196 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4196 3 (fun x => (if x<2710 then (if x<1768 then 0 else (if x<2620 then 1 else 2)) else (if x<3274 then 0 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4197 : Finset ℕ := ([80,250,1642,1678,1702,1768,2620,2650,2674,2710,2776,2800,3118,3244,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4197 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4197 80 3
  · have he : independentCachedBranchMembers4197.erase 80=independentCachedBranchMembers4195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4195
  · have he : independentCachedBranchMembers4197.filter (independentCachedEdge 80)=independentCachedBranchMembers4196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4196
def independentCachedBranchMembers4198 : Finset ℕ := ([12,36,66,80,192,250,1590,1642,1678,1692,1702,1746,1768,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3118,3132,3162,3186,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4198 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4198 3132 4
  · have he : independentCachedBranchMembers4198.erase 3132=independentCachedBranchMembers4194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4194
  · have he : independentCachedBranchMembers4198.filter (independentCachedEdge 3132)=independentCachedBranchMembers4197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4197
def independentCachedBranchMembers4199 : Finset ℕ := ([12,36,66,80,192,250,1582,1590,1596,1626,1642,1650,1678,1686,1692,1702,1708,1738,1746,1752,1762,1768,1776,2606,2614,2620,2650,2674,2680,2702,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4199 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4199 1686 5
  · have he : independentCachedBranchMembers4199.erase 1686=independentCachedBranchMembers4179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4179
  · have he : independentCachedBranchMembers4199.filter (independentCachedEdge 1686)=independentCachedBranchMembers4198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4198
def independentCachedBranchMembers4200 : Finset ℕ := ([12,36,192,250,1582,1590,1738,1746,1762,1776,2614,2620,2770,2776,2786,2792,2800,3102,3118,3132,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4200 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4200 5 (fun x => (if x<2770 then (if x<1738 then (if x<250 then (if x<36 then 0 else (if x<192 then 1 else 0)) else (if x<1582 then 2 else (if x<1590 then 0 else 1))) else (if x<1776 then (if x<1746 then 2 else (if x<1762 then 1 else 0)) else (if x<2614 then 2 else (if x<2620 then 3 else 0)))) else (if x<3118 then (if x<2792 then (if x<2776 then 2 else (if x<2786 then 1 else 3)) else (if x<2800 then 2 else (if x<3102 then 0 else 0))) else (if x<3282 then (if x<3132 then 1 else (if x<3274 then 3 else 1)) else (if x<3304 then (if x<3288 then 0 else 2) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4201 : Finset ℕ := ([250,1582,1738,1762,2614,2620,2770,2776,2800,3118,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4201 4 (fun x => (if x<2770 then (if x<1762 then (if x<1582 then 0 else (if x<1738 then 1 else 0)) else (if x<2614 then 1 else (if x<2620 then 2 else 1))) else (if x<3118 then (if x<2776 then 0 else (if x<2800 then 3 else 1)) else (if x<3274 then 2 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4202 : Finset ℕ := ([12,36,192,250,1582,1590,1738,1746,1762,1776,2606,2614,2620,2770,2776,2786,2792,2800,3102,3118,3132,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4202 2606 4
  · have he : independentCachedBranchMembers4202.erase 2606=independentCachedBranchMembers4200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4200
  · have he : independentCachedBranchMembers4202.filter (independentCachedEdge 2606)=independentCachedBranchMembers4201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4201
def independentCachedBranchMembers4203 : Finset ℕ := ([12,1582,1590,1738,1746,1776,2620,2776,2786,3102,3132,3288] : List ℕ).toFinset
theorem independentCachedBranchBound4203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4203 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4203 4 (fun x => (if x<2620 then (if x<1738 then (if x<1582 then 0 else (if x<1590 then 0 else 1)) else (if x<1746 then 2 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2776 then 0 else (if x<2786 then 1 else 2)) else (if x<3132 then 0 else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4204 : Finset ℕ := ([12,36,192,250,1582,1590,1738,1746,1752,1762,1776,2606,2614,2620,2770,2776,2786,2792,2800,3102,3118,3132,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4204 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4204 1752 4
  · have he : independentCachedBranchMembers4204.erase 1752=independentCachedBranchMembers4202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4202
  · have he : independentCachedBranchMembers4204.filter (independentCachedEdge 1752)=independentCachedBranchMembers4203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4203
def independentCachedBranchMembers4205 : Finset ℕ := ([12,1582,1738,1776,2620,2770,2776,2786,2792,3102,3118,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4205 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4205 4 (fun x => (if x<2776 then (if x<1776 then (if x<1582 then 0 else (if x<1738 then 0 else 1)) else (if x<2620 then 1 else (if x<2770 then 0 else 1))) else (if x<3102 then (if x<2786 then 2 else (if x<2792 then 2 else 1)) else (if x<3274 then (if x<3118 then 0 else 3) else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4206 : Finset ℕ := ([12,1776,2620,2776,2792,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4206 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4206 3 (fun x => (if x<2776 then (if x<1776 then 0 else (if x<2620 then 0 else 1)) else (if x<2792 then 1 else (if x<3312 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4207 : Finset ℕ := ([12,1582,1738,1776,2614,2620,2770,2776,2786,2792,3102,3118,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4207 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4207 2614 3
  · have he : independentCachedBranchMembers4207.erase 2614=independentCachedBranchMembers4205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4205
  · have he : independentCachedBranchMembers4207.filter (independentCachedEdge 2614)=independentCachedBranchMembers4206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4206
def independentCachedBranchMembers4208 : Finset ℕ := ([12,36,192,250,1582,1590,1738,1746,1752,1762,1776,2606,2614,2620,2762,2770,2776,2786,2792,2800,3102,3118,3132,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4208 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4208 2762 4
  · have he : independentCachedBranchMembers4208.erase 2762=independentCachedBranchMembers4204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4204
  · have he : independentCachedBranchMembers4208.filter (independentCachedEdge 2762)=independentCachedBranchMembers4207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4207
def independentCachedBranchMembers4209 : Finset ℕ := ([250,1582,1590,1738,1746,1762,2620,2776,2792,2800,3132,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4209 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4209 4 (fun x => (if x<2776 then (if x<1738 then (if x<1582 then 0 else (if x<1590 then 1 else 2)) else (if x<1762 then (if x<1746 then 0 else 2) else (if x<2620 then 1 else 1))) else (if x<3132 then (if x<2792 then 0 else (if x<2800 then 3 else 1)) else (if x<3304 then (if x<3288 then 2 else 2) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4210 : Finset ℕ := ([12,36,192,250,1582,1590,1596,1738,1746,1752,1762,1776,2606,2614,2620,2762,2770,2776,2786,2792,2800,3102,3118,3132,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4210 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4210 1596 4
  · have he : independentCachedBranchMembers4210.erase 1596=independentCachedBranchMembers4208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4208
  · have he : independentCachedBranchMembers4210.filter (independentCachedEdge 1596)=independentCachedBranchMembers4209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4209
def independentCachedBranchMembers4211 : Finset ℕ := ([36,1590,1752,1762,2606,2614,2776,2786,3102,3132,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4211 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4211 4 (fun x => (if x<2786 then (if x<1762 then (if x<1590 then 0 else (if x<1752 then 0 else 1)) else (if x<2614 then (if x<2606 then 1 else 0) else (if x<2776 then 2 else 3))) else (if x<3274 then (if x<3102 then 2 else (if x<3132 then 2 else 0)) else (if x<3304 then (if x<3282 then 1 else 3) else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4212 : Finset ℕ := ([1590,1752,2606,2786,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4212 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4212 3 (fun x => (if x<2786 then (if x<1752 then 0 else (if x<2606 then 1 else 0)) else (if x<3274 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4213 : Finset ℕ := ([36,1582,1590,1752,1762,2606,2614,2776,2786,3102,3132,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4213 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4213 1582 3
  · have he : independentCachedBranchMembers4213.erase 1582=independentCachedBranchMembers4211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4211
  · have he : independentCachedBranchMembers4213.filter (independentCachedEdge 1582)=independentCachedBranchMembers4212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4212
def independentCachedBranchMembers4214 : Finset ℕ := ([12,36,192,250,1582,1590,1596,1738,1746,1752,1762,1776,2606,2614,2620,2762,2770,2776,2786,2792,2800,3102,3118,3132,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4214 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4214 3298 4
  · have he : independentCachedBranchMembers4214.erase 3298=independentCachedBranchMembers4210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4210
  · have he : independentCachedBranchMembers4214.filter (independentCachedEdge 3298)=independentCachedBranchMembers4213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4213
def independentCachedBranchMembers4215 : Finset ℕ := ([12,36,1590,1738,1752,1762,1776,2606,2620,2770,2792,3118,3132,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4215 4 (fun x => (if x<2606 then (if x<1738 then (if x<36 then 0 else (if x<1590 then 1 else 1)) else (if x<1762 then (if x<1752 then 2 else 3) else (if x<1776 then 0 else 2))) else (if x<3118 then (if x<2770 then (if x<2620 then 1 else 0) else (if x<2792 then 2 else 2)) else (if x<3282 then (if x<3132 then 3 else 1) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4216 : Finset ℕ := ([12,36,192,250,1582,1590,1596,1738,1746,1752,1762,1768,1776,2606,2614,2620,2762,2770,2776,2786,2792,2800,3102,3118,3132,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4216 1768 4
  · have he : independentCachedBranchMembers4216.erase 1768=independentCachedBranchMembers4214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4214
  · have he : independentCachedBranchMembers4216.filter (independentCachedEdge 1768)=independentCachedBranchMembers4215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4215
def independentCachedBranchMembers4217 : Finset ℕ := ([12,250,1590,1746,1762,1776,2614,2770,2786,2800,3102,3118,3132,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4217 4 (fun x => (if x<2786 then (if x<1762 then (if x<1590 then (if x<250 then 0 else 1) else (if x<1746 then 2 else 0)) else (if x<2614 then (if x<1776 then 1 else 2) else (if x<2770 then 3 else 1))) else (if x<3132 then (if x<3102 then (if x<2800 then 0 else 3) else (if x<3118 then 2 else 3)) else (if x<3288 then (if x<3274 then 0 else 1) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4218 : Finset ℕ := ([12,36,192,250,1582,1590,1596,1738,1746,1752,1762,1768,1776,2606,2614,2620,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4218 3126 4
  · have he : independentCachedBranchMembers4218.erase 3126=independentCachedBranchMembers4216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4216
  · have he : independentCachedBranchMembers4218.filter (independentCachedEdge 3126)=independentCachedBranchMembers4217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4217
def independentCachedBranchMembers4219 : Finset ℕ := ([12,36,66,80,132,192,250,1582,1590,1596,1626,1642,1650,1678,1686,1692,1702,1708,1738,1746,1752,1762,1768,1776,2606,2614,2620,2650,2674,2680,2702,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4219 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4219 132 5
  · have he : independentCachedBranchMembers4219.erase 132=independentCachedBranchMembers4199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4199
  · have he : independentCachedBranchMembers4219.filter (independentCachedEdge 132)=independentCachedBranchMembers4218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4218
def independentCachedBranchMembers4220 : Finset ℕ := ([12,66,80,192,1596,1650,1678,1708,1746,1762,1776,2606,2620,2674,2702,2716,2732,2770,2786,2800,3102,3118,3186,3228,3244,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4220 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4220 5 (fun x => (if x<2702 then (if x<1708 then (if x<192 then (if x<66 then 0 else (if x<80 then 0 else 1)) else (if x<1650 then (if x<1596 then 2 else 0) else (if x<1678 then 0 else 1))) else (if x<1776 then (if x<1746 then 3 else (if x<1762 then 1 else 2)) else (if x<2620 then (if x<2606 then 3 else 1) else (if x<2674 then 2 else 1)))) else (if x<3118 then (if x<2770 then (if x<2716 then 3 else (if x<2732 then 0 else 4)) else (if x<2800 then (if x<2786 then 0 else 4) else (if x<3102 then 2 else 2))) else (if x<3244 then (if x<3186 then 3 else (if x<3228 then 3 else 4)) else (if x<3298 then (if x<3282 then 0 else 2) else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4221 : Finset ℕ := ([66,1596,1678,1708,1746,1776,2606,2674,2716,2786,3118,3186,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4221 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4221 4 (fun x => (if x<2674 then (if x<1708 then (if x<1596 then 0 else (if x<1678 then 0 else 1)) else (if x<1776 then (if x<1746 then 2 else 1) else (if x<2606 then 2 else 1))) else (if x<3118 then (if x<2716 then 1 else (if x<2786 then 0 else 3)) else (if x<3228 then (if x<3186 then 2 else 2) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4222 : Finset ℕ := ([12,66,80,192,1582,1596,1650,1678,1708,1746,1762,1776,2606,2620,2674,2702,2716,2732,2770,2786,2800,3102,3118,3186,3228,3244,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4222 1582 4
  · have he : independentCachedBranchMembers4222.erase 1582=independentCachedBranchMembers4220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4220
  · have he : independentCachedBranchMembers4222.filter (independentCachedEdge 1582)=independentCachedBranchMembers4221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4221
def independentCachedBranchMembers4223 : Finset ℕ := ([80,1596,1678,1776,2620,2674,2702,2800,3102,3118,3228,3244,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4223 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4223 4 (fun x => (if x<2800 then (if x<1776 then (if x<1596 then 0 else (if x<1678 then 1 else 0)) else (if x<2674 then (if x<2620 then 1 else 2) else (if x<2702 then 0 else 2))) else (if x<3228 then (if x<3102 then 3 else (if x<3118 then 1 else 2)) else (if x<3282 then (if x<3244 then 2 else 0) else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
