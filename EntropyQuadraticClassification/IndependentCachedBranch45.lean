/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch44
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4224 : Finset ℕ := ([1678,1776,2620,2674,3102,3118] : List ℕ).toFinset
theorem independentCachedBranchBound4224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4224 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4224 3 (fun x => (if x<2674 then (if x<1776 then 0 else (if x<2620 then 1 else 2)) else (if x<3102 then 0 else (if x<3118 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4225 : Finset ℕ := ([80,1596,1650,1678,1776,2620,2674,2702,2800,3102,3118,3228,3244,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4225 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4225 1650 3
  · have he : independentCachedBranchMembers4225.erase 1650=independentCachedBranchMembers4223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4223
  · have he : independentCachedBranchMembers4225.filter (independentCachedEdge 1650)=independentCachedBranchMembers4224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4224
def independentCachedBranchMembers4226 : Finset ℕ := ([12,66,80,192,1582,1596,1650,1678,1708,1746,1762,1776,2606,2620,2674,2702,2716,2732,2770,2786,2800,3102,3118,3132,3186,3228,3244,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4226 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4226 3132 4
  · have he : independentCachedBranchMembers4226.erase 3132=independentCachedBranchMembers4222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4222
  · have he : independentCachedBranchMembers4226.filter (independentCachedEdge 3132)=independentCachedBranchMembers4225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4225
def independentCachedBranchMembers4227 : Finset ℕ := ([80,192,1596,1650,1678,1708,1762,2606,2716,2770,2800,3118,3228,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4227 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4227 4 (fun x => (if x<2606 then (if x<1650 then (if x<192 then 0 else (if x<1596 then 1 else 1)) else (if x<1708 then (if x<1678 then 0 else 2) else (if x<1762 then 3 else 2))) else (if x<3118 then (if x<2770 then (if x<2716 then 1 else 2) else (if x<2800 then 0 else 2)) else (if x<3282 then (if x<3228 then 3 else 3) else (if x<3312 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4228 : Finset ℕ := ([12,66,80,192,1582,1596,1650,1678,1692,1708,1746,1762,1776,2606,2620,2674,2702,2716,2732,2770,2786,2800,3102,3118,3132,3186,3228,3244,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4228 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4228 1692 4
  · have he : independentCachedBranchMembers4228.erase 1692=independentCachedBranchMembers4226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4226
  · have he : independentCachedBranchMembers4228.filter (independentCachedEdge 1692)=independentCachedBranchMembers4227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4227
def independentCachedBranchMembers4229 : Finset ℕ := ([66,192,1596,1678,1746,1762,2620,2702,2770,2786,3102,3118,3186,3228,3244,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4229 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4229 4 (fun x => (if x<2770 then (if x<1746 then (if x<1596 then (if x<192 then 0 else 1) else (if x<1678 then 0 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2702 then 1 else 3))) else (if x<3186 then (if x<3102 then (if x<2786 then 0 else 3) else (if x<3118 then 2 else 1)) else (if x<3244 then (if x<3228 then 2 else 3) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4230 : Finset ℕ := ([12,66,80,192,1582,1596,1650,1678,1692,1708,1746,1762,1776,2606,2620,2674,2702,2716,2732,2770,2786,2800,3102,3118,3132,3186,3214,3228,3244,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4230 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4230 3214 4
  · have he : independentCachedBranchMembers4230.erase 3214=independentCachedBranchMembers4228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4228
  · have he : independentCachedBranchMembers4230.filter (independentCachedEdge 3214)=independentCachedBranchMembers4229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4229
def independentCachedBranchMembers4231 : Finset ℕ := ([12,36,66,72,80,132,192,250,1582,1590,1596,1626,1642,1650,1678,1686,1692,1702,1708,1738,1746,1752,1762,1768,1776,2606,2614,2620,2650,2674,2680,2702,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4231 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4231 72 5
  · have he : independentCachedBranchMembers4231.erase 72=independentCachedBranchMembers4219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4219
  · have he : independentCachedBranchMembers4231.filter (independentCachedEdge 72)=independentCachedBranchMembers4230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4230
def independentCachedBranchMembers4232 : Finset ℕ := ([80,192,250,1582,1626,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,2710,2762,2776,2800,3102,3126,3178,3192,3214,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4232 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4232 5 (fun x => (if x<2674 then (if x<1738 then (if x<1582 then (if x<192 then 0 else (if x<250 then 1 else 0)) else (if x<1686 then (if x<1626 then 1 else 0) else (if x<1708 then 2 else 2))) else (if x<1776 then (if x<1752 then 1 else (if x<1762 then 2 else 2)) else (if x<2620 then (if x<2606 then 0 else 3) else (if x<2650 then 1 else 3)))) else (if x<3178 then (if x<2776 then (if x<2710 then 0 else (if x<2762 then 3 else 4)) else (if x<3102 then (if x<2800 then 0 else 4) else (if x<3126 then 3 else 1))) else (if x<3238 then (if x<3192 then 3 else (if x<3214 then 0 else 4)) else (if x<3282 then (if x<3252 then 2 else 4) else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4233 : Finset ℕ := ([250,1686,1762,1776,2674,2710,2800,3102,3178,3192,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4233 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4233 4 (fun x => (if x<2800 then (if x<1776 then (if x<1686 then 0 else (if x<1762 then 1 else 0)) else (if x<2674 then 1 else (if x<2710 then 0 else 2))) else (if x<3192 then (if x<3102 then 2 else (if x<3178 then 1 else 0)) else (if x<3214 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4234 : Finset ℕ := ([36,80,192,250,1582,1626,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,2710,2762,2776,2800,3102,3126,3178,3192,3214,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4234 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4234 36 4
  · have he : independentCachedBranchMembers4234.erase 36=independentCachedBranchMembers4232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4232
  · have he : independentCachedBranchMembers4234.filter (independentCachedEdge 36)=independentCachedBranchMembers4233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4233
def independentCachedBranchMembers4235 : Finset ℕ := ([36,80,192,250,1582,1626,1738,1776,2606,2650,2762,2800,3102,3178,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound4235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4235 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4235 4 (fun x => (if x<2606 then (if x<1582 then (if x<192 then (if x<80 then 0 else 0) else (if x<250 then 1 else 1)) else (if x<1738 then (if x<1626 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3102 then (if x<2762 then (if x<2650 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3178 then 2 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4236 : Finset ℕ := ([36,80,192,250,1582,1626,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,2710,2762,2776,2800,3102,3126,3178,3192,3214,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4236 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4236 3228 4
  · have he : independentCachedBranchMembers4236.erase 3228=independentCachedBranchMembers4234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4234
  · have he : independentCachedBranchMembers4236.filter (independentCachedEdge 3228)=independentCachedBranchMembers4235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4235
def independentCachedBranchMembers4237 : Finset ℕ := ([36,80,1582,1626,1686,1708,1752,1762,2620,2674,2762,2800,3126,3192,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound4237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4237 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4237 4 (fun x => (if x<2620 then (if x<1686 then (if x<1582 then (if x<80 then 0 else 0) else (if x<1626 then 0 else 0)) else (if x<1752 then (if x<1708 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3126 then (if x<2762 then (if x<2674 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3192 then 2 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4238 : Finset ℕ := ([36,80,192,250,1582,1626,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,2710,2762,2776,2786,2800,3102,3126,3178,3192,3214,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4238 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4238 2786 4
  · have he : independentCachedBranchMembers4238.erase 2786=independentCachedBranchMembers4236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4236
  · have he : independentCachedBranchMembers4238.filter (independentCachedEdge 2786)=independentCachedBranchMembers4237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4237
def independentCachedBranchMembers4239 : Finset ℕ := ([192,250,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,3102,3126,3178,3192] : List ℕ).toFinset
theorem independentCachedBranchBound4239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4239 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4239 4 (fun x => (if x<2606 then (if x<1738 then (if x<1686 then (if x<250 then 0 else 0) else (if x<1708 then 1 else 1)) else (if x<1762 then (if x<1752 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3102 then (if x<2650 then (if x<2620 then 2 else 3) else (if x<2674 then 2 else 3)) else (if x<3178 then (if x<3126 then 2 else 3) else (if x<3192 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4240 : Finset ℕ := ([36,80,192,250,1582,1626,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3102,3126,3178,3192,3214,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4240 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4240 2732 4
  · have he : independentCachedBranchMembers4240.erase 2732=independentCachedBranchMembers4238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4238
  · have he : independentCachedBranchMembers4240.filter (independentCachedEdge 2732)=independentCachedBranchMembers4239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4239
def independentCachedBranchMembers4241 : Finset ℕ := ([192,1626,1708,1762,1776,2606,2620,2674,2710,2762,2776,3102,3238,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4241 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4241 4 (fun x => (if x<2674 then (if x<1762 then (if x<1626 then 0 else (if x<1708 then 1 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2620 then 2 else 0))) else (if x<3102 then (if x<2762 then (if x<2710 then 1 else 3) else (if x<2776 then 3 else 1)) else (if x<3252 then (if x<3238 then 0 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4242 : Finset ℕ := ([1762,1776,2674,2710,3102,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4242 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4242 3 (fun x => (if x<2710 then (if x<1776 then 0 else (if x<2674 then 1 else 0)) else (if x<3102 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4243 : Finset ℕ := ([36,192,1626,1708,1762,1776,2606,2620,2674,2710,2762,2776,3102,3238,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4243 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4243 36 3
  · have he : independentCachedBranchMembers4243.erase 36=independentCachedBranchMembers4241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4241
  · have he : independentCachedBranchMembers4243.filter (independentCachedEdge 36)=independentCachedBranchMembers4242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4242
def independentCachedBranchMembers4244 : Finset ℕ := ([36,80,192,250,1582,1626,1650,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3102,3126,3178,3192,3214,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4244 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4244 1650 4
  · have he : independentCachedBranchMembers4244.erase 1650=independentCachedBranchMembers4240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4240
  · have he : independentCachedBranchMembers4244.filter (independentCachedEdge 1650)=independentCachedBranchMembers4243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4243
def independentCachedBranchMembers4245 : Finset ℕ := ([250,1582,1708,1738,1762,2620,2650,2674,2710,2776,2800,3178,3214,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4245 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4245 4 (fun x => (if x<2674 then (if x<1738 then (if x<1582 then 0 else (if x<1708 then 1 else 2)) else (if x<2620 then (if x<1762 then 0 else 1) else (if x<2650 then 1 else 0))) else (if x<3178 then (if x<2776 then (if x<2710 then 2 else 3) else (if x<2800 then 3 else 1)) else (if x<3238 then (if x<3214 then 0 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4246 : Finset ℕ := ([1738,1762,2620,2710,3178,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4246 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4246 3 (fun x => (if x<2710 then (if x<1762 then 0 else (if x<2620 then 1 else 0)) else (if x<3178 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4247 : Finset ℕ := ([80,250,1582,1708,1738,1762,2620,2650,2674,2710,2776,2800,3178,3214,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4247 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4247 80 3
  · have he : independentCachedBranchMembers4247.erase 80=independentCachedBranchMembers4245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4245
  · have he : independentCachedBranchMembers4247.filter (independentCachedEdge 80)=independentCachedBranchMembers4246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4246
def independentCachedBranchMembers4248 : Finset ℕ := ([36,80,192,250,1582,1596,1626,1650,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3102,3126,3178,3192,3214,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4248 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4248 1596 4
  · have he : independentCachedBranchMembers4248.erase 1596=independentCachedBranchMembers4244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4244
  · have he : independentCachedBranchMembers4248.filter (independentCachedEdge 1596)=independentCachedBranchMembers4247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4247
def independentCachedBranchMembers4249 : Finset ℕ := ([80,192,1582,1686,1752,1776,2606,2710,2776,2800,3102,3126,3192,3214,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4249 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4249 4 (fun x => (if x<2776 then (if x<1752 then (if x<1582 then (if x<192 then 0 else 1) else (if x<1686 then 0 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2710 then 1 else 3))) else (if x<3192 then (if x<3102 then (if x<2800 then 0 else 3) else (if x<3126 then 2 else 1)) else (if x<3238 then (if x<3214 then 2 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4250 : Finset ℕ := ([36,66,80,192,250,1582,1596,1626,1650,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3102,3126,3178,3192,3214,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4250 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4250 66 4
  · have he : independentCachedBranchMembers4250.erase 66=independentCachedBranchMembers4248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4248
  · have he : independentCachedBranchMembers4250.filter (independentCachedEdge 66)=independentCachedBranchMembers4249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4249
def independentCachedBranchMembers4251 : Finset ℕ := ([36,250,1626,1686,1738,1752,2650,2710,2762,2776,3126,3178,3192,3238,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4251 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4251 4 (fun x => (if x<2762 then (if x<1738 then (if x<1626 then (if x<250 then 0 else 1) else (if x<1686 then 0 else 2)) else (if x<2650 then (if x<1752 then 1 else 2) else (if x<2710 then 1 else 3))) else (if x<3192 then (if x<3126 then (if x<2776 then 0 else 3) else (if x<3178 then 2 else 1)) else (if x<3252 then (if x<3238 then 2 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4252 : Finset ℕ := ([12,36,66,80,192,250,1582,1596,1626,1650,1686,1708,1738,1752,1762,1776,2606,2620,2650,2674,2710,2732,2762,2776,2786,2800,3102,3126,3178,3192,3214,3228,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4252 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4252 12 4
  · have he : independentCachedBranchMembers4252.erase 12=independentCachedBranchMembers4250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4250
  · have he : independentCachedBranchMembers4252.filter (independentCachedEdge 12)=independentCachedBranchMembers4251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4251
def independentCachedBranchMembers4253 : Finset ℕ := ([12,36,66,72,80,132,192,250,1582,1590,1596,1626,1642,1650,1678,1686,1692,1702,1708,1738,1746,1752,1762,1768,1776,2606,2614,2620,2650,2674,2680,2702,2710,2716,2732,2740,2762,2770,2776,2786,2792,2800,3102,3118,3126,3132,3162,3178,3186,3192,3214,3222,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4253 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4253 3222 5
  · have he : independentCachedBranchMembers4253.erase 3222=independentCachedBranchMembers4231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4231
  · have he : independentCachedBranchMembers4253.filter (independentCachedEdge 3222)=independentCachedBranchMembers4252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4252
def independentCachedBranchMembers4254 : Finset ℕ := ([12,18,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4254 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4254 68 6
  · have he : independentCachedBranchMembers4254.erase 68=independentCachedBranchMembers4038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4038
  · have he : independentCachedBranchMembers4254.filter (independentCachedEdge 68)=independentCachedBranchMembers4253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4253
def independentCachedBranchMembers4255 : Finset ℕ := ([36,40,66,130,1596,1626,1644,1652,1678,1686,1720,1734,1746,1768,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3192,3222,3226,3244,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4255 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4255 6 (fun x => (if x<2680 then (if x<1678 then (if x<1596 then (if x<66 then (if x<40 then 0 else 1) else (if x<130 then 0 else 1)) else (if x<1644 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else 2))) else (if x<1746 then (if x<1720 then (if x<1686 then 3 else 2) else (if x<1734 then 2 else 1)) else (if x<2646 then (if x<1768 then 3 else 3) else (if x<2668 then 2 else 4)))) else (if x<3150 then (if x<2758 then (if x<2732 then (if x<2714 then 1 else 2) else (if x<2740 then 0 else 2)) else (if x<2770 then (if x<2762 then 4 else 0) else (if x<3132 then 1 else 1))) else (if x<3226 then (if x<3192 then (if x<3158 then 4 else 5) else (if x<3222 then 4 else 1)) else (if x<3274 then (if x<3244 then 5 else 3) else (if x<3282 then 3 else (if x<3300 then 0 else 4)))))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
