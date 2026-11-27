/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch138
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7232 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2702,2758,2776,2788,3118,3162,3174,3192,3226,3238,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7232 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7232 48 4
  · have he : independentCachedBranchMembers7232.erase 48=independentCachedBranchMembers7230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7230
  · have he : independentCachedBranchMembers7232.filter (independentCachedEdge 48)=independentCachedBranchMembers7231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7231
def independentCachedBranchMembers7233 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1764,2618,2638,2702,2788,3118,3162,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7233 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7233 4 (fun x => (if x<2618 then (if x<1594 then (if x<132 then (if x<68 then 0 else 0) else (if x<238 then 1 else 1)) else (if x<1678 then (if x<1614 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3118 then (if x<2702 then (if x<2638 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3162 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7234 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2702,2758,2776,2788,3118,3162,3174,3192,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7234 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7234 3282 4
  · have he : independentCachedBranchMembers7234.erase 3282=independentCachedBranchMembers7232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7232
  · have he : independentCachedBranchMembers7234.filter (independentCachedEdge 3282)=independentCachedBranchMembers7233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7233
def independentCachedBranchMembers7235 : Finset ℕ := ([132,238,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,3118,3162,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7235 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7235 4 (fun x => (if x<2618 then (if x<1714 then (if x<1678 then (if x<238 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3118 then (if x<2668 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3174 then (if x<3162 then 2 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7236 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2702,2738,2758,2776,2788,3118,3162,3174,3192,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7236 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7236 2738 4
  · have he : independentCachedBranchMembers7236.erase 2738=independentCachedBranchMembers7234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7234
  · have he : independentCachedBranchMembers7236.filter (independentCachedEdge 2738)=independentCachedBranchMembers7235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7235
def independentCachedBranchMembers7237 : Finset ℕ := ([48,68,1594,1614,1708,1714,1734,1752,2668,2674,2702,2788,3174,3192,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7237 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7237 4 (fun x => (if x<2668 then (if x<1708 then (if x<1594 then (if x<68 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3174 then (if x<2702 then (if x<2674 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3192 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7238 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2702,2732,2738,2758,2776,2788,3118,3162,3174,3192,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7238 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7238 2732 4
  · have he : independentCachedBranchMembers7238.erase 2732=independentCachedBranchMembers7236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7236
  · have he : independentCachedBranchMembers7238.filter (independentCachedEdge 2732)=independentCachedBranchMembers7237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7237
def independentCachedBranchMembers7239 : Finset ℕ := ([238,1594,1678,1708,1714,2638,2668,2674,2758,2776,2788,3118,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7239 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7239 4 (fun x => (if x<2674 then (if x<1708 then (if x<1594 then 0 else (if x<1678 then 1 else 0)) else (if x<2638 then (if x<1714 then 1 else 2) else (if x<2668 then 0 else 2))) else (if x<3118 then (if x<2776 then (if x<2758 then 1 else 3) else (if x<2788 then 3 else 1)) else (if x<3238 then (if x<3226 then 0 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7240 : Finset ℕ := ([1678,1708,2674,2776,3118,3238] : List ℕ).toFinset
theorem independentCachedBranchBound7240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7240 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7240 3 (fun x => (if x<2776 then (if x<1708 then 0 else (if x<2674 then 1 else 0)) else (if x<3118 then 2 else (if x<3238 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7241 : Finset ℕ := ([68,238,1594,1678,1708,1714,2638,2668,2674,2758,2776,2788,3118,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7241 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7241 68 3
  · have he : independentCachedBranchMembers7241.erase 68=independentCachedBranchMembers7239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7239
  · have he : independentCachedBranchMembers7241.filter (independentCachedEdge 68)=independentCachedBranchMembers7240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7240
def independentCachedBranchMembers7242 : Finset ℕ := ([48,68,132,238,1594,1614,1650,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2702,2732,2738,2758,2776,2788,3118,3162,3174,3192,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7242 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7242 1650 4
  · have he : independentCachedBranchMembers7242.erase 1650=independentCachedBranchMembers7238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7238
  · have he : independentCachedBranchMembers7242.filter (independentCachedEdge 1650)=independentCachedBranchMembers7241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7241
def independentCachedBranchMembers7243 : Finset ℕ := ([132,1614,1708,1714,1764,2618,2668,2674,2702,2758,2776,3162,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7243 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7243 4 (fun x => (if x<2674 then (if x<1714 then (if x<1614 then 0 else (if x<1708 then 1 else 0)) else (if x<2618 then (if x<1764 then 2 else 1) else (if x<2668 then 2 else 1))) else (if x<3162 then (if x<2758 then (if x<2702 then 0 else 3) else (if x<2776 then 1 else 3)) else (if x<3256 then (if x<3238 then 0 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7244 : Finset ℕ := ([1708,1764,2668,2776,3162,3238] : List ℕ).toFinset
theorem independentCachedBranchBound7244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7244 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7244 3 (fun x => (if x<2776 then (if x<1764 then 0 else (if x<2668 then 1 else 0)) else (if x<3162 then 2 else (if x<3238 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7245 : Finset ℕ := ([48,132,1614,1708,1714,1764,2618,2668,2674,2702,2758,2776,3162,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7245 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7245 48 3
  · have he : independentCachedBranchMembers7245.erase 48=independentCachedBranchMembers7243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7243
  · have he : independentCachedBranchMembers7245.filter (independentCachedEdge 48)=independentCachedBranchMembers7244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7244
def independentCachedBranchMembers7246 : Finset ℕ := ([48,68,132,238,1594,1614,1644,1650,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2702,2732,2738,2758,2776,2788,3118,3162,3174,3192,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7246 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7246 1644 4
  · have he : independentCachedBranchMembers7246.erase 1644=independentCachedBranchMembers7242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7242
  · have he : independentCachedBranchMembers7246.filter (independentCachedEdge 1644)=independentCachedBranchMembers7245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7245
def independentCachedBranchMembers7247 : Finset ℕ := ([48,238,1614,1678,1734,1752,2638,2702,2758,2776,3118,3174,3192,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7247 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7247 4 (fun x => (if x<2758 then (if x<1734 then (if x<1614 then (if x<238 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<2638 then (if x<1752 then 2 else 2) else (if x<2702 then 1 else 0))) else (if x<3192 then (if x<3118 then (if x<2776 then 3 else 3) else (if x<3174 then 1 else 2)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7248 : Finset ℕ := ([18,48,68,132,238,1594,1614,1644,1650,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2702,2732,2738,2758,2776,2788,3118,3162,3174,3192,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7248 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7248 18 4
  · have he : independentCachedBranchMembers7248.erase 18=independentCachedBranchMembers7246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7246
  · have he : independentCachedBranchMembers7248.filter (independentCachedEdge 18)=independentCachedBranchMembers7247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7247
def independentCachedBranchMembers7249 : Finset ℕ := ([68,132,1594,1734,1752,1764,2618,2758,2776,2788,3162,3174,3192,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7249 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7249 4 (fun x => (if x<2776 then (if x<1752 then (if x<1594 then (if x<132 then 0 else 1) else (if x<1734 then 0 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2758 then 1 else 0))) else (if x<3192 then (if x<3162 then (if x<2788 then 3 else 3) else (if x<3174 then 2 else 2)) else (if x<3238 then (if x<3226 then 1 else 3) else (if x<3256 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7250 : Finset ℕ := ([12,18,48,68,132,238,1594,1614,1644,1650,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2702,2732,2738,2758,2776,2788,3118,3162,3174,3192,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7250 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7250 12 4
  · have he : independentCachedBranchMembers7250.erase 12=independentCachedBranchMembers7248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7248
  · have he : independentCachedBranchMembers7250.filter (independentCachedEdge 12)=independentCachedBranchMembers7249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7249
def independentCachedBranchMembers7251 : Finset ℕ := ([12,18,36,48,68,80,132,144,238,250,1582,1594,1614,1626,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2758,2764,2770,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7251 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7251 3288 5
  · have he : independentCachedBranchMembers7251.erase 3288=independentCachedBranchMembers7229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7229
  · have he : independentCachedBranchMembers7251.filter (independentCachedEdge 3288)=independentCachedBranchMembers7250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7250
def independentCachedBranchMembers7252 : Finset ℕ := ([80,144,250,1582,1626,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2714,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7252 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7252 5 (fun x => (if x<2674 then (if x<1714 then (if x<1582 then (if x<144 then 0 else (if x<250 then 1 else 0)) else (if x<1690 then (if x<1626 then 1 else 0) else (if x<1708 then 1 else 2))) else (if x<1776 then (if x<1734 then 2 else (if x<1752 then 2 else 2)) else (if x<2650 then (if x<2606 then 0 else 3) else (if x<2668 then 3 else 1)))) else (if x<3174 then (if x<2776 then (if x<2714 then 0 else (if x<2758 then 4 else 3)) else (if x<3130 then (if x<2800 then 0 else 4) else (if x<3150 then 3 else 3))) else (if x<3238 then (if x<3192 then 1 else (if x<3214 then 0 else 4)) else (if x<3282 then (if x<3256 then 2 else 2) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7253 : Finset ℕ := ([250,1714,1734,1776,2674,2758,2800,3130,3150,3192,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7253 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7253 4 (fun x => (if x<2800 then (if x<1776 then (if x<1714 then 0 else (if x<1734 then 0 else 1)) else (if x<2674 then 1 else (if x<2758 then 0 else 2))) else (if x<3192 then (if x<3130 then 2 else (if x<3150 then 0 else 1)) else (if x<3214 then 1 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7254 : Finset ℕ := ([36,80,144,250,1582,1626,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2714,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7254 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7254 36 4
  · have he : independentCachedBranchMembers7254.erase 36=independentCachedBranchMembers7252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7252
  · have he : independentCachedBranchMembers7254.filter (independentCachedEdge 36)=independentCachedBranchMembers7253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7253
def independentCachedBranchMembers7255 : Finset ℕ := ([36,80,144,250,1582,1626,1690,1776,2606,2650,2714,2800,3130,3150,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7255 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7255 4 (fun x => (if x<2606 then (if x<1582 then (if x<144 then (if x<80 then 0 else 0) else (if x<250 then 1 else 1)) else (if x<1690 then (if x<1626 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3130 then (if x<2714 then (if x<2650 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3150 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7256 : Finset ℕ := ([36,80,144,250,1582,1626,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2714,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7256 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7256 3276 4
  · have he : independentCachedBranchMembers7256.erase 3276=independentCachedBranchMembers7254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7254
  · have he : independentCachedBranchMembers7256.filter (independentCachedEdge 3276)=independentCachedBranchMembers7255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7255
def independentCachedBranchMembers7257 : Finset ℕ := ([36,80,1582,1626,1708,1714,1734,1752,2668,2674,2714,2800,3174,3192,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7257 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7257 4 (fun x => (if x<2668 then (if x<1708 then (if x<1582 then (if x<80 then 0 else 0) else (if x<1626 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3174 then (if x<2714 then (if x<2674 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3192 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7258 : Finset ℕ := ([36,80,144,250,1582,1626,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2714,2738,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7258 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7258 2738 4
  · have he : independentCachedBranchMembers7258.erase 2738=independentCachedBranchMembers7256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7256
  · have he : independentCachedBranchMembers7258.filter (independentCachedEdge 2738)=independentCachedBranchMembers7257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7257
def independentCachedBranchMembers7259 : Finset ℕ := ([144,250,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,3130,3150,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7259 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7259 4 (fun x => (if x<2606 then (if x<1714 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3130 then (if x<2668 then (if x<2650 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3174 then (if x<3150 then 2 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7260 : Finset ℕ := ([36,80,144,250,1582,1626,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2714,2732,2738,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7260 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7260 2732 4
  · have he : independentCachedBranchMembers7260.erase 2732=independentCachedBranchMembers7258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7258
  · have he : independentCachedBranchMembers7260.filter (independentCachedEdge 2732)=independentCachedBranchMembers7259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7259
def independentCachedBranchMembers7261 : Finset ℕ := ([144,1626,1708,1714,1776,2606,2668,2674,2714,2758,2776,3150,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7261 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7261 4 (fun x => (if x<2674 then (if x<1714 then (if x<1626 then 0 else (if x<1708 then 1 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2668 then 2 else 0))) else (if x<3150 then (if x<2758 then (if x<2714 then 1 else 3) else (if x<2776 then 3 else 1)) else (if x<3256 then (if x<3238 then 0 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7262 : Finset ℕ := ([1714,1776,2674,2758,3150,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7262 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7262 3 (fun x => (if x<2758 then (if x<1776 then 0 else (if x<2674 then 1 else 0)) else (if x<3150 then 2 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7263 : Finset ℕ := ([36,144,1626,1708,1714,1776,2606,2668,2674,2714,2758,2776,3150,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7263 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7263 36 3
  · have he : independentCachedBranchMembers7263.erase 36=independentCachedBranchMembers7261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7261
  · have he : independentCachedBranchMembers7263.filter (independentCachedEdge 36)=independentCachedBranchMembers7262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7262
end EntropyDesigns.QuadraticRefinement
