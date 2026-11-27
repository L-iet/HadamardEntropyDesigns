/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch139
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7264 : Finset ℕ := ([36,80,144,250,1582,1626,1650,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2714,2732,2738,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7264 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7264 1650 4
  · have he : independentCachedBranchMembers7264.erase 1650=independentCachedBranchMembers7260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7260
  · have he : independentCachedBranchMembers7264.filter (independentCachedEdge 1650)=independentCachedBranchMembers7263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7263
def independentCachedBranchMembers7265 : Finset ℕ := ([250,1582,1690,1708,1714,2650,2668,2674,2758,2776,2800,3130,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7265 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7265 4 (fun x => (if x<2674 then (if x<1708 then (if x<1582 then 0 else (if x<1690 then 1 else 0)) else (if x<2650 then (if x<1714 then 2 else 1) else (if x<2668 then 0 else 1))) else (if x<3130 then (if x<2776 then (if x<2758 then 2 else 3) else (if x<2800 then 3 else 1)) else (if x<3238 then (if x<3214 then 0 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7266 : Finset ℕ := ([1690,1714,2668,2758,3130,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7266 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7266 3 (fun x => (if x<2758 then (if x<1714 then 0 else (if x<2668 then 1 else 0)) else (if x<3130 then 2 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7267 : Finset ℕ := ([80,250,1582,1690,1708,1714,2650,2668,2674,2758,2776,2800,3130,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7267 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7267 80 3
  · have he : independentCachedBranchMembers7267.erase 80=independentCachedBranchMembers7265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7265
  · have he : independentCachedBranchMembers7267.filter (independentCachedEdge 80)=independentCachedBranchMembers7266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7266
def independentCachedBranchMembers7268 : Finset ℕ := ([36,80,144,250,1582,1626,1644,1650,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2714,2732,2738,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7268 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7268 1644 4
  · have he : independentCachedBranchMembers7268.erase 1644=independentCachedBranchMembers7264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7264
  · have he : independentCachedBranchMembers7268.filter (independentCachedEdge 1644)=independentCachedBranchMembers7267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7267
def independentCachedBranchMembers7269 : Finset ℕ := ([80,144,1582,1734,1752,1776,2606,2758,2776,2800,3150,3174,3192,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7269 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7269 4 (fun x => (if x<2776 then (if x<1752 then (if x<1582 then (if x<144 then 0 else 1) else (if x<1734 then 0 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2758 then 1 else 3))) else (if x<3192 then (if x<3150 then (if x<2800 then 0 else 3) else (if x<3174 then 2 else 1)) else (if x<3238 then (if x<3214 then 2 else 3) else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7270 : Finset ℕ := ([18,36,80,144,250,1582,1626,1644,1650,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2714,2732,2738,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7270 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7270 18 4
  · have he : independentCachedBranchMembers7270.erase 18=independentCachedBranchMembers7268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7268
  · have he : independentCachedBranchMembers7270.filter (independentCachedEdge 18)=independentCachedBranchMembers7269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7269
def independentCachedBranchMembers7271 : Finset ℕ := ([36,250,1626,1690,1734,1752,2650,2714,2758,2776,3130,3174,3192,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7271 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7271 4 (fun x => (if x<2758 then (if x<1734 then (if x<1626 then (if x<250 then 0 else 1) else (if x<1690 then 0 else 1)) else (if x<2650 then (if x<1752 then 2 else 2) else (if x<2714 then 1 else 0))) else (if x<3192 then (if x<3130 then (if x<2776 then 3 else 3) else (if x<3174 then 1 else 2)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7272 : Finset ℕ := ([12,18,36,80,144,250,1582,1626,1644,1650,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2714,2732,2738,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7272 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7272 12 4
  · have he : independentCachedBranchMembers7272.erase 12=independentCachedBranchMembers7270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7270
  · have he : independentCachedBranchMembers7272.filter (independentCachedEdge 12)=independentCachedBranchMembers7271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7271
def independentCachedBranchMembers7273 : Finset ℕ := ([12,18,36,48,68,80,132,144,238,250,1582,1594,1614,1626,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2758,2764,2770,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7273 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7273 3270 5
  · have he : independentCachedBranchMembers7273.erase 3270=independentCachedBranchMembers7251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7251
  · have he : independentCachedBranchMembers7273.filter (independentCachedEdge 3270)=independentCachedBranchMembers7272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7272
def independentCachedBranchMembers7274 : Finset ℕ := ([132,238,1582,1626,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7274 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7274 5 (fun x => (if x<2680 then (if x<1720 then (if x<1626 then (if x<238 then 0 else (if x<1582 then 0 else 1)) else (if x<1678 then 1 else (if x<1702 then 0 else 2))) else (if x<1764 then (if x<1740 then 1 else (if x<1746 then 1 else 2)) else (if x<2638 then (if x<2618 then 0 else 1) else (if x<2662 then 1 else 3)))) else (if x<3162 then (if x<2758 then (if x<2714 then 3 else (if x<2732 then 4 else 0)) else (if x<2800 then (if x<2776 then 0 else 1) else (if x<3118 then 4 else 2))) else (if x<3214 then (if x<3180 then 2 else (if x<3186 then 3 else 3)) else (if x<3256 then (if x<3238 then 4 else 0) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7275 : Finset ℕ := ([238,1720,1740,1764,2618,2638,2662,2714,2758,3180,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7275 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7275 4 (fun x => (if x<2662 then (if x<1764 then (if x<1720 then 0 else (if x<1740 then 1 else 0)) else (if x<2618 then 1 else (if x<2638 then 1 else 0))) else (if x<3180 then (if x<2714 then 1 else (if x<2758 then 2 else 2)) else (if x<3256 then 0 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7276 : Finset ℕ := ([80,132,238,1582,1626,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7276 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7276 80 4
  · have he : independentCachedBranchMembers7276.erase 80=independentCachedBranchMembers7274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7274
  · have he : independentCachedBranchMembers7276.filter (independentCachedEdge 80)=independentCachedBranchMembers7275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7275
def independentCachedBranchMembers7277 : Finset ℕ := ([132,1678,1720,1740,2618,2638,2680,2758,2800,3186,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7277 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7277 4 (fun x => (if x<2680 then (if x<1740 then (if x<1678 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2638 then 1 else 1))) else (if x<3186 then (if x<2758 then 0 else (if x<2800 then 2 else 2)) else (if x<3214 then 0 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7278 : Finset ℕ := ([36,80,132,238,1582,1626,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7278 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7278 36 4
  · have he : independentCachedBranchMembers7278.erase 36=independentCachedBranchMembers7276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7276
  · have he : independentCachedBranchMembers7278.filter (independentCachedEdge 36)=independentCachedBranchMembers7277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7277
def independentCachedBranchMembers7279 : Finset ℕ := ([132,238,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,3118,3162,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7279 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7279 4 (fun x => (if x<2618 then (if x<1720 then (if x<1678 then (if x<238 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3118 then (if x<2662 then (if x<2638 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3180 then (if x<3162 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7280 : Finset ℕ := ([36,80,132,238,1582,1626,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7280 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7280 3282 4
  · have he : independentCachedBranchMembers7280.erase 3282=independentCachedBranchMembers7278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7278
  · have he : independentCachedBranchMembers7280.filter (independentCachedEdge 3282)=independentCachedBranchMembers7279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7279
def independentCachedBranchMembers7281 : Finset ℕ := ([36,80,1582,1626,1702,1720,1740,1746,2662,2680,2714,2800,3180,3186,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7281 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7281 4 (fun x => (if x<2662 then (if x<1702 then (if x<1582 then (if x<80 then 0 else 0) else (if x<1626 then 0 else 0)) else (if x<1740 then (if x<1720 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3180 then (if x<2714 then (if x<2680 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3186 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7282 : Finset ℕ := ([36,80,132,238,1582,1626,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7282 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7282 3276 4
  · have he : independentCachedBranchMembers7282.erase 3276=independentCachedBranchMembers7280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7280
  · have he : independentCachedBranchMembers7282.filter (independentCachedEdge 3276)=independentCachedBranchMembers7281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7281
def independentCachedBranchMembers7283 : Finset ℕ := ([36,80,132,238,1582,1626,1678,1764,2618,2638,2714,2800,3118,3162,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7283 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7283 4 (fun x => (if x<2618 then (if x<1582 then (if x<132 then (if x<80 then 0 else 0) else (if x<238 then 1 else 1)) else (if x<1678 then (if x<1626 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3118 then (if x<2714 then (if x<2638 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3162 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7284 : Finset ℕ := ([36,80,132,238,1582,1626,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2738,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7284 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7284 2738 4
  · have he : independentCachedBranchMembers7284.erase 2738=independentCachedBranchMembers7282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7282
  · have he : independentCachedBranchMembers7284.filter (independentCachedEdge 2738)=independentCachedBranchMembers7283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7283
def independentCachedBranchMembers7285 : Finset ℕ := ([36,238,1626,1678,1740,1746,2638,2714,2758,2776,3118,3180,3186,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7285 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7285 4 (fun x => (if x<2758 then (if x<1740 then (if x<1626 then (if x<238 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1746 then 2 else 2) else (if x<2714 then 1 else 1))) else (if x<3186 then (if x<3118 then (if x<2776 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7286 : Finset ℕ := ([36,80,132,238,1582,1626,1650,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2738,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7286 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7286 1650 4
  · have he : independentCachedBranchMembers7286.erase 1650=independentCachedBranchMembers7284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7284
  · have he : independentCachedBranchMembers7286.filter (independentCachedEdge 1650)=independentCachedBranchMembers7285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7285
def independentCachedBranchMembers7287 : Finset ℕ := ([80,132,1582,1740,1746,1764,2618,2758,2776,2800,3162,3180,3186,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7287 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7287 4 (fun x => (if x<2776 then (if x<1746 then (if x<1582 then (if x<132 then 0 else 0) else (if x<1740 then 1 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2758 then 1 else 2))) else (if x<3186 then (if x<3162 then (if x<2800 then 1 else 2) else (if x<3180 then 0 else 3)) else (if x<3238 then (if x<3214 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7288 : Finset ℕ := ([36,80,132,238,1582,1626,1644,1650,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2738,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7288 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7288 1644 4
  · have he : independentCachedBranchMembers7288.erase 1644=independentCachedBranchMembers7286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7286
  · have he : independentCachedBranchMembers7288.filter (independentCachedEdge 1644)=independentCachedBranchMembers7287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7287
def independentCachedBranchMembers7289 : Finset ℕ := ([80,238,1582,1678,1702,1720,2638,2662,2680,2758,2776,2800,3118,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7289 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7289 4 (fun x => (if x<2680 then (if x<1702 then (if x<1582 then (if x<238 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<2638 then (if x<1720 then 2 else 2) else (if x<2662 then 1 else 2))) else (if x<3118 then (if x<2776 then (if x<2758 then 2 else 3) else (if x<2800 then 0 else 3)) else (if x<3238 then (if x<3214 then 1 else 3) else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7290 : Finset ℕ := ([18,36,80,132,238,1582,1626,1644,1650,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2738,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7290 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7290 18 4
  · have he : independentCachedBranchMembers7290.erase 18=independentCachedBranchMembers7288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7288
  · have he : independentCachedBranchMembers7290.filter (independentCachedEdge 18)=independentCachedBranchMembers7289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7289
def independentCachedBranchMembers7291 : Finset ℕ := ([36,132,1626,1702,1720,1764,2618,2662,2680,2714,2758,2776,3162,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7291 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7291 4 (fun x => (if x<2680 then (if x<1720 then (if x<1626 then (if x<132 then 0 else 1) else (if x<1702 then 0 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2662 then 2 else 2))) else (if x<3162 then (if x<2758 then (if x<2714 then 1 else 0) else (if x<2776 then 3 else 3)) else (if x<3256 then (if x<3238 then 1 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7292 : Finset ℕ := ([12,18,36,80,132,238,1582,1626,1644,1650,1678,1702,1720,1740,1746,1764,2618,2638,2662,2680,2714,2732,2738,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7292 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7292 12 4
  · have he : independentCachedBranchMembers7292.erase 12=independentCachedBranchMembers7290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7290
  · have he : independentCachedBranchMembers7292.filter (independentCachedEdge 12)=independentCachedBranchMembers7291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7291
def independentCachedBranchMembers7293 : Finset ℕ := ([12,18,36,48,68,80,132,144,238,250,1582,1594,1614,1626,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2744,2758,2764,2770,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7293 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7293 2744 5
  · have he : independentCachedBranchMembers7293.erase 2744=independentCachedBranchMembers7273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7273
  · have he : independentCachedBranchMembers7293.filter (independentCachedEdge 2744)=independentCachedBranchMembers7292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7292
def independentCachedBranchMembers7294 : Finset ℕ := ([144,250,1594,1614,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7294 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7294 5 (fun x => (if x<2680 then (if x<1720 then (if x<1614 then (if x<250 then 0 else (if x<1594 then 0 else 1)) else (if x<1690 then 1 else (if x<1702 then 0 else 1))) else (if x<1776 then (if x<1740 then 2 else (if x<1746 then 2 else 1)) else (if x<2650 then (if x<2606 then 0 else 1) else (if x<2662 then 1 else 3)))) else (if x<3150 then (if x<2758 then (if x<2702 then 3 else (if x<2738 then 4 else 0)) else (if x<2788 then (if x<2776 then 1 else 0) else (if x<3130 then 4 else 2))) else (if x<3226 then (if x<3180 then 2 else (if x<3186 then 3 else 3)) else (if x<3256 then (if x<3238 then 4 else 3) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7295 : Finset ℕ := ([250,1702,1746,1776,2606,2650,2680,2702,2776,3186,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7295 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7295 4 (fun x => (if x<2680 then (if x<1776 then (if x<1702 then 0 else (if x<1746 then 1 else 0)) else (if x<2606 then 1 else (if x<2650 then 1 else 0))) else (if x<3186 then (if x<2702 then 1 else (if x<2776 then 2 else 2)) else (if x<3238 then 0 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
