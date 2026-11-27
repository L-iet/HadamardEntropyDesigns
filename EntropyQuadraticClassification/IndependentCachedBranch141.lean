/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch140
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7296 : Finset ℕ := ([68,144,250,1594,1614,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7296 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7296 68 4
  · have he : independentCachedBranchMembers7296.erase 68=independentCachedBranchMembers7294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7294
  · have he : independentCachedBranchMembers7296.filter (independentCachedEdge 68)=independentCachedBranchMembers7295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7295
def independentCachedBranchMembers7297 : Finset ℕ := ([144,1690,1702,1746,2606,2650,2662,2776,2788,3180,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound7297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7297 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7297 4 (fun x => (if x<2662 then (if x<1746 then (if x<1690 then 0 else (if x<1702 then 0 else 1)) else (if x<2606 then 1 else (if x<2650 then 1 else 1))) else (if x<3180 then (if x<2776 then 0 else (if x<2788 then 2 else 2)) else (if x<3226 then 0 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7298 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7298 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7298 48 4
  · have he : independentCachedBranchMembers7298.erase 48=independentCachedBranchMembers7296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7296
  · have he : independentCachedBranchMembers7298.filter (independentCachedEdge 48)=independentCachedBranchMembers7297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7297
def independentCachedBranchMembers7299 : Finset ℕ := ([48,68,1594,1614,1702,1720,1740,1746,2662,2680,2702,2788,3180,3186,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7299 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7299 4 (fun x => (if x<2662 then (if x<1702 then (if x<1594 then (if x<68 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1740 then (if x<1720 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3180 then (if x<2702 then (if x<2680 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3186 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7300 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7300 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7300 3282 4
  · have he : independentCachedBranchMembers7300.erase 3282=independentCachedBranchMembers7298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7298
  · have he : independentCachedBranchMembers7300.filter (independentCachedEdge 3282)=independentCachedBranchMembers7299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7299
def independentCachedBranchMembers7301 : Finset ℕ := ([144,250,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,3130,3150,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7301 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7301 4 (fun x => (if x<2606 then (if x<1720 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3130 then (if x<2662 then (if x<2650 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3180 then (if x<3150 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7302 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7302 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7302 3276 4
  · have he : independentCachedBranchMembers7302.erase 3276=independentCachedBranchMembers7300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7300
  · have he : independentCachedBranchMembers7302.filter (independentCachedEdge 3276)=independentCachedBranchMembers7301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7301
def independentCachedBranchMembers7303 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1776,2606,2650,2702,2788,3130,3150,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7303 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7303 4 (fun x => (if x<2606 then (if x<1594 then (if x<144 then (if x<68 then 0 else 0) else (if x<250 then 1 else 1)) else (if x<1690 then (if x<1614 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3130 then (if x<2702 then (if x<2650 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3150 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7304 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2732,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7304 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7304 2732 4
  · have he : independentCachedBranchMembers7304.erase 2732=independentCachedBranchMembers7302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7302
  · have he : independentCachedBranchMembers7304.filter (independentCachedEdge 2732)=independentCachedBranchMembers7303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7303
def independentCachedBranchMembers7305 : Finset ℕ := ([68,144,1594,1740,1746,1776,2606,2758,2776,2788,3150,3180,3186,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7305 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7305 4 (fun x => (if x<2776 then (if x<1746 then (if x<1594 then (if x<144 then 0 else 0) else (if x<1740 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2758 then 1 else 1))) else (if x<3186 then (if x<3150 then (if x<2788 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3238 then (if x<3226 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7306 : Finset ℕ := ([48,68,144,250,1594,1614,1650,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2732,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7306 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7306 1650 4
  · have he : independentCachedBranchMembers7306.erase 1650=independentCachedBranchMembers7304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7304
  · have he : independentCachedBranchMembers7306.filter (independentCachedEdge 1650)=independentCachedBranchMembers7305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7305
def independentCachedBranchMembers7307 : Finset ℕ := ([48,250,1614,1690,1740,1746,2650,2702,2758,2776,3130,3180,3186,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7307 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7307 4 (fun x => (if x<2758 then (if x<1740 then (if x<1614 then (if x<250 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1746 then 2 else 2) else (if x<2702 then 1 else 1))) else (if x<3186 then (if x<3130 then (if x<2776 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7308 : Finset ℕ := ([48,68,144,250,1594,1614,1644,1650,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2732,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7308 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7308 1644 4
  · have he : independentCachedBranchMembers7308.erase 1644=independentCachedBranchMembers7306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7306
  · have he : independentCachedBranchMembers7308.filter (independentCachedEdge 1644)=independentCachedBranchMembers7307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7307
def independentCachedBranchMembers7309 : Finset ℕ := ([48,144,1614,1702,1720,1776,2606,2662,2680,2702,2758,2776,3150,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7309 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7309 4 (fun x => (if x<2680 then (if x<1720 then (if x<1614 then (if x<144 then 0 else 1) else (if x<1702 then 0 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2662 then 2 else 1))) else (if x<3150 then (if x<2758 then (if x<2702 then 2 else 0) else (if x<2776 then 3 else 3)) else (if x<3256 then (if x<3238 then 1 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7310 : Finset ℕ := ([18,48,68,144,250,1594,1614,1644,1650,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2732,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7310 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7310 18 4
  · have he : independentCachedBranchMembers7310.erase 18=independentCachedBranchMembers7308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7308
  · have he : independentCachedBranchMembers7310.filter (independentCachedEdge 18)=independentCachedBranchMembers7309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7309
def independentCachedBranchMembers7311 : Finset ℕ := ([68,250,1594,1690,1702,1720,2650,2662,2680,2758,2776,2788,3130,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7311 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7311 4 (fun x => (if x<2680 then (if x<1702 then (if x<1594 then (if x<250 then 0 else 1) else (if x<1690 then 0 else 1)) else (if x<2650 then (if x<1720 then 2 else 2) else (if x<2662 then 1 else 2))) else (if x<3130 then (if x<2776 then (if x<2758 then 2 else 0) else (if x<2788 then 3 else 3)) else (if x<3238 then (if x<3226 then 1 else 3) else (if x<3256 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7312 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1702,1720,1740,1746,1776,2606,2650,2662,2680,2702,2732,2738,2758,2776,2788,3130,3150,3180,3186,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7312 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7312 12 4
  · have he : independentCachedBranchMembers7312.erase 12=independentCachedBranchMembers7310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7310
  · have he : independentCachedBranchMembers7312.filter (independentCachedEdge 12)=independentCachedBranchMembers7311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7311
def independentCachedBranchMembers7313 : Finset ℕ := ([12,18,36,48,68,80,132,144,238,250,1582,1594,1614,1626,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2726,2732,2738,2744,2758,2764,2770,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7313 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7313 2726 5
  · have he : independentCachedBranchMembers7313.erase 2726=independentCachedBranchMembers7293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7293
  · have he : independentCachedBranchMembers7313.filter (independentCachedEdge 2726)=independentCachedBranchMembers7312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7312
def independentCachedBranchMembers7314 : Finset ℕ := ([12,18,20,34,36,40,48,66,68,72,80,130,132,136,144,160,190,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7314 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7314 20 6
  · have he : independentCachedBranchMembers7314.erase 20=independentCachedBranchMembers7062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7062
  · have he : independentCachedBranchMembers7314.filter (independentCachedEdge 20)=independentCachedBranchMembers7313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7313
def independentCachedBranchMembers7315 : Finset ℕ := ([12,18,40,66,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2770,2792,3126,3164,3180,3186,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7315 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7315 6 (fun x => (if x<2662 then (if x<1692 then (if x<1596 then (if x<40 then (if x<18 then 0 else 0) else (if x<66 then 1 else 1)) else (if x<1644 then (if x<1622 then 1 else 1) else (if x<1650 then 0 else 0))) else (if x<1752 then (if x<1714 then (if x<1708 then 2 else 3) else (if x<1734 then 2 else 2)) else (if x<2620 then (if x<1768 then 3 else 2) else (if x<2646 then 4 else 4)))) else (if x<3164 then (if x<2738 then (if x<2716 then (if x<2680 then 5 else 5) else (if x<2732 then 3 else 0)) else (if x<2792 then (if x<2770 then 0 else 1) else (if x<3126 then 3 else 4))) else (if x<3244 then (if x<3186 then (if x<3180 then 4 else 5) else (if x<3222 then 5 else 2)) else (if x<3276 then (if x<3256 then 1 else 2) else (if x<3282 then 0 else (if x<3298 then 0 else 2)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7316 : Finset ℕ := ([18,66,1622,1650,1714,1734,2646,2662,2738,2770,3126,3186,3222,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7316 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7316 5 (fun x => (if x<2662 then (if x<1650 then (if x<66 then 0 else (if x<1622 then 1 else 0)) else (if x<1734 then (if x<1714 then 1 else 0) else (if x<2646 then 1 else 1))) else (if x<3186 then (if x<2770 then (if x<2738 then 2 else 2) else (if x<3126 then 0 else 2)) else (if x<3282 then (if x<3222 then 0 else 0) else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7317 : Finset ℕ := ([12,18,40,66,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2770,2792,3126,3164,3180,3186,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7317 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7317 252 5
  · have he : independentCachedBranchMembers7317.erase 252=independentCachedBranchMembers7315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7315
  · have he : independentCachedBranchMembers7317.filter (independentCachedEdge 252)=independentCachedBranchMembers7316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7316
def independentCachedBranchMembers7318 : Finset ℕ := ([12,40,1596,1644,1714,1734,2620,2680,2738,2770,3164,3180,3222,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7318 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7318 5 (fun x => (if x<2680 then (if x<1644 then (if x<40 then 0 else (if x<1596 then 1 else 0)) else (if x<1734 then (if x<1714 then 1 else 0) else (if x<2620 then 1 else 1))) else (if x<3180 then (if x<2770 then (if x<2738 then 2 else 2) else (if x<3164 then 0 else 2)) else (if x<3282 then (if x<3222 then 0 else 2) else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7319 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2770,2792,3126,3164,3180,3186,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7319 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7319 136 5
  · have he : independentCachedBranchMembers7319.erase 136=independentCachedBranchMembers7317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7317
  · have he : independentCachedBranchMembers7319.filter (independentCachedEdge 136)=independentCachedBranchMembers7318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7318
def independentCachedBranchMembers7320 : Finset ℕ := ([12,18,66,136,1622,1692,1708,1714,2646,2662,2680,2716,2732,2738,2770,3164,3180,3186,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7320 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7320 5 (fun x => (if x<2680 then (if x<1692 then (if x<66 then (if x<18 then 0 else 0) else (if x<136 then 1 else (if x<1622 then 1 else 1))) else (if x<1714 then (if x<1708 then 1 else 0) else (if x<2646 then 0 else (if x<2662 then 2 else 1)))) else (if x<3164 then (if x<2732 then (if x<2716 then 2 else 2) else (if x<2738 then 1 else (if x<2770 then 2 else 0))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3222 then 0 else (if x<3256 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7321 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2770,2792,3126,3164,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7321 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7321 3192 5
  · have he : independentCachedBranchMembers7321.erase 3192=independentCachedBranchMembers7319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7319
  · have he : independentCachedBranchMembers7321.filter (independentCachedEdge 3192)=independentCachedBranchMembers7320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7320
def independentCachedBranchMembers7322 : Finset ℕ := ([12,18,40,252,1596,1708,1714,1768,2620,2662,2680,2732,2738,2770,2792,3126,3180,3186,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7322 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7322 5 (fun x => (if x<2680 then (if x<1708 then (if x<40 then (if x<18 then 0 else 0) else (if x<252 then 1 else (if x<1596 then 1 else 1))) else (if x<1768 then (if x<1714 then 0 else 0) else (if x<2620 then 1 else (if x<2662 then 2 else 2)))) else (if x<3126 then (if x<2738 then (if x<2732 then 1 else 1) else (if x<2770 then 2 else (if x<2792 then 0 else 2))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3256 then 0 else (if x<3298 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7323 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2770,2792,3126,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7323 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7323 3174 5
  · have he : independentCachedBranchMembers7323.erase 3174=independentCachedBranchMembers7321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7321
  · have he : independentCachedBranchMembers7323.filter (independentCachedEdge 3174)=independentCachedBranchMembers7322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7322
def independentCachedBranchMembers7324 : Finset ℕ := ([40,252,1596,1644,1650,1734,1752,1768,2646,2662,2680,2716,2732,2738,2770,3164,3180,3186,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7324 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7324 5 (fun x => (if x<2680 then (if x<1734 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<1768 then (if x<1752 then 1 else 1) else (if x<2646 then 0 else (if x<2662 then 2 else 1)))) else (if x<3164 then (if x<2732 then (if x<2716 then 0 else 2) else (if x<2738 then 0 else (if x<2770 then 2 else 1))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3222 then 2 else (if x<3256 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7325 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2674,2680,2716,2732,2738,2770,2792,3126,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7325 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7325 2674 5
  · have he : independentCachedBranchMembers7325.erase 2674=independentCachedBranchMembers7323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7323
  · have he : independentCachedBranchMembers7325.filter (independentCachedEdge 2674)=independentCachedBranchMembers7324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7324
def independentCachedBranchMembers7326 : Finset ℕ := ([66,136,1622,1644,1650,1692,1734,1752,2620,2662,2680,2732,2738,2770,2792,3126,3180,3186,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7326 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7326 5 (fun x => (if x<2680 then (if x<1692 then (if x<1622 then (if x<136 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<2620 then 1 else (if x<2662 then 2 else 0)))) else (if x<3126 then (if x<2738 then (if x<2732 then 1 else 0) else (if x<2770 then 2 else (if x<2792 then 1 else 2))) else (if x<3186 then (if x<3180 then 2 else 2) else (if x<3256 then 0 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7327 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2668,2674,2680,2716,2732,2738,2770,2792,3126,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7327 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7327 2668 5
  · have he : independentCachedBranchMembers7327.erase 2668=independentCachedBranchMembers7325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7325
  · have he : independentCachedBranchMembers7327.filter (independentCachedEdge 2668)=independentCachedBranchMembers7326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7326
end EntropyDesigns.QuadraticRefinement
