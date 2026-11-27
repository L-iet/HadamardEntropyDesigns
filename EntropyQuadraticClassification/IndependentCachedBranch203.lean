/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch202
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9280 : Finset ℕ := ([3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9280 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9280 3174 4
  · have he : independentCachedBranchMembers9280.erase 3174=independentCachedBranchMembers9278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9278
  · have he : independentCachedBranchMembers9280.filter (independentCachedEdge 3174)=independentCachedBranchMembers9279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9279
def independentCachedBranchMembers9281 : Finset ℕ := ([3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9281 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9281 4 (fun x => (if x<3214 then (if x<3150 then (if x<3130 then (if x<3126 then 0 else 1) else (if x<3132 then 2 else 3)) else (if x<3162 then (if x<3158 then 1 else 0) else (if x<3164 then 3 else 2))) else (if x<3298 then (if x<3226 then (if x<3222 then 2 else 3) else (if x<3228 then 0 else 1)) else (if x<3304 then (if x<3300 then 0 else 1) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9282 : Finset ℕ := ([3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9282 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9282 3102 4
  · have he : independentCachedBranchMembers9282.erase 3102=independentCachedBranchMembers9280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9280
  · have he : independentCachedBranchMembers9282.filter (independentCachedEdge 3102)=independentCachedBranchMembers9281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9281
def independentCachedBranchMembers9283 : Finset ℕ := ([2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9283 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9283 2560 5
  · have he : independentCachedBranchMembers9283.erase 2560=independentCachedBranchMembers9257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9257
  · have he : independentCachedBranchMembers9283.filter (independentCachedEdge 2560)=independentCachedBranchMembers9282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9282
def independentCachedBranchMembers9284 : Finset ℕ := ([10,12,18,20,34,36,40,48,66,68,72,80,130,132,136,144,160,190,192,222,238,246,250,252,1536,1566,1582,1590,1594,1596,1614,1622,1626,1628,1638,1642,1644,1650,1652,1656,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9284 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9284 1536 6
  · have he : independentCachedBranchMembers9284.erase 1536=independentCachedBranchMembers8938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8938
  · have he : independentCachedBranchMembers9284.filter (independentCachedEdge 1536)=independentCachedBranchMembers9283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9283
def independentCachedBranchMembers9285 : Finset ℕ := ([160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,2714,2716,2726,2738,2758,2772,2792,2800,3222,3244,3250,3256,3274,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9285 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9285 6 (fun x => (if x<2726 then (if x<1720 then (if x<250 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<1706 then (if x<252 then 1 else 2) else (if x<1716 then 3 else 0))) else (if x<1762 then (if x<1746 then (if x<1740 then 2 else 2) else (if x<1752 then 1 else 3)) else (if x<2714 then (if x<1764 then 0 else 3) else (if x<2716 then 3 else 2)))) else (if x<3250 then (if x<2792 then (if x<2758 then (if x<2738 then 0 else 4) else (if x<2772 then 4 else 3)) else (if x<3222 then (if x<2800 then 2 else 0) else (if x<3244 then 4 else 2))) else (if x<3288 then (if x<3274 then (if x<3256 then 0 else 4) else (if x<3284 then 1 else 5)) else (if x<3300 then (if x<3298 then 2 else 4) else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9286 : Finset ℕ := ([160,192,1706,1740,1762,1764,2726,2758,2792,3244,3274,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9286 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9286 5 (fun x => (if x<2726 then (if x<1740 then (if x<192 then 0 else (if x<1706 then 1 else 0)) else (if x<1762 then 1 else (if x<1764 then 1 else 0))) else (if x<3244 then (if x<2758 then 0 else (if x<2792 then 1 else 0)) else (if x<3298 then (if x<3274 then 0 else 1) else (if x<3300 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9287 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,2714,2716,2726,2738,2758,2772,2792,2800,3222,3244,3250,3256,3274,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9287 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9287 144 5
  · have he : independentCachedBranchMembers9287.erase 144=independentCachedBranchMembers9285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9285
  · have he : independentCachedBranchMembers9287.filter (independentCachedEdge 144)=independentCachedBranchMembers9286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9286
def independentCachedBranchMembers9288 : Finset ℕ := ([1716,1720,1746,1752,1762,1764,2714,2716,2726,2758,2800,3222,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9288 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9288 5 (fun x => (if x<2716 then (if x<1752 then (if x<1720 then 0 else (if x<1746 then 1 else 0)) else (if x<1764 then (if x<1762 then 2 else 1) else (if x<2714 then 2 else 2))) else (if x<3222 then (if x<2758 then (if x<2726 then 1 else 2) else (if x<2800 then 1 else 0)) else (if x<3274 then (if x<3244 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9289 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1776,2714,2716,2726,2738,2758,2772,2792,2800,3222,3244,3250,3256,3274,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9289 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9289 1776 5
  · have he : independentCachedBranchMembers9289.erase 1776=independentCachedBranchMembers9287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9287
  · have he : independentCachedBranchMembers9289.filter (independentCachedEdge 1776)=independentCachedBranchMembers9288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9288
def independentCachedBranchMembers9290 : Finset ℕ := ([144,160,246,252,1720,1764,1776,2714,2758,2792,3222,3244,3250,3256,3274,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9290 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9290 5 (fun x => (if x<2792 then (if x<1720 then (if x<246 then (if x<160 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1776 then (if x<1764 then 1 else 1) else (if x<2714 then 0 else (if x<2758 then 2 else 2)))) else (if x<3256 then (if x<3244 then (if x<3222 then 1 else 2) else (if x<3250 then 1 else 0)) else (if x<3284 then (if x<3274 then 2 else 2) else (if x<3300 then 0 else (if x<3312 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9291 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1776,2714,2716,2726,2738,2758,2762,2772,2792,2800,3222,3244,3250,3256,3274,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9291 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9291 2762 5
  · have he : independentCachedBranchMembers9291.erase 2762=independentCachedBranchMembers9289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9289
  · have he : independentCachedBranchMembers9291.filter (independentCachedEdge 2762)=independentCachedBranchMembers9290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9290
def independentCachedBranchMembers9292 : Finset ℕ := ([144,192,246,250,1752,1762,1776,2716,2726,2792,3222,3244,3250,3274,3284,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9292 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9292 5 (fun x => (if x<2792 then (if x<1752 then (if x<246 then (if x<192 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1776 then (if x<1762 then 1 else 1) else (if x<2716 then 0 else (if x<2726 then 2 else 2)))) else (if x<3274 then (if x<3244 then (if x<3222 then 1 else 2) else (if x<3250 then 2 else 0)) else (if x<3288 then (if x<3284 then 1 else 0) else (if x<3298 then 2 else (if x<3312 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9293 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1776,2714,2716,2726,2732,2738,2758,2762,2772,2792,2800,3222,3244,3250,3256,3274,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9293 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9293 2732 5
  · have he : independentCachedBranchMembers9293.erase 2732=independentCachedBranchMembers9291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9291
  · have he : independentCachedBranchMembers9293.filter (independentCachedEdge 2732)=independentCachedBranchMembers9292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9292
def independentCachedBranchMembers9294 : Finset ℕ := ([160,252,1706,1716,1720,1740,1746,1764,2716,2726,2792,3222,3244,3250,3274,3284,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9294 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9294 5 (fun x => (if x<2726 then (if x<1720 then (if x<1706 then (if x<252 then 0 else 0) else (if x<1716 then 1 else 0)) else (if x<1746 then (if x<1740 then 2 else 1) else (if x<1764 then 1 else (if x<2716 then 2 else 3)))) else (if x<3274 then (if x<3222 then (if x<2792 then 3 else 2) else (if x<3244 then 3 else (if x<3250 then 0 else 1))) else (if x<3288 then (if x<3284 then 1 else 1) else (if x<3298 then 3 else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9295 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1776,2714,2716,2726,2732,2738,2758,2762,2772,2792,2800,3222,3244,3250,3256,3274,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9295 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9295 3282 5
  · have he : independentCachedBranchMembers9295.erase 3282=independentCachedBranchMembers9293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9293
  · have he : independentCachedBranchMembers9295.filter (independentCachedEdge 3282)=independentCachedBranchMembers9294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9294
def independentCachedBranchMembers9296 : Finset ℕ := ([192,250,1706,1716,1740,1746,1752,1762,2714,2758,2792,3222,3244,3250,3256,3274,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9296 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9296 5 (fun x => (if x<2758 then (if x<1740 then (if x<1706 then (if x<250 then 0 else 0) else (if x<1716 then 1 else 1)) else (if x<1752 then (if x<1746 then 1 else 0) else (if x<1762 then 2 else (if x<2714 then 2 else 3)))) else (if x<3256 then (if x<3222 then (if x<2792 then 3 else 2) else (if x<3244 then 3 else (if x<3250 then 1 else 1))) else (if x<3284 then (if x<3274 then 3 else 0) else (if x<3300 then 1 else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9297 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1776,2714,2716,2726,2732,2738,2758,2762,2772,2792,2800,3222,3244,3250,3252,3256,3274,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9297 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9297 3252 5
  · have he : independentCachedBranchMembers9297.erase 3252=independentCachedBranchMembers9295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9295
  · have he : independentCachedBranchMembers9297.filter (independentCachedEdge 3252)=independentCachedBranchMembers9296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9296
def independentCachedBranchMembers9298 : Finset ℕ := ([144,160,246,250,1706,1716,1720,1740,1746,1762,1776,2714,2726,2800,3244,3250,3274,3284,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9298 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9298 5 (fun x => (if x<1776 then (if x<1716 then (if x<246 then (if x<160 then 0 else 1) else (if x<250 then 0 else (if x<1706 then 1 else 1))) else (if x<1740 then (if x<1720 then 0 else 2) else (if x<1746 then 2 else (if x<1762 then 0 else 2)))) else (if x<3250 then (if x<2726 then (if x<2714 then 1 else 3) else (if x<2800 then 3 else (if x<3244 then 0 else 4))) else (if x<3284 then (if x<3274 then 0 else 4) else (if x<3288 then 0 else (if x<3300 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9299 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1776,2714,2716,2726,2732,2738,2758,2762,2772,2792,2800,3222,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9299 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9299 3276 5
  · have he : independentCachedBranchMembers9299.erase 3276=independentCachedBranchMembers9297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9297
  · have he : independentCachedBranchMembers9299.filter (independentCachedEdge 3276)=independentCachedBranchMembers9298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9298
def independentCachedBranchMembers9300 : Finset ℕ := ([144,192,246,252,1706,1716,1740,1746,1752,1764,1776,2716,2758,2800,3244,3250,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9300 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9300 5 (fun x => (if x<1776 then (if x<1716 then (if x<246 then (if x<192 then 0 else 1) else (if x<252 then 0 else (if x<1706 then 1 else 2))) else (if x<1746 then (if x<1740 then 0 else 1) else (if x<1752 then 0 else (if x<1764 then 2 else 2)))) else (if x<3250 then (if x<2758 then (if x<2716 then 1 else 3) else (if x<2800 then 3 else (if x<3244 then 0 else 4))) else (if x<3274 then (if x<3256 then 0 else 3) else (if x<3284 then 4 else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9301 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1776,2714,2716,2726,2732,2738,2758,2762,2772,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9301 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9301 3242 5
  · have he : independentCachedBranchMembers9301.erase 3242=independentCachedBranchMembers9299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9299
  · have he : independentCachedBranchMembers9301.filter (independentCachedEdge 3242)=independentCachedBranchMembers9300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9300
def independentCachedBranchMembers9302 : Finset ℕ := ([144,246,1706,1720,1740,1752,1762,1764,1776,2714,2716,2726,2738,2758,2772,2792,3250,3252,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9302 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9302 5 (fun x => (if x<2716 then (if x<1752 then (if x<1706 then (if x<246 then 0 else 0) else (if x<1720 then 1 else (if x<1740 then 2 else 1))) else (if x<1764 then (if x<1762 then 3 else 2) else (if x<1776 then 3 else (if x<2714 then 0 else 3)))) else (if x<2792 then (if x<2738 then (if x<2726 then 2 else 3) else (if x<2758 then 0 else (if x<2772 then 2 else 0))) else (if x<3252 then (if x<3250 then 1 else 4) else (if x<3282 then 0 else (if x<3284 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9303 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2758,2762,2772,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9303 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9303 1768 5
  · have he : independentCachedBranchMembers9303.erase 1768=independentCachedBranchMembers9301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9301
  · have he : independentCachedBranchMembers9303.filter (independentCachedEdge 1768)=independentCachedBranchMembers9302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9302
def independentCachedBranchMembers9304 : Finset ℕ := ([144,252,1716,1720,1740,1752,1762,2716,2726,2738,2758,2762,2792,2800,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9304 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9304 5 (fun x => (if x<2762 then (if x<1752 then (if x<1716 then (if x<252 then 0 else 0) else (if x<1720 then 0 else (if x<1740 then 1 else 1))) else (if x<2726 then (if x<1762 then 0 else (if x<2716 then 1 else 0)) else (if x<2738 then 2 else (if x<2758 then 1 else 1)))) else (if x<3252 then (if x<2800 then (if x<2792 then 2 else 1) else (if x<3222 then 0 else (if x<3244 then 3 else 3))) else (if x<3284 then (if x<3256 then 2 else (if x<3276 then 0 else 4)) else (if x<3288 then 0 else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9305 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2758,2762,2772,2786,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9305 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9305 2786 5
  · have he : independentCachedBranchMembers9305.erase 2786=independentCachedBranchMembers9303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9303
  · have he : independentCachedBranchMembers9305.filter (independentCachedEdge 2786)=independentCachedBranchMembers9304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9304
def independentCachedBranchMembers9306 : Finset ℕ := ([192,246,1720,1740,1746,1762,1764,2714,2716,2732,2738,2758,2792,2800,3222,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9306 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9306 5 (fun x => (if x<2758 then (if x<1762 then (if x<1720 then (if x<246 then 0 else 0) else (if x<1740 then 1 else (if x<1746 then 1 else 0))) else (if x<2716 then (if x<1764 then 1 else (if x<2714 then 0 else 2)) else (if x<2732 then 1 else (if x<2738 then 2 else 1)))) else (if x<3274 then (if x<2800 then (if x<2792 then 0 else 1) else (if x<3222 then 0 else (if x<3256 then 3 else 2))) else (if x<3284 then (if x<3276 then 3 else (if x<3282 then 4 else 2)) else (if x<3298 then 0 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9307 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2786,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9307 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9307 2744 5
  · have he : independentCachedBranchMembers9307.erase 2744=independentCachedBranchMembers9305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9305
  · have he : independentCachedBranchMembers9307.filter (independentCachedEdge 2744)=independentCachedBranchMembers9306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9306
def independentCachedBranchMembers9308 : Finset ℕ := ([144,160,250,252,1720,1740,1746,1762,1764,2714,2716,2732,2738,2758,2792,2800,3242,3244,3250,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9308 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9308 5 (fun x => (if x<2732 then (if x<1740 then (if x<250 then (if x<160 then 0 else 1) else (if x<252 then 0 else (if x<1720 then 1 else 0))) else (if x<1764 then (if x<1746 then 2 else (if x<1762 then 0 else 2)) else (if x<2714 then 1 else (if x<2716 then 0 else 2)))) else (if x<3242 then (if x<2758 then (if x<2738 then 1 else 2) else (if x<2792 then 2 else (if x<2800 then 2 else 0))) else (if x<3252 then (if x<3244 then 3 else (if x<3250 then 4 else 0)) else (if x<3288 then 1 else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9309 : Finset ℕ := ([144,160,192,246,250,252,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2786,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9309 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9309 1734 5
  · have he : independentCachedBranchMembers9309.erase 1734=independentCachedBranchMembers9307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9307
  · have he : independentCachedBranchMembers9309.filter (independentCachedEdge 1734)=independentCachedBranchMembers9308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9308
def independentCachedBranchMembers9310 : Finset ℕ := ([160,192,246,250,1716,1720,1740,1752,1762,2716,2726,2738,2758,2762,2792,2800,3242,3250,3274,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9310 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9310 5 (fun x => (if x<2738 then (if x<1720 then (if x<246 then (if x<192 then 0 else 1) else (if x<250 then 0 else (if x<1716 then 1 else 0))) else (if x<1762 then (if x<1740 then 2 else (if x<1752 then 2 else 1)) else (if x<2716 then 0 else (if x<2726 then 2 else 0)))) else (if x<3242 then (if x<2762 then (if x<2758 then 2 else 2) else (if x<2792 then 1 else (if x<2800 then 2 else 0))) else (if x<3282 then (if x<3250 then 3 else (if x<3274 then 0 else 4)) else (if x<3300 then 1 else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9311 : Finset ℕ := ([144,160,192,246,250,252,1692,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2786,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9311 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9311 1692 5
  · have he : independentCachedBranchMembers9311.erase 1692=independentCachedBranchMembers9309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9309
  · have he : independentCachedBranchMembers9311.filter (independentCachedEdge 1692)=independentCachedBranchMembers9310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9310
end EntropyDesigns.QuadraticRefinement
