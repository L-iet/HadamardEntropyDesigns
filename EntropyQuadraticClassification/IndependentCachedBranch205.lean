/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch204
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9344 : Finset ℕ := ([160,192,246,1702,1716,1734,1746,1762,1764,1776,2726,2738,2758,2772,2786,2788,2800,3250,3252,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9344 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9344 3312 4
  · have he : independentCachedBranchMembers9344.erase 3312=independentCachedBranchMembers9340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9340
  · have he : independentCachedBranchMembers9344.filter (independentCachedEdge 3312)=independentCachedBranchMembers9343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9343
def independentCachedBranchMembers9345 : Finset ℕ := ([160,192,1762,1764,1776,2786,2788,2800,3250,3252,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9345 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9345 4 (fun x => (if x<2788 then (if x<1764 then (if x<192 then 0 else (if x<1762 then 1 else 0)) else (if x<1776 then 1 else (if x<2786 then 2 else 1))) else (if x<3252 then (if x<2800 then 0 else (if x<3250 then 3 else 2)) else (if x<3282 then 3 else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9346 : Finset ℕ := ([160,192,246,1702,1716,1734,1746,1762,1764,1776,2726,2738,2758,2772,2786,2788,2800,3222,3250,3252,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9346 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9346 3222 4
  · have he : independentCachedBranchMembers9346.erase 3222=independentCachedBranchMembers9344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9344
  · have he : independentCachedBranchMembers9346.filter (independentCachedEdge 3222)=independentCachedBranchMembers9345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9345
def independentCachedBranchMembers9347 : Finset ℕ := ([160,192,1702,1734,1762,1764,2726,2758,2786,2788,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9347 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9347 4 (fun x => (if x<2726 then (if x<1734 then (if x<192 then 0 else (if x<1702 then 1 else 0)) else (if x<1762 then 1 else (if x<1764 then 2 else 3))) else (if x<2788 then (if x<2758 then 2 else (if x<2786 then 3 else 0)) else (if x<3298 then 1 else (if x<3300 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9348 : Finset ℕ := ([144,160,192,246,1702,1716,1734,1746,1762,1764,1776,2726,2738,2758,2772,2786,2788,2800,3222,3250,3252,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9348 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9348 144 4
  · have he : independentCachedBranchMembers9348.erase 144=independentCachedBranchMembers9346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9346
  · have he : independentCachedBranchMembers9348.filter (independentCachedEdge 144)=independentCachedBranchMembers9347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9347
def independentCachedBranchMembers9349 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9349 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9349 136 5
  · have he : independentCachedBranchMembers9349.erase 136=independentCachedBranchMembers9339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9339
  · have he : independentCachedBranchMembers9349.filter (independentCachedEdge 136)=independentCachedBranchMembers9348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9348
def independentCachedBranchMembers9350 : Finset ℕ := ([136,160,238,252,1692,1702,1706,1716,1720,1740,1746,1764,1768,2714,2732,2738,2758,2762,2772,2776,2786,2800,3214,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9350 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9350 5 (fun x => (if x<2738 then (if x<1716 then (if x<252 then (if x<160 then 0 else (if x<238 then 1 else 0)) else (if x<1702 then (if x<1692 then 1 else 2) else (if x<1706 then 2 else 0))) else (if x<1764 then (if x<1740 then (if x<1720 then 1 else 3) else (if x<1746 then 0 else 2)) else (if x<2714 then (if x<1768 then 3 else 1) else (if x<2732 then 3 else 0)))) else (if x<3214 then (if x<2772 then (if x<2758 then 4 else (if x<2762 then 3 else 0)) else (if x<2786 then (if x<2776 then 4 else 2) else (if x<2800 then 2 else 1))) else (if x<3276 then (if x<3252 then (if x<3242 then 0 else 4) else (if x<3256 then 4 else 1)) else (if x<3300 then (if x<3282 then 4 else 4) else (if x<3304 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9351 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2770,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9351 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9351 2770 5
  · have he : independentCachedBranchMembers9351.erase 2770=independentCachedBranchMembers9349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9349
  · have he : independentCachedBranchMembers9351.filter (independentCachedEdge 2770)=independentCachedBranchMembers9350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9350
def independentCachedBranchMembers9352 : Finset ℕ := ([144,160,246,250,1690,1702,1706,1716,1720,1740,1746,1762,1776,2716,2732,2738,2758,2762,2772,2776,2788,2792,3222,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9352 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9352 5 (fun x => (if x<2738 then (if x<1716 then (if x<250 then (if x<160 then 0 else (if x<246 then 1 else 0)) else (if x<1702 then (if x<1690 then 1 else 2) else (if x<1706 then 2 else 1))) else (if x<1762 then (if x<1740 then (if x<1720 then 0 else 3) else (if x<1746 then 2 else 0)) else (if x<2716 then (if x<1776 then 3 else 1) else (if x<2732 then 3 else 4)))) else (if x<3222 then (if x<2772 then (if x<2758 then 0 else (if x<2762 then 3 else 4)) else (if x<2788 then (if x<2776 then 0 else 2) else (if x<2792 then 2 else 1))) else (if x<3276 then (if x<3252 then (if x<3242 then 0 else 4) else (if x<3256 then 4 else 1)) else (if x<3298 then (if x<3282 then 4 else 4) else (if x<3312 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9353 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9353 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9353 2764 5
  · have he : independentCachedBranchMembers9353.erase 2764=independentCachedBranchMembers9351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9351
  · have he : independentCachedBranchMembers9353.filter (independentCachedEdge 2764)=independentCachedBranchMembers9352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9352
def independentCachedBranchMembers9354 : Finset ℕ := ([136,192,238,250,1690,1706,1716,1734,1740,1746,1752,1762,1768,2716,2726,2732,2738,2744,2762,2772,2788,2800,3214,3242,3252,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9354 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9354 5 (fun x => (if x<2732 then (if x<1734 then (if x<250 then (if x<192 then 0 else (if x<238 then 1 else 0)) else (if x<1706 then (if x<1690 then 1 else 2) else (if x<1716 then 0 else 2))) else (if x<1762 then (if x<1746 then (if x<1740 then 2 else 0) else (if x<1752 then 1 else 3)) else (if x<2716 then (if x<1768 then 3 else 1) else (if x<2726 then 3 else 3)))) else (if x<3214 then (if x<2762 then (if x<2738 then 0 else (if x<2744 then 4 else 2)) else (if x<2788 then (if x<2772 then 0 else 4) else (if x<2800 then 2 else 1))) else (if x<3282 then (if x<3252 then (if x<3242 then 0 else 4) else (if x<3276 then 4 else 4)) else (if x<3298 then (if x<3288 then 4 else 1) else (if x<3304 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9355 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9355 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9355 2740 5
  · have he : independentCachedBranchMembers9355.erase 2740=independentCachedBranchMembers9353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9353
  · have he : independentCachedBranchMembers9355.filter (independentCachedEdge 2740)=independentCachedBranchMembers9354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9354
def independentCachedBranchMembers9356 : Finset ℕ := ([136,160,238,250,1692,1706,1716,1734,1740,1746,1752,1764,1776,2714,2726,2732,2738,2744,2762,2772,2786,2792,3214,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9356 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9356 5 (fun x => (if x<2732 then (if x<1734 then (if x<250 then (if x<160 then 0 else (if x<238 then 1 else 0)) else (if x<1706 then (if x<1692 then 1 else 2) else (if x<1716 then 0 else 3))) else (if x<1764 then (if x<1746 then (if x<1740 then 2 else 0) else (if x<1752 then 3 else 4)) else (if x<2714 then (if x<1776 then 4 else 1) else (if x<2726 then 4 else 4)))) else (if x<3214 then (if x<2762 then (if x<2738 then 0 else (if x<2744 then 1 else 2)) else (if x<2786 then (if x<2772 then 0 else 2) else (if x<2792 then 2 else 1))) else (if x<3274 then (if x<3250 then (if x<3244 then 0 else 3) else (if x<3256 then 3 else 1)) else (if x<3298 then (if x<3284 then 3 else 3) else (if x<3304 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9357 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1716,1720,1734,1740,1746,1748,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9357 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9357 1748 5
  · have he : independentCachedBranchMembers9357.erase 1748=independentCachedBranchMembers9355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9355
  · have he : independentCachedBranchMembers9357.filter (independentCachedEdge 1748)=independentCachedBranchMembers9356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9356
def independentCachedBranchMembers9358 : Finset ℕ := ([144,160,246,252,1690,1706,1716,1734,1740,1746,1752,1762,1768,2716,2726,2732,2738,2744,2762,2772,2788,2800,3222,3244,3250,3256,3274,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9358 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9358 5 (fun x => (if x<2732 then (if x<1734 then (if x<252 then (if x<160 then 0 else (if x<246 then 1 else 0)) else (if x<1706 then (if x<1690 then 1 else 2) else (if x<1716 then 3 else 0))) else (if x<1762 then (if x<1746 then (if x<1740 then 2 else 3) else (if x<1752 then 0 else 4)) else (if x<2716 then (if x<1768 then 4 else 1) else (if x<2726 then 4 else 4)))) else (if x<3222 then (if x<2762 then (if x<2738 then 1 else (if x<2744 then 0 else 2)) else (if x<2788 then (if x<2772 then 2 else 0) else (if x<2800 then 2 else 1))) else (if x<3274 then (if x<3250 then (if x<3244 then 0 else 3) else (if x<3256 then 3 else 1)) else (if x<3300 then (if x<3284 then 3 else 3) else (if x<3312 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9359 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9359 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9359 1738 5
  · have he : independentCachedBranchMembers9359.erase 1738=independentCachedBranchMembers9357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9357
  · have he : independentCachedBranchMembers9359.filter (independentCachedEdge 1738)=independentCachedBranchMembers9358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9358
def independentCachedBranchMembers9360 : Finset ℕ := ([144,192,246,250,1692,1702,1706,1716,1720,1740,1746,1764,1768,2714,2732,2738,2758,2762,2772,2776,2786,2800,3222,3244,3250,3274,3284,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9360 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9360 5 (fun x => (if x<2738 then (if x<1716 then (if x<250 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<1702 then (if x<1692 then 1 else 2) else (if x<1706 then 2 else 3))) else (if x<1764 then (if x<1740 then (if x<1720 then 0 else 4) else (if x<1746 then 3 else 0)) else (if x<2714 then (if x<1768 then 4 else 1) else (if x<2732 then 4 else 2)))) else (if x<3222 then (if x<2772 then (if x<2758 then 0 else (if x<2762 then 4 else 1)) else (if x<2786 then (if x<2776 then 0 else 2) else (if x<2800 then 2 else 1))) else (if x<3284 then (if x<3250 then (if x<3244 then 0 else 3) else (if x<3274 then 3 else 3)) else (if x<3298 then (if x<3288 then 3 else 1) else (if x<3312 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9361 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9361 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9361 1708 5
  · have he : independentCachedBranchMembers9361.erase 1708=independentCachedBranchMembers9359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9359
  · have he : independentCachedBranchMembers9361.filter (independentCachedEdge 1708)=independentCachedBranchMembers9360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9360
def independentCachedBranchMembers9362 : Finset ℕ := ([136,144,250,252,1690,1692,1706,1716,1734,1752,1768,1776,2714,2716,2732,2738,2740,2758,2776,2792,2800,3214,3222,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9362 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9362 5 (fun x => (if x<2738 then (if x<1716 then (if x<252 then (if x<144 then 0 else (if x<250 then 1 else 0)) else (if x<1692 then (if x<1690 then 1 else 0) else (if x<1706 then 1 else 2))) else (if x<1776 then (if x<1752 then (if x<1734 then 2 else 2) else (if x<1768 then 2 else 0)) else (if x<2716 then (if x<2714 then 1 else 3) else (if x<2732 then 4 else 3)))) else (if x<3222 then (if x<2776 then (if x<2740 then 4 else (if x<2758 then 1 else 3)) else (if x<2800 then (if x<2792 then 0 else 4) else (if x<3214 then 3 else 3))) else (if x<3282 then (if x<3274 then (if x<3256 then 4 else 0) else (if x<3276 then 0 else 4)) else (if x<3298 then (if x<3284 then 3 else 1) else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9363 : Finset ℕ := ([250,1692,1706,1716,1768,2714,2732,2738,2758,2776,2800,3222,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9363 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9363 4 (fun x => (if x<2738 then (if x<1716 then (if x<1692 then 0 else (if x<1706 then 1 else 0)) else (if x<2714 then (if x<1768 then 2 else 1) else (if x<2732 then 0 else 1))) else (if x<3222 then (if x<2776 then (if x<2758 then 2 else 3) else (if x<2800 then 1 else 3)) else (if x<3284 then (if x<3274 then 2 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9364 : Finset ℕ := ([1706,1768,2732,2758,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9364 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9364 3 (fun x => (if x<2758 then (if x<1768 then 0 else (if x<2732 then 1 else 0)) else (if x<3274 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9365 : Finset ℕ := ([144,250,1692,1706,1716,1768,2714,2732,2738,2758,2776,2800,3222,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9365 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9365 144 3
  · have he : independentCachedBranchMembers9365.erase 144=independentCachedBranchMembers9363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9363
  · have he : independentCachedBranchMembers9365.filter (independentCachedEdge 144)=independentCachedBranchMembers9364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9364
def independentCachedBranchMembers9366 : Finset ℕ := ([136,144,250,252,1690,1692,1706,1708,1716,1734,1752,1768,1776,2714,2716,2732,2738,2740,2758,2776,2792,2800,3214,3222,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9366 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9366 1708 4
  · have he : independentCachedBranchMembers9366.erase 1708=independentCachedBranchMembers9362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9362
  · have he : independentCachedBranchMembers9366.filter (independentCachedEdge 1708)=independentCachedBranchMembers9365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9365
def independentCachedBranchMembers9367 : Finset ℕ := ([136,144,1690,1692,1734,1752,2714,2716,2758,2776,3214,3222,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9367 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9367 4 (fun x => (if x<2758 then (if x<1734 then (if x<1690 then (if x<144 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<2714 then (if x<1752 then 2 else 2) else (if x<2716 then 1 else 0))) else (if x<3274 then (if x<3214 then (if x<2776 then 3 else 3) else (if x<3222 then 0 else 1)) else (if x<3282 then (if x<3276 then 2 else 3) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9368 : Finset ℕ := ([136,144,160,250,252,1690,1692,1706,1708,1716,1734,1752,1768,1776,2714,2716,2732,2738,2740,2758,2776,2792,2800,3214,3222,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9368 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9368 160 4
  · have he : independentCachedBranchMembers9368.erase 160=independentCachedBranchMembers9366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9366
  · have he : independentCachedBranchMembers9368.filter (independentCachedEdge 160)=independentCachedBranchMembers9367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9367
def independentCachedBranchMembers9369 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9369 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9369 3270 5
  · have he : independentCachedBranchMembers9369.erase 3270=independentCachedBranchMembers9361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9361
  · have he : independentCachedBranchMembers9369.filter (independentCachedEdge 3270)=independentCachedBranchMembers9368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9368
def independentCachedBranchMembers9370 : Finset ℕ := ([160,192,238,246,1692,1702,1706,1734,1746,1764,1768,1776,2716,2726,2738,2758,2762,2770,2788,2792,2800,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9370 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9370 5 (fun x => (if x<2758 then (if x<1734 then (if x<246 then (if x<192 then 0 else (if x<238 then 1 else 0)) else (if x<1702 then (if x<1692 then 1 else 2) else (if x<1706 then 0 else 2))) else (if x<1776 then (if x<1764 then (if x<1746 then 1 else 2) else (if x<1768 then 2 else 0)) else (if x<2726 then (if x<2716 then 1 else 3) else (if x<2738 then 3 else 4)))) else (if x<3222 then (if x<2788 then (if x<2762 then 4 else (if x<2770 then 3 else 1)) else (if x<2800 then (if x<2792 then 0 else 4) else (if x<3214 then 3 else 3))) else (if x<3276 then (if x<3252 then (if x<3244 then 4 else 0) else (if x<3256 then 3 else 4)) else (if x<3288 then (if x<3284 then 4 else 1) else (if x<3298 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9371 : Finset ℕ := ([246,1706,1734,1746,1768,2716,2726,2738,2762,2788,2800,3222,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9371 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9371 4 (fun x => (if x<2738 then (if x<1746 then (if x<1706 then 0 else (if x<1734 then 1 else 0)) else (if x<2716 then (if x<1768 then 1 else 2) else (if x<2726 then 3 else 0))) else (if x<3222 then (if x<2788 then (if x<2762 then 1 else 1) else (if x<2800 then 2 else 3)) else (if x<3256 then (if x<3244 then 0 else 2) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9372 : Finset ℕ := ([1734,1746,2716,2762,3222,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9372 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9372 3 (fun x => (if x<2762 then (if x<1746 then 0 else (if x<2716 then 1 else 2)) else (if x<3222 then 0 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9373 : Finset ℕ := ([160,246,1706,1734,1746,1768,2716,2726,2738,2762,2788,2800,3222,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9373 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9373 160 3
  · have he : independentCachedBranchMembers9373.erase 160=independentCachedBranchMembers9371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9371
  · have he : independentCachedBranchMembers9373.filter (independentCachedEdge 160)=independentCachedBranchMembers9372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9372
def independentCachedBranchMembers9374 : Finset ℕ := ([160,192,238,246,1692,1702,1706,1734,1738,1746,1764,1768,1776,2716,2726,2738,2758,2762,2770,2788,2792,2800,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9374 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9374 1738 4
  · have he : independentCachedBranchMembers9374.erase 1738=independentCachedBranchMembers9370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9370
  · have he : independentCachedBranchMembers9374.filter (independentCachedEdge 1738)=independentCachedBranchMembers9373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9373
def independentCachedBranchMembers9375 : Finset ℕ := ([238,246,1692,1702,1734,1764,2716,2726,2758,2788,3214,3222,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9375 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9375 4 (fun x => (if x<2758 then (if x<1734 then (if x<1692 then (if x<246 then 0 else 1) else (if x<1702 then 2 else 0)) else (if x<2716 then (if x<1764 then 1 else 2) else (if x<2726 then 3 else 1))) else (if x<3244 then (if x<3214 then (if x<2788 then 0 else 3) else (if x<3222 then 0 else 1)) else (if x<3276 then (if x<3252 then 2 else 3) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
