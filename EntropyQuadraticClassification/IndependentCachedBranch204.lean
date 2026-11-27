/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch203
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9312 : Finset ℕ := ([144,250,1692,1706,1720,1746,1752,1764,2714,2726,2732,2758,2772,2786,2792,2800,3222,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9312 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9312 5 (fun x => (if x<2772 then (if x<1752 then (if x<1706 then (if x<250 then 0 else (if x<1692 then 0 else 1)) else (if x<1720 then 1 else (if x<1746 then 0 else 0))) else (if x<2726 then (if x<1764 then 2 else (if x<2714 then 1 else 0)) else (if x<2732 then 2 else (if x<2758 then 1 else 3)))) else (if x<3250 then (if x<2800 then (if x<2786 then 1 else (if x<2792 then 1 else 2)) else (if x<3222 then 0 else (if x<3242 then 3 else 4))) else (if x<3282 then (if x<3256 then 0 else (if x<3274 then 3 else 3)) else (if x<3288 then 4 else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9313 : Finset ℕ := ([144,160,192,246,250,252,1692,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2786,2788,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9313 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9313 2788 5
  · have he : independentCachedBranchMembers9313.erase 2788=independentCachedBranchMembers9311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9311
  · have he : independentCachedBranchMembers9313.filter (independentCachedEdge 2788)=independentCachedBranchMembers9312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9312
def independentCachedBranchMembers9314 : Finset ℕ := ([160,246,1706,1716,1734,1752,1762,1764,2714,2716,2726,2744,2762,2772,2792,2800,3222,3242,3244,3250,3252,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9314 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9314 5 (fun x => (if x<2762 then (if x<1762 then (if x<1716 then (if x<246 then 0 else (if x<1706 then 0 else 1)) else (if x<1734 then 0 else (if x<1752 then 1 else 1))) else (if x<2716 then (if x<1764 then 0 else (if x<2714 then 2 else 2)) else (if x<2726 then 3 else (if x<2744 then 0 else 1)))) else (if x<3244 then (if x<2800 then (if x<2772 then 1 else (if x<2792 then 1 else 2)) else (if x<3222 then 0 else (if x<3242 then 3 else 4))) else (if x<3288 then (if x<3250 then 3 else (if x<3252 then 0 else 4)) else (if x<3298 then 3 else (if x<3300 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9315 : Finset ℕ := ([144,160,192,246,250,252,1692,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9315 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9315 2776 5
  · have he : independentCachedBranchMembers9315.erase 2776=independentCachedBranchMembers9313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9313
  · have he : independentCachedBranchMembers9315.filter (independentCachedEdge 2776)=independentCachedBranchMembers9314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9314
def independentCachedBranchMembers9316 : Finset ℕ := ([144,192,250,252,1706,1716,1734,1752,1762,1764,2714,2716,2726,2744,2762,2772,2792,2800,3256,3274,3276,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9316 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9316 5 (fun x => (if x<2726 then (if x<1734 then (if x<252 then (if x<192 then 0 else (if x<250 then 1 else 0)) else (if x<1706 then 1 else (if x<1716 then 2 else 2))) else (if x<1764 then (if x<1752 then 2 else (if x<1762 then 0 else 3)) else (if x<2714 then 1 else (if x<2716 then 0 else 3)))) else (if x<3256 then (if x<2772 then (if x<2744 then 2 else (if x<2762 then 2 else 2)) else (if x<2792 then 1 else (if x<2800 then 1 else 0))) else (if x<3282 then (if x<3274 then 0 else (if x<3276 then 4 else 1)) else (if x<3284 then 0 else (if x<3312 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9317 : Finset ℕ := ([144,160,192,246,250,252,1692,1702,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9317 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9317 1702 5
  · have he : independentCachedBranchMembers9317.erase 1702=independentCachedBranchMembers9315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9315
  · have he : independentCachedBranchMembers9317.filter (independentCachedEdge 1702)=independentCachedBranchMembers9316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9316
def independentCachedBranchMembers9318 : Finset ℕ := ([160,192,246,252,1692,1706,1720,1746,1752,1764,2714,2726,2732,2758,2772,2786,2792,2800,3244,3252,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9318 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9318 5 (fun x => (if x<2732 then (if x<1720 then (if x<252 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<1692 then 1 else (if x<1706 then 2 else 2))) else (if x<1764 then (if x<1746 then 3 else (if x<1752 then 2 else 1)) else (if x<2714 then 0 else (if x<2726 then 2 else 0)))) else (if x<3244 then (if x<2786 then (if x<2758 then 2 else (if x<2772 then 3 else 1)) else (if x<2792 then 2 else (if x<2800 then 1 else 0))) else (if x<3284 then (if x<3252 then 4 else (if x<3276 then 0 else 1)) else (if x<3298 then 4 else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9319 : Finset ℕ := ([144,160,192,246,250,252,1690,1692,1702,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9319 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9319 1690 5
  · have he : independentCachedBranchMembers9319.erase 1690=independentCachedBranchMembers9317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9317
  · have he : independentCachedBranchMembers9319.filter (independentCachedEdge 1690)=independentCachedBranchMembers9318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9318
def independentCachedBranchMembers9320 : Finset ℕ := ([246,1690,1692,1702,1716,1734,1746,1768,2714,2716,2726,2738,2758,2772,2792,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9320 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9320 5 (fun x => (if x<2758 then (if x<1746 then (if x<1702 then (if x<1690 then 0 else (if x<1692 then 1 else 2)) else (if x<1716 then 0 else (if x<1734 then 1 else 1))) else (if x<2716 then (if x<1768 then 0 else (if x<2714 then 1 else 2)) else (if x<2726 then 3 else (if x<2738 then 3 else 0)))) else (if x<3256 then (if x<3222 then (if x<2772 then 0 else (if x<2792 then 2 else 3)) else (if x<3242 then 0 else (if x<3244 then 4 else 3))) else (if x<3288 then (if x<3274 then 1 else (if x<3276 then 1 else 4)) else (if x<3300 then (if x<3298 then 2 else 0) else (if x<3312 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9321 : Finset ℕ := ([1734,1768,2726,2758,2792,3242,3244,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9321 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9321 4 (fun x => (if x<3242 then (if x<2726 then (if x<1768 then 0 else 0) else (if x<2758 then 1 else (if x<2792 then 2 else 1))) else (if x<3276 then (if x<3244 then 1 else (if x<3274 then 3 else 0)) else (if x<3298 then 2 else (if x<3300 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9322 : Finset ℕ := ([1734,2726,2792,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9322 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9322 3 (fun x => (if x<2792 then (if x<2726 then 0 else 0) else (if x<3274 then 1 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9323 : Finset ℕ := ([1702,1734,1768,2726,2758,2792,3242,3244,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9323 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9323 1702 3
  · have he : independentCachedBranchMembers9323.erase 1702=independentCachedBranchMembers9321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9321
  · have he : independentCachedBranchMembers9323.filter (independentCachedEdge 1702)=independentCachedBranchMembers9322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9322
def independentCachedBranchMembers9324 : Finset ℕ := ([144,246,1690,1692,1702,1716,1734,1746,1768,2714,2716,2726,2738,2758,2772,2792,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9324 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9324 144 4
  · have he : independentCachedBranchMembers9324.erase 144=independentCachedBranchMembers9320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9320
  · have he : independentCachedBranchMembers9324.filter (independentCachedEdge 144)=independentCachedBranchMembers9323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9323
def independentCachedBranchMembers9325 : Finset ℕ := ([144,160,192,246,250,252,1690,1692,1702,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9325 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9325 3304 5
  · have he : independentCachedBranchMembers9325.erase 3304=independentCachedBranchMembers9319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9319
  · have he : independentCachedBranchMembers9325.filter (independentCachedEdge 3304)=independentCachedBranchMembers9324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9324
def independentCachedBranchMembers9326 : Finset ℕ := ([160,192,246,250,252,1716,1720,1746,1752,1762,1764,1768,2738,2744,2772,2776,2786,2788,2792,3222,3242,3244,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9326 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9326 5 (fun x => (if x<2738 then (if x<1720 then (if x<250 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<252 then 1 else (if x<1716 then 2 else 0))) else (if x<1762 then (if x<1746 then 2 else (if x<1752 then 1 else 3)) else (if x<1764 then 0 else (if x<1768 then 2 else 1)))) else (if x<2792 then (if x<2776 then (if x<2744 then 0 else (if x<2772 then 3 else 3)) else (if x<2786 then 1 else (if x<2788 then 1 else 0))) else (if x<3244 then (if x<3222 then 2 else (if x<3242 then 4 else 4)) else (if x<3276 then (if x<3274 then 2 else 1) else (if x<3312 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9327 : Finset ℕ := ([160,192,1762,1764,1768,2786,2788,2792,3242,3244,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9327 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9327 4 (fun x => (if x<2788 then (if x<1764 then (if x<192 then 0 else (if x<1762 then 1 else 0)) else (if x<1768 then 1 else (if x<2786 then 2 else 1))) else (if x<3244 then (if x<2792 then 0 else (if x<3242 then 3 else 2)) else (if x<3274 then 3 else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9328 : Finset ℕ := ([144,160,192,246,250,252,1716,1720,1746,1752,1762,1764,1768,2738,2744,2772,2776,2786,2788,2792,3222,3242,3244,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9328 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9328 144 4
  · have he : independentCachedBranchMembers9328.erase 144=independentCachedBranchMembers9326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9326
  · have he : independentCachedBranchMembers9328.filter (independentCachedEdge 144)=independentCachedBranchMembers9327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9327
def independentCachedBranchMembers9329 : Finset ℕ := ([144,160,192,246,250,252,1690,1692,1702,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9329 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9329 3214 5
  · have he : independentCachedBranchMembers9329.erase 3214=independentCachedBranchMembers9325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9325
  · have he : independentCachedBranchMembers9329.filter (independentCachedEdge 3214)=independentCachedBranchMembers9328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9328
def independentCachedBranchMembers9330 : Finset ℕ := ([144,250,252,1690,1692,1716,1720,1746,1752,1776,2714,2716,2738,2744,2772,2776,2800,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9330 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9330 5 (fun x => (if x<2716 then (if x<1716 then (if x<252 then (if x<250 then 0 else 0) else (if x<1690 then 1 else (if x<1692 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1746 then 3 else 2)) else (if x<1776 then 4 else (if x<2714 then 0 else 3)))) else (if x<3250 then (if x<2772 then (if x<2738 then 4 else (if x<2744 then 0 else 1)) else (if x<2776 then 1 else (if x<2800 then 0 else 2))) else (if x<3282 then (if x<3252 then 2 else (if x<3256 then 1 else 0)) else (if x<3284 then 0 else (if x<3288 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9331 : Finset ℕ := ([1692,1776,2714,2716,2800,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9331 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9331 4 (fun x => (if x<3250 then (if x<2714 then (if x<1776 then 0 else 0) else (if x<2716 then 1 else (if x<2800 then 2 else 1))) else (if x<3282 then (if x<3252 then 1 else (if x<3256 then 0 else 2)) else (if x<3284 then 3 else (if x<3288 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9332 : Finset ℕ := ([1692,2714,2800,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9332 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9332 3 (fun x => (if x<2800 then (if x<2714 then 0 else 0) else (if x<3252 then 1 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9333 : Finset ℕ := ([1690,1692,1776,2714,2716,2800,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9333 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9333 1690 3
  · have he : independentCachedBranchMembers9333.erase 1690=independentCachedBranchMembers9331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9331
  · have he : independentCachedBranchMembers9333.filter (independentCachedEdge 1690)=independentCachedBranchMembers9332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9332
def independentCachedBranchMembers9334 : Finset ℕ := ([144,250,252,1690,1692,1716,1720,1746,1752,1776,2714,2716,2738,2744,2772,2776,2800,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9334 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9334 3312 4
  · have he : independentCachedBranchMembers9334.erase 3312=independentCachedBranchMembers9330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9330
  · have he : independentCachedBranchMembers9334.filter (independentCachedEdge 3312)=independentCachedBranchMembers9333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9333
def independentCachedBranchMembers9335 : Finset ℕ := ([250,252,1720,1752,1776,2744,2776,2800,3250,3252,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9335 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9335 4 (fun x => (if x<2776 then (if x<1752 then (if x<252 then 0 else (if x<1720 then 1 else 0)) else (if x<1776 then 1 else (if x<2744 then 2 else 1))) else (if x<3252 then (if x<2800 then 0 else (if x<3250 then 3 else 2)) else (if x<3282 then 3 else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9336 : Finset ℕ := ([144,250,252,1690,1692,1716,1720,1746,1752,1776,2714,2716,2738,2744,2772,2776,2800,3222,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9336 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9336 3222 4
  · have he : independentCachedBranchMembers9336.erase 3222=independentCachedBranchMembers9334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9334
  · have he : independentCachedBranchMembers9336.filter (independentCachedEdge 3222)=independentCachedBranchMembers9335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9335
def independentCachedBranchMembers9337 : Finset ℕ := ([250,252,1690,1692,1720,1752,2714,2716,2744,2776,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9337 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9337 4 (fun x => (if x<2714 then (if x<1692 then (if x<252 then 0 else (if x<1690 then 1 else 0)) else (if x<1720 then 1 else (if x<1752 then 2 else 3))) else (if x<2776 then (if x<2716 then 2 else (if x<2744 then 3 else 0)) else (if x<3256 then 1 else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9338 : Finset ℕ := ([144,246,250,252,1690,1692,1716,1720,1746,1752,1776,2714,2716,2738,2744,2772,2776,2800,3222,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9338 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9338 246 4
  · have he : independentCachedBranchMembers9338.erase 246=independentCachedBranchMembers9336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9336
  · have he : independentCachedBranchMembers9338.filter (independentCachedEdge 246)=independentCachedBranchMembers9337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9337
def independentCachedBranchMembers9339 : Finset ℕ := ([144,160,192,238,246,250,252,1690,1692,1702,1706,1716,1720,1734,1740,1746,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3214,3222,3242,3244,3250,3252,3256,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9339 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9339 238 5
  · have he : independentCachedBranchMembers9339.erase 238=independentCachedBranchMembers9329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9329
  · have he : independentCachedBranchMembers9339.filter (independentCachedEdge 238)=independentCachedBranchMembers9338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9338
def independentCachedBranchMembers9340 : Finset ℕ := ([160,192,246,1702,1716,1734,1746,1762,1764,1776,2726,2738,2758,2772,2786,2788,2800,3250,3252,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9340 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9340 5 (fun x => (if x<2738 then (if x<1734 then (if x<246 then (if x<192 then 0 else 1) else (if x<1702 then 0 else (if x<1716 then 0 else 2))) else (if x<1764 then (if x<1746 then 1 else (if x<1762 then 2 else 3)) else (if x<1776 then 4 else (if x<2726 then 0 else 3)))) else (if x<3250 then (if x<2786 then (if x<2758 then 0 else (if x<2772 then 4 else 1)) else (if x<2788 then 1 else (if x<2800 then 0 else 2))) else (if x<3284 then (if x<3252 then 2 else (if x<3282 then 0 else 1)) else (if x<3298 then 2 else (if x<3300 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9341 : Finset ℕ := ([1734,1776,2726,2758,2800,3250,3252,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9341 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9341 4 (fun x => (if x<3250 then (if x<2726 then (if x<1776 then 0 else 0) else (if x<2758 then 1 else (if x<2800 then 2 else 1))) else (if x<3284 then (if x<3252 then 1 else (if x<3282 then 3 else 0)) else (if x<3298 then 2 else (if x<3300 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9342 : Finset ℕ := ([1734,2726,2800,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9342 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9342 3 (fun x => (if x<2800 then (if x<2726 then 0 else 0) else (if x<3282 then 1 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9343 : Finset ℕ := ([1702,1734,1776,2726,2758,2800,3250,3252,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9343 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9343 1702 3
  · have he : independentCachedBranchMembers9343.erase 1702=independentCachedBranchMembers9341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9341
  · have he : independentCachedBranchMembers9343.filter (independentCachedEdge 1702)=independentCachedBranchMembers9342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9342
end EntropyDesigns.QuadraticRefinement
