/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch205
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9376 : Finset ℕ := ([160,192,238,246,250,1692,1702,1706,1734,1738,1746,1764,1768,1776,2716,2726,2738,2758,2762,2770,2788,2792,2800,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9376 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9376 250 4
  · have he : independentCachedBranchMembers9376.erase 250=independentCachedBranchMembers9374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9374
  · have he : independentCachedBranchMembers9376.filter (independentCachedEdge 250)=independentCachedBranchMembers9375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9375
def independentCachedBranchMembers9377 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3228,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9377 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9377 3228 5
  · have he : independentCachedBranchMembers9377.erase 3228=independentCachedBranchMembers9369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9369
  · have he : independentCachedBranchMembers9377.filter (independentCachedEdge 3228)=independentCachedBranchMembers9376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9376
def independentCachedBranchMembers9378 : Finset ℕ := ([160,192,246,250,252,1716,1720,1746,1752,1762,1764,2714,2716,2726,2732,2758,2762,2800,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9378 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9378 5 (fun x => (if x<2732 then (if x<1746 then (if x<250 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<1716 then (if x<252 then 1 else 2) else (if x<1720 then 0 else 2))) else (if x<1764 then (if x<1752 then 1 else (if x<1762 then 3 else 0)) else (if x<2716 then (if x<2714 then 2 else 3) else (if x<2726 then 4 else 0)))) else (if x<3256 then (if x<2800 then (if x<2758 then 2 else (if x<2762 then 4 else 1)) else (if x<3250 then (if x<3214 then 0 else 4) else (if x<3252 then 0 else 2))) else (if x<3288 then (if x<3282 then 3 else (if x<3284 then 3 else 4)) else (if x<3300 then (if x<3298 then 1 else 1) else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9379 : Finset ℕ := ([160,192,1762,1764,2726,2732,2758,2762,3214,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9379 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9379 4 (fun x => (if x<2758 then (if x<1764 then (if x<192 then 0 else (if x<1762 then 1 else 0)) else (if x<2726 then 1 else (if x<2732 then 0 else 2))) else (if x<3298 then (if x<2762 then 1 else (if x<3214 then 2 else 2)) else (if x<3300 then 1 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9380 : Finset ℕ := ([144,160,192,246,250,252,1716,1720,1746,1752,1762,1764,2714,2716,2726,2732,2758,2762,2800,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9380 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9380 144 4
  · have he : independentCachedBranchMembers9380.erase 144=independentCachedBranchMembers9378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9378
  · have he : independentCachedBranchMembers9380.filter (independentCachedEdge 144)=independentCachedBranchMembers9379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9379
def independentCachedBranchMembers9381 : Finset ℕ := ([144,160,246,250,1716,1720,1746,1762,2716,2732,2758,2762,3252,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9381 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9381 4 (fun x => (if x<2716 then (if x<1716 then (if x<246 then (if x<160 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1746 then (if x<1720 then 0 else 1) else (if x<1762 then 0 else 1))) else (if x<3252 then (if x<2758 then (if x<2732 then 2 else 3) else (if x<2762 then 2 else 3)) else (if x<3282 then (if x<3256 then 3 else 2) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9382 : Finset ℕ := ([144,160,192,246,250,252,1716,1720,1746,1752,1762,1764,2714,2716,2726,2732,2758,2762,2764,2800,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9382 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9382 2764 4
  · have he : independentCachedBranchMembers9382.erase 2764=independentCachedBranchMembers9380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9380
  · have he : independentCachedBranchMembers9382.filter (independentCachedEdge 2764)=independentCachedBranchMembers9381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9381
def independentCachedBranchMembers9383 : Finset ℕ := ([144,246,1720,1752,1762,1764,2714,2716,2726,2758,3214,3250,3252,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9383 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9383 4 (fun x => (if x<2726 then (if x<1762 then (if x<1720 then (if x<246 then 0 else 0) else (if x<1752 then 1 else 2)) else (if x<2714 then (if x<1764 then 1 else 2) else (if x<2716 then 2 else 1))) else (if x<3252 then (if x<3214 then (if x<2758 then 2 else 1) else (if x<3250 then 3 else 0)) else (if x<3284 then (if x<3282 then 3 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9384 : Finset ℕ := ([144,160,192,246,250,252,1716,1720,1746,1752,1762,1764,1768,2714,2716,2726,2732,2758,2762,2764,2800,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9384 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9384 1768 4
  · have he : independentCachedBranchMembers9384.erase 1768=independentCachedBranchMembers9382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9382
  · have he : independentCachedBranchMembers9384.filter (independentCachedEdge 1768)=independentCachedBranchMembers9383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9383
def independentCachedBranchMembers9385 : Finset ℕ := ([160,250,1716,1746,1752,1764,2714,2726,2732,2762,3214,3250,3256,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9385 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9385 4 (fun x => (if x<2732 then (if x<1752 then (if x<1716 then (if x<250 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2714 then (if x<1764 then 2 else 2) else (if x<2726 then 2 else 2))) else (if x<3256 then (if x<3214 then (if x<2762 then 1 else 1) else (if x<3250 then 3 else 0)) else (if x<3298 then (if x<3284 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9386 : Finset ℕ := ([144,160,192,246,250,252,1716,1720,1746,1748,1752,1762,1764,1768,2714,2716,2726,2732,2758,2762,2764,2800,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9386 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9386 1748 4
  · have he : independentCachedBranchMembers9386.erase 1748=independentCachedBranchMembers9384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9384
  · have he : independentCachedBranchMembers9386.filter (independentCachedEdge 1748)=independentCachedBranchMembers9385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9385
def independentCachedBranchMembers9387 : Finset ℕ := ([136,144,160,192,238,246,250,252,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3228,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9387 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9387 2702 5
  · have he : independentCachedBranchMembers9387.erase 2702=independentCachedBranchMembers9377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9377
  · have he : independentCachedBranchMembers9387.filter (independentCachedEdge 2702)=independentCachedBranchMembers9386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9386
def independentCachedBranchMembers9388 : Finset ℕ := ([160,192,250,252,1690,1692,1702,1716,1734,1746,1768,2744,2776,2786,2788,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9388 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9388 5 (fun x => (if x<2776 then (if x<1702 then (if x<252 then (if x<192 then 0 else (if x<250 then 1 else 0)) else (if x<1690 then 1 else (if x<1692 then 2 else 3))) else (if x<1746 then (if x<1716 then 2 else (if x<1734 then 4 else 3)) else (if x<1768 then 4 else (if x<2744 then 0 else 0)))) else (if x<3256 then (if x<3222 then (if x<2786 then 1 else (if x<2788 then 0 else 1)) else (if x<3242 then 2 else (if x<3244 then 0 else 4))) else (if x<3288 then (if x<3274 then 3 else (if x<3276 then 4 else 1)) else (if x<3300 then (if x<3298 then 2 else 3) else (if x<3312 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9389 : Finset ℕ := ([160,252,1692,1702,2776,2786,3222,3244,3256,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9389 4 (fun x => (if x<3222 then (if x<1702 then (if x<252 then 0 else (if x<1692 then 0 else 1)) else (if x<2776 then 1 else (if x<2786 then 1 else 1))) else (if x<3274 then (if x<3244 then 2 else (if x<3256 then 0 else 2)) else (if x<3300 then 2 else (if x<3312 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9390 : Finset ℕ := ([160,192,250,252,1690,1692,1702,1716,1734,1746,1768,2744,2762,2776,2786,2788,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9390 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9390 2762 4
  · have he : independentCachedBranchMembers9390.erase 2762=independentCachedBranchMembers9388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9388
  · have he : independentCachedBranchMembers9390.filter (independentCachedEdge 2762)=independentCachedBranchMembers9389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9389
def independentCachedBranchMembers9391 : Finset ℕ := ([192,250,1690,1734,2744,2788,3222,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9391 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9391 4 (fun x => (if x<3222 then (if x<1734 then (if x<250 then 0 else (if x<1690 then 0 else 1)) else (if x<2744 then 1 else (if x<2788 then 1 else 1))) else (if x<3288 then (if x<3244 then 2 else (if x<3274 then 2 else 0)) else (if x<3298 then 2 else (if x<3312 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9392 : Finset ℕ := ([160,192,250,252,1690,1692,1702,1716,1734,1746,1768,2732,2744,2762,2776,2786,2788,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9392 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9392 2732 4
  · have he : independentCachedBranchMembers9392.erase 2732=independentCachedBranchMembers9390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9390
  · have he : independentCachedBranchMembers9392.filter (independentCachedEdge 2732)=independentCachedBranchMembers9391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9391
def independentCachedBranchMembers9393 : Finset ℕ := ([250,252,1690,1692,1716,1746,2744,2776,3222,3256,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9393 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9393 4 (fun x => (if x<2744 then (if x<1692 then (if x<252 then 0 else (if x<1690 then 1 else 0)) else (if x<1716 then 1 else (if x<1746 then 2 else 2))) else (if x<3256 then (if x<2776 then 0 else (if x<3222 then 1 else 2)) else (if x<3288 then 1 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9394 : Finset ℕ := ([160,192,238,250,252,1690,1692,1702,1716,1734,1746,1768,2732,2744,2762,2776,2786,2788,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9394 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9394 238 4
  · have he : independentCachedBranchMembers9394.erase 238=independentCachedBranchMembers9392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9392
  · have he : independentCachedBranchMembers9394.filter (independentCachedEdge 238)=independentCachedBranchMembers9393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9393
def independentCachedBranchMembers9395 : Finset ℕ := ([160,192,1702,1716,1734,1746,2786,2788,3222,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9395 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9395 4 (fun x => (if x<2786 then (if x<1716 then (if x<192 then 0 else (if x<1702 then 1 else 0)) else (if x<1734 then 2 else (if x<1746 then 1 else 2))) else (if x<3298 then (if x<2788 then 0 else (if x<3222 then 1 else 2)) else (if x<3300 then 1 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9396 : Finset ℕ := ([136,160,192,238,250,252,1690,1692,1702,1716,1734,1746,1768,2732,2744,2762,2776,2786,2788,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9396 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9396 136 4
  · have he : independentCachedBranchMembers9396.erase 136=independentCachedBranchMembers9394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9394
  · have he : independentCachedBranchMembers9396.filter (independentCachedEdge 136)=independentCachedBranchMembers9395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9395
def independentCachedBranchMembers9397 : Finset ℕ := ([136,238,1690,1692,1702,1734,2744,2776,2786,2788,3222,3242,3244,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9397 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9397 4 (fun x => (if x<2786 then (if x<1702 then (if x<1690 then (if x<238 then 0 else 0) else (if x<1692 then 1 else 2)) else (if x<2744 then (if x<1734 then 1 else 2) else (if x<2776 then 2 else 1))) else (if x<3244 then (if x<3222 then (if x<2788 then 2 else 1) else (if x<3242 then 3 else 0)) else (if x<3276 then (if x<3274 then 3 else 3) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9398 : Finset ℕ := ([136,160,192,238,250,252,1690,1692,1702,1716,1734,1746,1768,2732,2744,2762,2776,2786,2788,2800,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9398 2800 4
  · have he : independentCachedBranchMembers9398.erase 2800=independentCachedBranchMembers9396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9396
  · have he : independentCachedBranchMembers9398.filter (independentCachedEdge 2800)=independentCachedBranchMembers9397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9397
def independentCachedBranchMembers9399 : Finset ℕ := ([160,250,1690,1702,1716,1746,2732,2762,2776,2788,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9399 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9399 4 (fun x => (if x<2776 then (if x<1716 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2732 then (if x<1746 then 2 else 2) else (if x<2762 then 2 else 2))) else (if x<3256 then (if x<3222 then (if x<2788 then 1 else 1) else (if x<3242 then 3 else 0)) else (if x<3298 then (if x<3276 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9400 : Finset ℕ := ([136,160,192,238,250,252,1690,1692,1702,1716,1734,1746,1768,2732,2744,2762,2764,2776,2786,2788,2800,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9400 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9400 2764 4
  · have he : independentCachedBranchMembers9400.erase 2764=independentCachedBranchMembers9398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9398
  · have he : independentCachedBranchMembers9400.filter (independentCachedEdge 2764)=independentCachedBranchMembers9399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9399
def independentCachedBranchMembers9401 : Finset ℕ := ([136,160,238,250,1692,1716,1734,1746,2732,2744,2762,2786,3244,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9401 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9401 4 (fun x => (if x<2732 then (if x<1692 then (if x<238 then (if x<160 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1734 then (if x<1716 then 2 else 3) else (if x<1746 then 2 else 3))) else (if x<3244 then (if x<2762 then (if x<2744 then 0 else 1) else (if x<2786 then 0 else 1)) else (if x<3274 then (if x<3256 then 3 else 2) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9402 : Finset ℕ := ([136,160,192,238,250,252,1690,1692,1702,1716,1734,1746,1748,1768,2732,2744,2762,2764,2776,2786,2788,2800,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9402 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9402 1748 4
  · have he : independentCachedBranchMembers9402.erase 1748=independentCachedBranchMembers9400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9400
  · have he : independentCachedBranchMembers9402.filter (independentCachedEdge 1748)=independentCachedBranchMembers9401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9401
def independentCachedBranchMembers9403 : Finset ℕ := ([136,144,160,192,238,246,250,252,1686,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3228,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9403 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9403 1686 5
  · have he : independentCachedBranchMembers9403.erase 1686=independentCachedBranchMembers9387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9387
  · have he : independentCachedBranchMembers9403.filter (independentCachedEdge 1686)=independentCachedBranchMembers9402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9402
def independentCachedBranchMembers9404 : Finset ℕ := ([160,238,246,250,252,1702,1706,1716,1720,1762,1764,1768,1776,2726,2732,2738,2740,2744,2786,2788,2792,2800,3242,3244,3250,3252,3256,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9404 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9404 5 (fun x => (if x<2738 then (if x<1716 then (if x<250 then (if x<238 then 0 else (if x<246 then 0 else 1)) else (if x<1702 then (if x<252 then 2 else 3) else (if x<1706 then 0 else 2))) else (if x<1768 then (if x<1762 then (if x<1720 then 1 else 3) else (if x<1764 then 1 else 3)) else (if x<2726 then (if x<1776 then 0 else 2) else (if x<2732 then 1 else 0)))) else (if x<3244 then (if x<2788 then (if x<2744 then (if x<2740 then 2 else 3) else (if x<2786 then 4 else 0)) else (if x<2800 then (if x<2792 then 4 else 2) else (if x<3242 then 1 else 0))) else (if x<3298 then (if x<3252 then (if x<3250 then 3 else 1) else (if x<3256 then 4 else 2)) else (if x<3304 then (if x<3300 then 2 else 0) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9405 : Finset ℕ := ([246,250,1702,1706,1716,1720,1764,1768,2732,2738,2786,2800,3244,3250,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9405 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9405 4 (fun x => (if x<2732 then (if x<1716 then (if x<1702 then (if x<250 then 0 else 1) else (if x<1706 then 0 else 1)) else (if x<1764 then (if x<1720 then 2 else 3) else (if x<1768 then 3 else 2))) else (if x<3244 then (if x<2786 then (if x<2738 then 2 else 0) else (if x<2800 then 1 else 2)) else (if x<3298 then (if x<3250 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9406 : Finset ℕ := ([160,238,246,250,252,1702,1706,1708,1716,1720,1762,1764,1768,1776,2726,2732,2738,2740,2744,2786,2788,2792,2800,3242,3244,3250,3252,3256,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9406 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9406 1708 4
  · have he : independentCachedBranchMembers9406.erase 1708=independentCachedBranchMembers9404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9404
  · have he : independentCachedBranchMembers9406.filter (independentCachedEdge 1708)=independentCachedBranchMembers9405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9405
def independentCachedBranchMembers9407 : Finset ℕ := ([136,144,160,192,222,238,246,250,252,1686,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3228,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9407 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9407 222 5
  · have he : independentCachedBranchMembers9407.erase 222=independentCachedBranchMembers9403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9403
  · have he : independentCachedBranchMembers9407.filter (independentCachedEdge 222)=independentCachedBranchMembers9406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9406
end EntropyDesigns.QuadraticRefinement
