/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch206
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9408 : Finset ℕ := ([136,144,160,192,250,1690,1706,1720,1746,1752,1762,1768,1776,2714,2738,2744,2762,2770,2776,2786,2792,2800,3242,3250,3256,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9408 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9408 5 (fun x => (if x<2744 then (if x<1720 then (if x<192 then (if x<144 then 0 else (if x<160 then 1 else 2)) else (if x<1690 then (if x<250 then 3 else 0) else (if x<1706 then 0 else 2))) else (if x<1768 then (if x<1752 then (if x<1746 then 1 else 1) else (if x<1762 then 3 else 3)) else (if x<2714 then (if x<1776 then 0 else 2) else (if x<2738 then 1 else 2)))) else (if x<3250 then (if x<2786 then (if x<2770 then (if x<2762 then 0 else 0) else (if x<2776 then 3 else 4)) else (if x<2800 then (if x<2792 then 4 else 2) else (if x<3242 then 1 else 0))) else (if x<3288 then (if x<3274 then (if x<3256 then 1 else 2) else (if x<3282 then 3 else 4)) else (if x<3304 then (if x<3298 then 0 else 2) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9409 : Finset ℕ := ([144,160,1690,1706,1746,1752,1762,1768,2738,2744,2762,2800,3250,3256,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9409 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9409 4 (fun x => (if x<2738 then (if x<1746 then (if x<1690 then (if x<160 then 0 else 1) else (if x<1706 then 0 else 1)) else (if x<1762 then (if x<1752 then 2 else 3) else (if x<1768 then 3 else 2))) else (if x<3250 then (if x<2762 then (if x<2744 then 0 else 1) else (if x<2800 then 2 else 2)) else (if x<3274 then (if x<3256 then 1 else 0) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9410 : Finset ℕ := ([136,144,160,192,250,1690,1706,1720,1738,1746,1752,1762,1768,1776,2714,2738,2744,2762,2770,2776,2786,2792,2800,3242,3250,3256,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9410 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9410 1738 4
  · have he : independentCachedBranchMembers9410.erase 1738=independentCachedBranchMembers9408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9408
  · have he : independentCachedBranchMembers9410.filter (independentCachedEdge 1738)=independentCachedBranchMembers9409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9409
def independentCachedBranchMembers9411 : Finset ℕ := ([132,136,144,160,192,222,238,246,250,252,1686,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3228,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9411 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9411 132 5
  · have he : independentCachedBranchMembers9411.erase 132=independentCachedBranchMembers9407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9407
  · have he : independentCachedBranchMembers9411.filter (independentCachedEdge 132)=independentCachedBranchMembers9410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9410
def independentCachedBranchMembers9412 : Finset ℕ := ([144,192,250,252,1692,1702,1720,1738,1746,1748,1768,1776,2714,2726,2744,2762,2764,2770,2772,2792,2800,3214,3222,3242,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9412 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9412 5 (fun x => (if x<2762 then (if x<1738 then (if x<252 then (if x<192 then 0 else (if x<250 then 1 else 0)) else (if x<1702 then (if x<1692 then 1 else 2) else (if x<1720 then 2 else 0))) else (if x<1776 then (if x<1748 then (if x<1746 then 2 else 0) else (if x<1768 then 1 else 1)) else (if x<2726 then (if x<2714 then 2 else 0) else (if x<2744 then 3 else 3)))) else (if x<3242 then (if x<2792 then (if x<2770 then (if x<2764 then 3 else 1) else (if x<2772 then 4 else 3)) else (if x<3214 then (if x<2800 then 4 else 0) else (if x<3222 then 2 else 4))) else (if x<3270 then (if x<3250 then (if x<3244 then 3 else 4) else (if x<3252 then 0 else 2)) else (if x<3298 then (if x<3288 then 3 else 0) else (if x<3300 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9413 : Finset ℕ := ([192,250,1692,1702,1738,1746,1768,1776,2714,2744,2764,2772,3242,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9413 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9413 4 (fun x => (if x<2714 then (if x<1738 then (if x<1692 then (if x<250 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<1768 then (if x<1746 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3242 then (if x<2764 then (if x<2744 then 2 else 3) else (if x<2772 then 2 else 3)) else (if x<3270 then (if x<3250 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9414 : Finset ℕ := ([144,192,250,252,1692,1702,1720,1738,1746,1748,1768,1776,2714,2716,2726,2744,2762,2764,2770,2772,2792,2800,3214,3222,3242,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9414 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9414 2716 4
  · have he : independentCachedBranchMembers9414.erase 2716=independentCachedBranchMembers9412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9412
  · have he : independentCachedBranchMembers9414.filter (independentCachedEdge 2716)=independentCachedBranchMembers9413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9413
def independentCachedBranchMembers9415 : Finset ℕ := ([250,1692,1738,1748,1768,2714,2726,2744,2764,2770,2800,3222,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9415 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9415 4 (fun x => (if x<2744 then (if x<1748 then (if x<1692 then 0 else (if x<1738 then 1 else 0)) else (if x<2714 then (if x<1768 then 2 else 1) else (if x<2726 then 0 else 3))) else (if x<3222 then (if x<2770 then (if x<2764 then 1 else 1) else (if x<2800 then 2 else 3)) else (if x<3252 then (if x<3242 then 2 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9416 : Finset ℕ := ([1738,1768,2726,2764,3242,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9416 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9416 3 (fun x => (if x<2764 then (if x<1768 then 0 else (if x<2726 then 1 else 2)) else (if x<3242 then 0 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9417 : Finset ℕ := ([144,250,1692,1738,1748,1768,2714,2726,2744,2764,2770,2800,3222,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9417 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9417 144 3
  · have he : independentCachedBranchMembers9417.erase 144=independentCachedBranchMembers9415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9415
  · have he : independentCachedBranchMembers9417.filter (independentCachedEdge 144)=independentCachedBranchMembers9416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9416
def independentCachedBranchMembers9418 : Finset ℕ := ([144,192,250,252,1692,1702,1720,1738,1740,1746,1748,1768,1776,2714,2716,2726,2744,2762,2764,2770,2772,2792,2800,3214,3222,3242,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9418 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9418 1740 4
  · have he : independentCachedBranchMembers9418.erase 1740=independentCachedBranchMembers9414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9414
  · have he : independentCachedBranchMembers9418.filter (independentCachedEdge 1740)=independentCachedBranchMembers9417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9417
def independentCachedBranchMembers9419 : Finset ℕ := ([252,1692,1720,1738,1746,2714,2726,2764,2772,2792,2800,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9419 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9419 4 (fun x => (if x<2764 then (if x<1738 then (if x<1692 then 0 else (if x<1720 then 0 else 1)) else (if x<2714 then (if x<1746 then 1 else 2) else (if x<2726 then 1 else 3))) else (if x<3244 then (if x<2792 then (if x<2772 then 0 else 2) else (if x<2800 then 1 else 3)) else (if x<3270 then (if x<3252 then 0 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9420 : Finset ℕ := ([1692,1720,2714,2726,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound9420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9420 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9420 3 (fun x => (if x<2726 then (if x<1720 then 0 else (if x<2714 then 1 else 0)) else (if x<3244 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9421 : Finset ℕ := ([192,252,1692,1720,1738,1746,2714,2726,2764,2772,2792,2800,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9421 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9421 192 3
  · have he : independentCachedBranchMembers9421.erase 192=independentCachedBranchMembers9419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9419
  · have he : independentCachedBranchMembers9421.filter (independentCachedEdge 192)=independentCachedBranchMembers9420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9420
def independentCachedBranchMembers9422 : Finset ℕ := ([144,192,250,252,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2714,2716,2726,2744,2762,2764,2770,2772,2792,2800,3214,3222,3242,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9422 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9422 1690 4
  · have he : independentCachedBranchMembers9422.erase 1690=independentCachedBranchMembers9418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9418
  · have he : independentCachedBranchMembers9422.filter (independentCachedEdge 1690)=independentCachedBranchMembers9421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9421
def independentCachedBranchMembers9423 : Finset ℕ := ([250,252,1702,1720,1768,1776,2726,2744,2792,2800,3242,3244,3250,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9423 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9423 4 (fun x => (if x<2792 then (if x<1768 then (if x<1702 then (if x<252 then 0 else 1) else (if x<1720 then 2 else 0)) else (if x<2726 then (if x<1776 then 1 else 2) else (if x<2744 then 3 else 1))) else (if x<3250 then (if x<3242 then (if x<2800 then 0 else 3) else (if x<3244 then 0 else 1)) else (if x<3298 then (if x<3252 then 2 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9424 : Finset ℕ := ([144,192,222,250,252,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2714,2716,2726,2744,2762,2764,2770,2772,2792,2800,3214,3222,3242,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9424 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9424 222 4
  · have he : independentCachedBranchMembers9424.erase 222=independentCachedBranchMembers9422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9422
  · have he : independentCachedBranchMembers9424.filter (independentCachedEdge 222)=independentCachedBranchMembers9423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9423
def independentCachedBranchMembers9425 : Finset ℕ := ([144,192,1702,1746,1748,1776,2726,2770,2772,2800,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9425 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9425 4 (fun x => (if x<2772 then (if x<1748 then (if x<1702 then (if x<192 then 0 else 1) else (if x<1746 then 2 else 0)) else (if x<2726 then (if x<1776 then 1 else 2) else (if x<2770 then 3 else 1))) else (if x<3252 then (if x<3222 then (if x<2800 then 0 else 3) else (if x<3250 then 0 else 2)) else (if x<3298 then (if x<3270 then 3 else 1) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9426 : Finset ℕ := ([136,144,192,222,250,252,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2714,2716,2726,2744,2762,2764,2770,2772,2792,2800,3214,3222,3242,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9426 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9426 136 4
  · have he : independentCachedBranchMembers9426.erase 136=independentCachedBranchMembers9424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9424
  · have he : independentCachedBranchMembers9426.filter (independentCachedEdge 136)=independentCachedBranchMembers9425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9425
def independentCachedBranchMembers9427 : Finset ℕ := ([132,136,144,160,192,222,238,246,250,252,1686,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9427 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9427 3238 5
  · have he : independentCachedBranchMembers9427.erase 3238=independentCachedBranchMembers9411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9411
  · have he : independentCachedBranchMembers9427.filter (independentCachedEdge 3238)=independentCachedBranchMembers9426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9426
def independentCachedBranchMembers9428 : Finset ℕ := ([160,192,246,252,1690,1708,1716,1734,1748,1762,1768,1776,2714,2726,2740,2758,2764,2772,2786,2792,2800,3214,3222,3228,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9428 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9428 5 (fun x => (if x<2758 then (if x<1734 then (if x<252 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<1708 then (if x<1690 then 1 else 2) else (if x<1716 then 2 else 0))) else (if x<1776 then (if x<1762 then (if x<1748 then 2 else 1) else (if x<1768 then 0 else 1)) else (if x<2726 then (if x<2714 then 2 else 3) else (if x<2740 then 0 else 3)))) else (if x<3228 then (if x<2792 then (if x<2772 then (if x<2764 then 3 else 1) else (if x<2786 then 4 else 4)) else (if x<3214 then (if x<2800 then 3 else 0) else (if x<3222 then 2 else 3))) else (if x<3274 then (if x<3250 then (if x<3242 then 4 else 4) else (if x<3256 then 0 else 2)) else (if x<3288 then (if x<3282 then 3 else 2) else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9429 : Finset ℕ := ([192,246,1690,1708,1734,1748,1762,1776,2726,2740,2764,2792,3222,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9429 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9429 4 (fun x => (if x<2726 then (if x<1734 then (if x<1690 then (if x<246 then 0 else 0) else (if x<1708 then 1 else 1)) else (if x<1762 then (if x<1748 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3222 then (if x<2764 then (if x<2740 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3274 then (if x<3250 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9430 : Finset ℕ := ([160,192,246,252,1690,1708,1716,1734,1748,1762,1768,1776,2714,2726,2732,2740,2758,2764,2772,2786,2792,2800,3214,3222,3228,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9430 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9430 2732 4
  · have he : independentCachedBranchMembers9430.erase 2732=independentCachedBranchMembers9428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9428
  · have he : independentCachedBranchMembers9430.filter (independentCachedEdge 2732)=independentCachedBranchMembers9429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9429
def independentCachedBranchMembers9431 : Finset ℕ := ([246,1708,1734,1748,1768,2714,2726,2740,2764,2786,2800,3222,3242,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9431 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9431 4 (fun x => (if x<2740 then (if x<1748 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<2714 then (if x<1768 then 1 else 2) else (if x<2726 then 3 else 0))) else (if x<3222 then (if x<2786 then (if x<2764 then 1 else 1) else (if x<2800 then 2 else 3)) else (if x<3256 then (if x<3242 then 0 else 2) else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9432 : Finset ℕ := ([1734,1748,2714,2764,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9432 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9432 3 (fun x => (if x<2764 then (if x<1748 then 0 else (if x<2714 then 1 else 2)) else (if x<3222 then 0 else (if x<3282 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9433 : Finset ℕ := ([160,246,1708,1734,1748,1768,2714,2726,2740,2764,2786,2800,3222,3242,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9433 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9433 160 3
  · have he : independentCachedBranchMembers9433.erase 160=independentCachedBranchMembers9431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9431
  · have he : independentCachedBranchMembers9433.filter (independentCachedEdge 160)=independentCachedBranchMembers9432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9432
def independentCachedBranchMembers9434 : Finset ℕ := ([160,192,246,252,1690,1708,1716,1734,1740,1748,1762,1768,1776,2714,2726,2732,2740,2758,2764,2772,2786,2792,2800,3214,3222,3228,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9434 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9434 1740 4
  · have he : independentCachedBranchMembers9434.erase 1740=independentCachedBranchMembers9430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9430
  · have he : independentCachedBranchMembers9434.filter (independentCachedEdge 1740)=independentCachedBranchMembers9433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9433
def independentCachedBranchMembers9435 : Finset ℕ := ([252,1708,1716,1734,1762,2714,2726,2764,2772,2792,2800,3228,3256,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9435 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9435 4 (fun x => (if x<2764 then (if x<1734 then (if x<1708 then 0 else (if x<1716 then 0 else 1)) else (if x<2714 then (if x<1762 then 1 else 2) else (if x<2726 then 3 else 1))) else (if x<3228 then (if x<2792 then (if x<2772 then 0 else 1) else (if x<2800 then 2 else 3)) else (if x<3274 then (if x<3256 then 0 else 3) else (if x<3282 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9436 : Finset ℕ := ([1708,1716,2714,2726,3228,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9436 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9436 3 (fun x => (if x<2726 then (if x<1716 then 0 else (if x<2714 then 1 else 2)) else (if x<3228 then 0 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9437 : Finset ℕ := ([192,252,1708,1716,1734,1762,2714,2726,2764,2772,2792,2800,3228,3256,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9437 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9437 192 3
  · have he : independentCachedBranchMembers9437.erase 192=independentCachedBranchMembers9435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9435
  · have he : independentCachedBranchMembers9437.filter (independentCachedEdge 192)=independentCachedBranchMembers9436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9436
def independentCachedBranchMembers9438 : Finset ℕ := ([160,192,246,252,1690,1702,1708,1716,1734,1740,1748,1762,1768,1776,2714,2726,2732,2740,2758,2764,2772,2786,2792,2800,3214,3222,3228,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9438 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9438 1702 4
  · have he : independentCachedBranchMembers9438.erase 1702=independentCachedBranchMembers9434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9434
  · have he : independentCachedBranchMembers9438.filter (independentCachedEdge 1702)=independentCachedBranchMembers9437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9437
def independentCachedBranchMembers9439 : Finset ℕ := ([246,252,1690,1716,1748,1776,2714,2740,2772,2800,3222,3228,3250,3256,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9439 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9439 4 (fun x => (if x<2772 then (if x<1748 then (if x<1690 then (if x<252 then 0 else 1) else (if x<1716 then 2 else 0)) else (if x<2714 then (if x<1776 then 1 else 2) else (if x<2740 then 3 else 1))) else (if x<3250 then (if x<3222 then (if x<2800 then 0 else 3) else (if x<3228 then 0 else 1)) else (if x<3282 then (if x<3256 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
