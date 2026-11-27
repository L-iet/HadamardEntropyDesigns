/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch207
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9440 : Finset ℕ := ([160,192,238,246,252,1690,1702,1708,1716,1734,1740,1748,1762,1768,1776,2714,2726,2732,2740,2758,2764,2772,2786,2792,2800,3214,3222,3228,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9440 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9440 238 4
  · have he : independentCachedBranchMembers9440.erase 238=independentCachedBranchMembers9438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9438
  · have he : independentCachedBranchMembers9440.filter (independentCachedEdge 238)=independentCachedBranchMembers9439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9439
def independentCachedBranchMembers9441 : Finset ℕ := ([160,192,1690,1762,1768,1776,2714,2786,2792,2800,3242,3250,3256,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9441 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9441 4 (fun x => (if x<2792 then (if x<1768 then (if x<1690 then (if x<192 then 0 else 1) else (if x<1762 then 2 else 0)) else (if x<2714 then (if x<1776 then 1 else 2) else (if x<2786 then 3 else 1))) else (if x<3256 then (if x<3242 then (if x<2800 then 0 else 3) else (if x<3250 then 0 else 2)) else (if x<3282 then (if x<3274 then 3 else 1) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9442 : Finset ℕ := ([132,160,192,238,246,252,1690,1702,1708,1716,1734,1740,1748,1762,1768,1776,2714,2726,2732,2740,2758,2764,2772,2786,2792,2800,3214,3222,3228,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9442 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9442 132 4
  · have he : independentCachedBranchMembers9442.erase 132=independentCachedBranchMembers9440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9440
  · have he : independentCachedBranchMembers9442.filter (independentCachedEdge 132)=independentCachedBranchMembers9441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9441
def independentCachedBranchMembers9443 : Finset ℕ := ([132,136,144,160,192,222,238,246,250,252,1686,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9443 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9443 3226 5
  · have he : independentCachedBranchMembers9443.erase 3226=independentCachedBranchMembers9427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9427
  · have he : independentCachedBranchMembers9443.filter (independentCachedEdge 3226)=independentCachedBranchMembers9442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9442
def independentCachedBranchMembers9444 : Finset ℕ := ([144,192,246,252,1692,1706,1716,1734,1746,1752,1764,1776,2714,2726,2732,2738,2744,2762,2772,2786,2792,3222,3242,3252,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9444 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9444 5 (fun x => (if x<2732 then (if x<1734 then (if x<252 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<1706 then (if x<1692 then 1 else 2) else (if x<1716 then 2 else 0))) else (if x<1764 then (if x<1746 then 2 else (if x<1752 then 0 else 1)) else (if x<2714 then (if x<1776 then 1 else 2) else (if x<2726 then 3 else 3)))) else (if x<3222 then (if x<2762 then (if x<2738 then 4 else (if x<2744 then 0 else 2)) else (if x<2786 then (if x<2772 then 4 else 0) else (if x<2792 then 2 else 1))) else (if x<3282 then (if x<3252 then (if x<3242 then 0 else 3) else (if x<3276 then 4 else 1)) else (if x<3300 then (if x<3288 then 4 else 3) else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9445 : Finset ℕ := ([144,252,1692,1706,1716,1734,1752,1776,2714,2732,2738,2792,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9445 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9445 4 (fun x => (if x<2714 then (if x<1716 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3222 then (if x<2738 then (if x<2732 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3282 then (if x<3276 then 3 else 3) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9446 : Finset ℕ := ([144,192,246,252,1692,1706,1716,1734,1746,1752,1764,1776,2714,2726,2732,2738,2744,2762,2772,2786,2792,3222,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9446 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9446 3270 4
  · have he : independentCachedBranchMembers9446.erase 3270=independentCachedBranchMembers9444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9444
  · have he : independentCachedBranchMembers9446.filter (independentCachedEdge 3270)=independentCachedBranchMembers9445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9445
def independentCachedBranchMembers9447 : Finset ℕ := ([192,246,1692,1706,1734,1746,1764,1776,2726,2738,2762,2792,3222,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9447 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9447 4 (fun x => (if x<2726 then (if x<1734 then (if x<1692 then (if x<246 then 0 else 0) else (if x<1706 then 1 else 1)) else (if x<1764 then (if x<1746 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3222 then (if x<2762 then (if x<2738 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3276 then (if x<3252 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9448 : Finset ℕ := ([144,192,246,252,1692,1706,1716,1734,1746,1752,1764,1776,2714,2726,2732,2738,2744,2762,2772,2786,2792,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9448 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9448 3228 4
  · have he : independentCachedBranchMembers9448.erase 3228=independentCachedBranchMembers9446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9446
  · have he : independentCachedBranchMembers9448.filter (independentCachedEdge 3228)=independentCachedBranchMembers9447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9447
def independentCachedBranchMembers9449 : Finset ℕ := ([144,192,246,252,1716,1746,1752,1764,2714,2726,2732,2762,3252,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9449 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9449 4 (fun x => (if x<2714 then (if x<1716 then (if x<246 then (if x<192 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1752 then (if x<1746 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3252 then (if x<2732 then (if x<2726 then 2 else 2) else (if x<2762 then 3 else 3)) else (if x<3288 then (if x<3282 then 3 else 3) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9450 : Finset ℕ := ([144,192,246,252,1692,1706,1716,1734,1746,1752,1764,1776,2702,2714,2726,2732,2738,2744,2762,2772,2786,2792,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9450 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9450 2702 4
  · have he : independentCachedBranchMembers9450.erase 2702=independentCachedBranchMembers9448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9448
  · have he : independentCachedBranchMembers9450.filter (independentCachedEdge 2702)=independentCachedBranchMembers9449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9449
def independentCachedBranchMembers9451 : Finset ℕ := ([144,246,1692,1734,1752,1764,2714,2726,2744,2786,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9451 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9451 4 (fun x => (if x<2744 then (if x<1752 then (if x<1692 then (if x<246 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2714 then (if x<1764 then 2 else 2) else (if x<2726 then 2 else 2))) else (if x<3252 then (if x<3222 then (if x<2786 then 1 else 1) else (if x<3242 then 0 else 3)) else (if x<3282 then (if x<3276 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9452 : Finset ℕ := ([144,192,246,252,1692,1706,1716,1734,1740,1746,1752,1764,1776,2702,2714,2726,2732,2738,2744,2762,2772,2786,2792,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9452 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9452 1740 4
  · have he : independentCachedBranchMembers9452.erase 1740=independentCachedBranchMembers9450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9450
  · have he : independentCachedBranchMembers9452.filter (independentCachedEdge 1740)=independentCachedBranchMembers9451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9451
def independentCachedBranchMembers9453 : Finset ℕ := ([192,252,1692,1716,1734,1746,2732,2744,2762,2786,3222,3242,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9453 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9453 4 (fun x => (if x<2762 then (if x<1734 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1716 then 1 else 2)) else (if x<2732 then (if x<1746 then 1 else 2) else (if x<2744 then 2 else 1))) else (if x<3276 then (if x<3222 then (if x<2786 then 2 else 1) else (if x<3242 then 3 else 3)) else (if x<3300 then (if x<3288 then 0 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9454 : Finset ℕ := ([144,192,246,252,1686,1692,1706,1716,1734,1740,1746,1752,1764,1776,2702,2714,2726,2732,2738,2744,2762,2772,2786,2792,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9454 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9454 1686 4
  · have he : independentCachedBranchMembers9454.erase 1686=independentCachedBranchMembers9452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9452
  · have he : independentCachedBranchMembers9454.filter (independentCachedEdge 1686)=independentCachedBranchMembers9453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9453
def independentCachedBranchMembers9455 : Finset ℕ := ([246,252,1706,1716,1764,1776,2726,2732,2738,2744,2786,2792,3242,3252,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9455 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9455 4 (fun x => (if x<2738 then (if x<1764 then (if x<1706 then (if x<252 then 0 else 1) else (if x<1716 then 2 else 0)) else (if x<2726 then (if x<1776 then 1 else 2) else (if x<2732 then 0 else 1))) else (if x<3242 then (if x<2786 then (if x<2744 then 2 else 3) else (if x<2792 then 3 else 2)) else (if x<3300 then (if x<3252 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9456 : Finset ℕ := ([144,192,222,246,252,1686,1692,1706,1716,1734,1740,1746,1752,1764,1776,2702,2714,2726,2732,2738,2744,2762,2772,2786,2792,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9456 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9456 222 4
  · have he : independentCachedBranchMembers9456.erase 222=independentCachedBranchMembers9454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9454
  · have he : independentCachedBranchMembers9456.filter (independentCachedEdge 222)=independentCachedBranchMembers9455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9455
def independentCachedBranchMembers9457 : Finset ℕ := ([144,192,1706,1746,1752,1776,2714,2738,2744,2762,2786,2792,3242,3282,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9457 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9457 4 (fun x => (if x<2744 then (if x<1752 then (if x<1706 then (if x<192 then 0 else 1) else (if x<1746 then 2 else 0)) else (if x<2714 then (if x<1776 then 1 else 2) else (if x<2738 then 0 else 2))) else (if x<3242 then (if x<2786 then (if x<2762 then 3 else 1) else (if x<2792 then 3 else 2)) else (if x<3288 then (if x<3282 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9458 : Finset ℕ := ([132,144,192,222,246,252,1686,1692,1706,1716,1734,1740,1746,1752,1764,1776,2702,2714,2726,2732,2738,2744,2762,2772,2786,2792,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9458 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9458 132 4
  · have he : independentCachedBranchMembers9458.erase 132=independentCachedBranchMembers9456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9456
  · have he : independentCachedBranchMembers9458.filter (independentCachedEdge 132)=independentCachedBranchMembers9457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9457
def independentCachedBranchMembers9459 : Finset ℕ := ([132,136,144,160,192,222,238,246,250,252,1686,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9459 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9459 2730 5
  · have he : independentCachedBranchMembers9459.erase 2730=independentCachedBranchMembers9443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9443
  · have he : independentCachedBranchMembers9459.filter (independentCachedEdge 2730)=independentCachedBranchMembers9458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9458
def independentCachedBranchMembers9460 : Finset ℕ := ([160,192,250,252,1686,1708,1720,1738,1752,1762,1764,1776,2714,2716,2726,2738,2740,2758,2770,2772,2792,3222,3242,3256,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9460 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9460 5 (fun x => (if x<2726 then (if x<1738 then (if x<252 then (if x<192 then 0 else (if x<250 then 1 else 0)) else (if x<1708 then (if x<1686 then 1 else 2) else (if x<1720 then 2 else 0))) else (if x<1764 then (if x<1752 then 2 else (if x<1762 then 1 else 0)) else (if x<2714 then (if x<1776 then 1 else 2) else (if x<2716 then 3 else 4)))) else (if x<3222 then (if x<2758 then (if x<2738 then 3 else (if x<2740 then 0 else 2)) else (if x<2772 then (if x<2770 then 4 else 2) else (if x<2792 then 1 else 0))) else (if x<3288 then (if x<3256 then (if x<3242 then 3 else 0) else (if x<3276 then 4 else 1)) else (if x<3300 then (if x<3298 then 3 else 4) else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9461 : Finset ℕ := ([160,252,1686,1708,1720,1738,1764,1776,2716,2726,2738,2772,3242,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9461 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9461 4 (fun x => (if x<2716 then (if x<1720 then (if x<1686 then (if x<252 then 0 else 0) else (if x<1708 then 1 else 0)) else (if x<1764 then (if x<1738 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3242 then (if x<2738 then (if x<2726 then 2 else 2) else (if x<2772 then 3 else 3)) else (if x<3288 then (if x<3276 then 3 else 3) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9462 : Finset ℕ := ([160,192,250,252,1686,1708,1720,1738,1752,1762,1764,1776,2714,2716,2726,2738,2740,2758,2770,2772,2792,3222,3242,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9462 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9462 3274 4
  · have he : independentCachedBranchMembers9462.erase 3274=independentCachedBranchMembers9460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9460
  · have he : independentCachedBranchMembers9462.filter (independentCachedEdge 3274)=independentCachedBranchMembers9461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9461
def independentCachedBranchMembers9463 : Finset ℕ := ([192,250,1686,1708,1738,1752,1762,1776,2714,2738,2758,2772,3242,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9463 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9463 4 (fun x => (if x<2714 then (if x<1738 then (if x<1686 then (if x<250 then 0 else 0) else (if x<1708 then 1 else 1)) else (if x<1762 then (if x<1752 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3242 then (if x<2758 then (if x<2738 then 2 else 3) else (if x<2772 then 2 else 3)) else (if x<3276 then (if x<3256 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9464 : Finset ℕ := ([160,192,250,252,1686,1708,1720,1738,1752,1762,1764,1776,2714,2716,2726,2738,2740,2758,2770,2772,2792,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9464 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9464 3244 4
  · have he : independentCachedBranchMembers9464.erase 3244=independentCachedBranchMembers9462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9462
  · have he : independentCachedBranchMembers9464.filter (independentCachedEdge 3244)=independentCachedBranchMembers9463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9463
def independentCachedBranchMembers9465 : Finset ℕ := ([160,192,250,252,1720,1752,1762,1764,2714,2716,2726,2758,3256,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9465 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9465 4 (fun x => (if x<2714 then (if x<1720 then (if x<250 then (if x<192 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1762 then (if x<1752 then 0 else 1) else (if x<1764 then 0 else 1))) else (if x<3256 then (if x<2726 then (if x<2716 then 2 else 3) else (if x<2758 then 2 else 3)) else (if x<3298 then (if x<3288 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9466 : Finset ℕ := ([160,192,250,252,1686,1708,1720,1738,1752,1762,1764,1776,2702,2714,2716,2726,2738,2740,2758,2770,2772,2792,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9466 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9466 2702 4
  · have he : independentCachedBranchMembers9466.erase 2702=independentCachedBranchMembers9464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9464
  · have he : independentCachedBranchMembers9466.filter (independentCachedEdge 2702)=independentCachedBranchMembers9465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9465
def independentCachedBranchMembers9467 : Finset ℕ := ([160,250,1708,1738,1752,1764,2714,2726,2740,2770,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9467 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9467 4 (fun x => (if x<2740 then (if x<1752 then (if x<1708 then (if x<250 then 0 else 0) else (if x<1738 then 1 else 1)) else (if x<2714 then (if x<1764 then 2 else 2) else (if x<2726 then 2 else 2))) else (if x<3256 then (if x<3222 then (if x<2770 then 1 else 1) else (if x<3242 then 3 else 0)) else (if x<3298 then (if x<3276 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9468 : Finset ℕ := ([160,192,250,252,1686,1708,1720,1738,1740,1752,1762,1764,1776,2702,2714,2716,2726,2738,2740,2758,2770,2772,2792,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9468 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9468 1740 4
  · have he : independentCachedBranchMembers9468.erase 1740=independentCachedBranchMembers9466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9466
  · have he : independentCachedBranchMembers9468.filter (independentCachedEdge 1740)=independentCachedBranchMembers9467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9467
def independentCachedBranchMembers9469 : Finset ℕ := ([192,252,1708,1720,1738,1762,2716,2740,2758,2770,3222,3242,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9469 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9469 4 (fun x => (if x<2758 then (if x<1738 then (if x<1708 then (if x<252 then 0 else 0) else (if x<1720 then 1 else 2)) else (if x<2716 then (if x<1762 then 1 else 2) else (if x<2740 then 2 else 1))) else (if x<3276 then (if x<3222 then (if x<2770 then 2 else 1) else (if x<3242 then 3 else 3)) else (if x<3300 then (if x<3288 then 0 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9470 : Finset ℕ := ([160,192,250,252,1686,1706,1708,1720,1738,1740,1752,1762,1764,1776,2702,2714,2716,2726,2738,2740,2758,2770,2772,2792,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9470 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9470 1706 4
  · have he : independentCachedBranchMembers9470.erase 1706=independentCachedBranchMembers9468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9468
  · have he : independentCachedBranchMembers9470.filter (independentCachedEdge 1706)=independentCachedBranchMembers9469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9469
def independentCachedBranchMembers9471 : Finset ℕ := ([250,252,1686,1720,1752,1776,2714,2716,2738,2740,2770,2772,3222,3256,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9471 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9471 4 (fun x => (if x<2738 then (if x<1752 then (if x<1686 then (if x<252 then 0 else 1) else (if x<1720 then 2 else 0)) else (if x<2714 then (if x<1776 then 1 else 2) else (if x<2716 then 0 else 1))) else (if x<3222 then (if x<2770 then (if x<2740 then 2 else 3) else (if x<2772 then 3 else 2)) else (if x<3288 then (if x<3256 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
