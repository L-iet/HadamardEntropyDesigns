/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch210
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9536 : Finset ℕ := ([192,238,246,250,252,1738,1740,1746,1748,1762,1764,1768,1776,2758,2764,2770,2776,2786,2788,2792,2800,3270,3274,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9536 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9536 5 (fun x => (if x<2764 then (if x<1746 then (if x<250 then (if x<238 then 0 else (if x<246 then 0 else 1)) else (if x<1738 then (if x<252 then 2 else 3) else (if x<1740 then 0 else 3))) else (if x<1764 then (if x<1748 then 1 else (if x<1762 then 4 else 2)) else (if x<1776 then (if x<1768 then 0 else 4) else (if x<2758 then 3 else 0)))) else (if x<3270 then (if x<2786 then (if x<2770 then 4 else (if x<2776 then 2 else 3)) else (if x<2792 then (if x<2788 then 1 else 3) else (if x<2800 then 0 else 4))) else (if x<3298 then (if x<3284 then (if x<3274 then 1 else 2) else (if x<3288 then 3 else 4)) else (if x<3304 then (if x<3300 then 0 else 4) else (if x<3312 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9537 : Finset ℕ := ([238,252,1740,1746,1764,1768,2764,2770,2788,2792,3270,3274,3284,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9537 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9537 4 (fun x => (if x<2788 then (if x<1764 then (if x<1740 then (if x<252 then 0 else 1) else (if x<1746 then 0 else 2)) else (if x<2764 then (if x<1768 then 1 else 2) else (if x<2770 then 1 else 3))) else (if x<3284 then (if x<3270 then (if x<2792 then 0 else 3) else (if x<3274 then 0 else 2)) else (if x<3298 then (if x<3288 then 1 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9538 : Finset ℕ := ([192,238,246,250,252,1738,1740,1746,1748,1762,1764,1768,1776,2758,2764,2770,2776,2786,2788,2792,2800,3270,3274,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9538 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9538 3282 4
  · have he : independentCachedBranchMembers9538.erase 3282=independentCachedBranchMembers9536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9536
  · have he : independentCachedBranchMembers9538.filter (independentCachedEdge 3282)=independentCachedBranchMembers9537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9537
def independentCachedBranchMembers9539 : Finset ℕ := ([246,250,1740,1746,1762,1776,2764,2770,2786,2800,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9539 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9539 4 (fun x => (if x<2786 then (if x<1762 then (if x<1740 then (if x<250 then 0 else 1) else (if x<1746 then 2 else 0)) else (if x<2764 then (if x<1776 then 1 else 2) else (if x<2770 then 3 else 1))) else (if x<3284 then (if x<3270 then (if x<2800 then 0 else 3) else (if x<3274 then 0 else 1)) else (if x<3300 then (if x<3288 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9540 : Finset ℕ := ([192,238,246,250,252,1738,1740,1746,1748,1762,1764,1768,1776,2758,2764,2770,2776,2786,2788,2792,2800,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9540 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9540 3276 4
  · have he : independentCachedBranchMembers9540.erase 3276=independentCachedBranchMembers9538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9538
  · have he : independentCachedBranchMembers9540.filter (independentCachedEdge 3276)=independentCachedBranchMembers9539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9539
def independentCachedBranchMembers9541 : Finset ℕ := ([238,250,1738,1748,1762,1768,2758,2764,2770,2776,2788,2800,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9541 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9541 4 (fun x => (if x<2770 then (if x<1762 then (if x<1738 then (if x<250 then 0 else 1) else (if x<1748 then 0 else 2)) else (if x<2758 then (if x<1768 then 1 else 2) else (if x<2764 then 0 else 2))) else (if x<3274 then (if x<2788 then (if x<2776 then 1 else 3) else (if x<2800 then 3 else 2)) else (if x<3298 then (if x<3284 then 1 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9542 : Finset ℕ := ([192,238,246,250,252,1738,1740,1746,1748,1762,1764,1768,1776,2758,2764,2770,2772,2776,2786,2788,2792,2800,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9542 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9542 2772 4
  · have he : independentCachedBranchMembers9542.erase 2772=independentCachedBranchMembers9540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9540
  · have he : independentCachedBranchMembers9542.filter (independentCachedEdge 2772)=independentCachedBranchMembers9541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9541
def independentCachedBranchMembers9543 : Finset ℕ := ([246,252,1738,1748,1764,1776,2758,2764,2770,2776,2786,2792,3274,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9543 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9543 4 (fun x => (if x<2770 then (if x<1764 then (if x<1738 then (if x<252 then 0 else 1) else (if x<1748 then 2 else 0)) else (if x<2758 then (if x<1776 then 1 else 2) else (if x<2764 then 0 else 1))) else (if x<3274 then (if x<2786 then (if x<2776 then 2 else 3) else (if x<2792 then 3 else 2)) else (if x<3300 then (if x<3284 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9544 : Finset ℕ := ([192,238,246,250,252,1738,1740,1746,1748,1762,1764,1768,1776,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9544 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9544 2762 4
  · have he : independentCachedBranchMembers9544.erase 2762=independentCachedBranchMembers9542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9542
  · have he : independentCachedBranchMembers9544.filter (independentCachedEdge 2762)=independentCachedBranchMembers9543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9543
def independentCachedBranchMembers9545 : Finset ℕ := ([238,246,1738,1740,1746,1748,1768,1776,2758,2776,2786,2788,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9545 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9545 4 (fun x => (if x<2758 then (if x<1746 then (if x<1738 then (if x<246 then 0 else 1) else (if x<1740 then 0 else 2)) else (if x<1768 then (if x<1748 then 1 else 3) else (if x<1776 then 3 else 2))) else (if x<3270 then (if x<2786 then (if x<2776 then 0 else 2) else (if x<2788 then 1 else 2)) else (if x<3298 then (if x<3288 then 1 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9546 : Finset ℕ := ([192,238,246,250,252,1738,1740,1746,1748,1752,1762,1764,1768,1776,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9546 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9546 1752 4
  · have he : independentCachedBranchMembers9546.erase 1752=independentCachedBranchMembers9544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9544
  · have he : independentCachedBranchMembers9546.filter (independentCachedEdge 1752)=independentCachedBranchMembers9545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9545
def independentCachedBranchMembers9547 : Finset ℕ := ([250,252,1738,1740,1746,1748,1762,1764,2758,2776,2792,2800,3270,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9547 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9547 4 (fun x => (if x<2758 then (if x<1746 then (if x<1738 then (if x<252 then 0 else 1) else (if x<1740 then 0 else 1)) else (if x<1762 then (if x<1748 then 2 else 3) else (if x<1764 then 3 else 2))) else (if x<3270 then (if x<2792 then (if x<2776 then 2 else 0) else (if x<2800 then 1 else 2)) else (if x<3304 then (if x<3288 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9548 : Finset ℕ := ([192,238,246,250,252,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9548 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9548 1734 4
  · have he : independentCachedBranchMembers9548.erase 1734=independentCachedBranchMembers9546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9546
  · have he : independentCachedBranchMembers9548.filter (independentCachedEdge 1734)=independentCachedBranchMembers9547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9547
def independentCachedBranchMembers9549 : Finset ℕ := ([238,246,250,252,1762,1764,1768,1776,2786,2788,2792,2800,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9549 4 (fun x => (if x<2786 then (if x<1762 then (if x<250 then (if x<246 then 0 else 1) else (if x<252 then 2 else 3)) else (if x<1768 then (if x<1764 then 0 else 1) else (if x<1776 then 2 else 3))) else (if x<3298 then (if x<2792 then (if x<2788 then 1 else 0) else (if x<2800 then 3 else 2)) else (if x<3304 then (if x<3300 then 2 else 3) else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9550 : Finset ℕ := ([192,222,238,246,250,252,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9550 222 4
  · have he : independentCachedBranchMembers9550.erase 222=independentCachedBranchMembers9548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9548
  · have he : independentCachedBranchMembers9550.filter (independentCachedEdge 222)=independentCachedBranchMembers9549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9549
def independentCachedBranchMembers9551 : Finset ℕ := ([132,136,144,160,190,192,222,238,246,250,252,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9551 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9551 190 5
  · have he : independentCachedBranchMembers9551.erase 190=independentCachedBranchMembers9535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9535
  · have he : independentCachedBranchMembers9551.filter (independentCachedEdge 190)=independentCachedBranchMembers9550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9550
def independentCachedBranchMembers9552 : Finset ℕ := ([136,144,160,192,252,1708,1716,1720,1740,1748,1752,1768,1776,2716,2740,2744,2764,2776,2788,2792,2800,3228,3244,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9552 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9552 5 (fun x => (if x<2744 then (if x<1720 then (if x<192 then (if x<144 then 0 else (if x<160 then 1 else 2)) else (if x<1708 then (if x<252 then 3 else 0) else (if x<1716 then 0 else 1))) else (if x<1768 then (if x<1748 then (if x<1740 then 2 else 3) else (if x<1752 then 4 else 0)) else (if x<2716 then (if x<1776 then 4 else 3) else (if x<2740 then 0 else 2)))) else (if x<3244 then (if x<2788 then (if x<2764 then 1 else (if x<2776 then 4 else 3)) else (if x<2800 then (if x<2792 then 3 else 0) else (if x<3228 then 4 else 1))) else (if x<3288 then (if x<3276 then (if x<3256 then 2 else 0) else (if x<3284 then 0 else 3)) else (if x<3304 then (if x<3300 then 4 else 4) else (if x<3312 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9553 : Finset ℕ := ([136,192,1716,1740,1752,1768,2740,2764,2776,2792,3228,3244,3256,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9553 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9553 4 (fun x => (if x<2776 then (if x<1752 then (if x<1716 then (if x<192 then 0 else 1) else (if x<1740 then 2 else 0)) else (if x<2740 then (if x<1768 then 1 else 2) else (if x<2764 then 3 else 1))) else (if x<3256 then (if x<3228 then (if x<2792 then 0 else 3) else (if x<3244 then 0 else 2)) else (if x<3300 then (if x<3284 then 3 else 1) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9554 : Finset ℕ := ([136,144,160,192,252,1708,1716,1720,1740,1748,1752,1768,1776,2716,2740,2744,2764,2776,2788,2792,2800,3228,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9554 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9554 3252 4
  · have he : independentCachedBranchMembers9554.erase 3252=independentCachedBranchMembers9552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9552
  · have he : independentCachedBranchMembers9554.filter (independentCachedEdge 3252)=independentCachedBranchMembers9553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9553
def independentCachedBranchMembers9555 : Finset ℕ := ([136,160,1708,1720,1748,1768,2716,2740,2764,2776,2788,2800,3244,3256,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9555 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9555 4 (fun x => (if x<2764 then (if x<1748 then (if x<1708 then (if x<160 then 0 else 1) else (if x<1720 then 0 else 1)) else (if x<2716 then (if x<1768 then 2 else 2) else (if x<2740 then 0 else 1))) else (if x<3244 then (if x<2788 then (if x<2776 then 2 else 3) else (if x<2800 then 3 else 2)) else (if x<3284 then (if x<3256 then 1 else 0) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9556 : Finset ℕ := ([136,144,160,192,252,1708,1716,1720,1740,1748,1752,1768,1776,2716,2740,2744,2764,2772,2776,2788,2792,2800,3228,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9556 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9556 2772 4
  · have he : independentCachedBranchMembers9556.erase 2772=independentCachedBranchMembers9554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9554
  · have he : independentCachedBranchMembers9556.filter (independentCachedEdge 2772)=independentCachedBranchMembers9555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9555
def independentCachedBranchMembers9557 : Finset ℕ := ([144,192,1708,1748,1752,1776,2716,2740,2744,2764,2788,2792,3244,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9557 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9557 4 (fun x => (if x<2744 then (if x<1752 then (if x<1708 then (if x<192 then 0 else 1) else (if x<1748 then 2 else 0)) else (if x<2716 then (if x<1776 then 1 else 2) else (if x<2740 then 0 else 2))) else (if x<3244 then (if x<2788 then (if x<2764 then 3 else 1) else (if x<2792 then 3 else 2)) else (if x<3288 then (if x<3284 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9558 : Finset ℕ := ([136,144,160,192,252,1708,1716,1720,1740,1748,1752,1768,1776,2716,2732,2740,2744,2764,2772,2776,2788,2792,2800,3228,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9558 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9558 2732 4
  · have he : independentCachedBranchMembers9558.erase 2732=independentCachedBranchMembers9556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9556
  · have he : independentCachedBranchMembers9558.filter (independentCachedEdge 2732)=independentCachedBranchMembers9557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9557
def independentCachedBranchMembers9559 : Finset ℕ := ([136,144,1708,1716,1740,1748,1768,1776,2716,2744,2776,2788,3228,3256,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9559 4 (fun x => (if x<2716 then (if x<1740 then (if x<1708 then (if x<144 then 0 else 1) else (if x<1716 then 0 else 1)) else (if x<1768 then (if x<1748 then 2 else 3) else (if x<1776 then 3 else 2))) else (if x<3228 then (if x<2776 then (if x<2744 then 0 else 1) else (if x<2788 then 2 else 2)) else (if x<3288 then (if x<3256 then 1 else 0) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9560 : Finset ℕ := ([136,144,160,192,252,1708,1716,1720,1740,1748,1752,1764,1768,1776,2716,2732,2740,2744,2764,2772,2776,2788,2792,2800,3228,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9560 1764 4
  · have he : independentCachedBranchMembers9560.erase 1764=independentCachedBranchMembers9558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9558
  · have he : independentCachedBranchMembers9560.filter (independentCachedEdge 1764)=independentCachedBranchMembers9559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9559
def independentCachedBranchMembers9561 : Finset ℕ := ([160,192,1708,1716,1720,1740,1748,1752,2716,2788,2792,2800,3228,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9561 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9561 4 (fun x => (if x<2716 then (if x<1720 then (if x<1708 then (if x<192 then 0 else 1) else (if x<1716 then 0 else 2)) else (if x<1748 then (if x<1740 then 3 else 1) else (if x<1752 then 3 else 2))) else (if x<3228 then (if x<2792 then (if x<2788 then 2 else 0) else (if x<2800 then 1 else 2)) else (if x<3304 then (if x<3300 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9562 : Finset ℕ := ([136,144,160,192,252,1692,1708,1716,1720,1740,1748,1752,1764,1768,1776,2716,2732,2740,2744,2764,2772,2776,2788,2792,2800,3228,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9562 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9562 1692 4
  · have he : independentCachedBranchMembers9562.erase 1692=independentCachedBranchMembers9560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9560
  · have he : independentCachedBranchMembers9562.filter (independentCachedEdge 1692)=independentCachedBranchMembers9561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9561
def independentCachedBranchMembers9563 : Finset ℕ := ([136,144,160,192,1720,1752,1768,1776,2744,2776,2792,2800,3256,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9563 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9563 4 (fun x => (if x<2744 then (if x<1720 then (if x<160 then (if x<144 then 0 else 1) else (if x<192 then 2 else 3)) else (if x<1768 then (if x<1752 then 0 else 1) else (if x<1776 then 2 else 3))) else (if x<3256 then (if x<2792 then (if x<2776 then 1 else 0) else (if x<2800 then 3 else 2)) else (if x<3304 then (if x<3288 then 2 else 3) else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9564 : Finset ℕ := ([132,136,144,160,192,252,1692,1708,1716,1720,1740,1748,1752,1764,1768,1776,2716,2732,2740,2744,2764,2772,2776,2788,2792,2800,3228,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9564 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9564 132 4
  · have he : independentCachedBranchMembers9564.erase 132=independentCachedBranchMembers9562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9562
  · have he : independentCachedBranchMembers9564.filter (independentCachedEdge 132)=independentCachedBranchMembers9563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9563
def independentCachedBranchMembers9565 : Finset ℕ := ([130,132,136,144,160,190,192,222,238,246,250,252,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9565 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9565 130 5
  · have he : independentCachedBranchMembers9565.erase 130=independentCachedBranchMembers9551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9551
  · have he : independentCachedBranchMembers9565.filter (independentCachedEdge 130)=independentCachedBranchMembers9564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9564
def independentCachedBranchMembers9566 : Finset ℕ := ([10,12,18,20,34,36,40,48,66,68,72,80,126,130,132,136,144,160,190,192,222,238,246,250,252,1536,1566,1582,1590,1594,1596,1614,1622,1626,1628,1638,1642,1644,1650,1652,1656,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9566 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9566 126 6
  · have he : independentCachedBranchMembers9566.erase 126=independentCachedBranchMembers9284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9284
  · have he : independentCachedBranchMembers9566.filter (independentCachedEdge 126)=independentCachedBranchMembers9565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9565
def independentCachedBranchMembers9567 : Finset ℕ := ([36,48,66,72,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2740,2758,2762,2776,3118,3132,3158,3162,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9567 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9567 6 (fun x => (if x<2638 then (if x<1708 then (if x<1590 then (if x<66 then (if x<48 then 0 else 1) else (if x<72 then 0 else 1)) else (if x<1614 then (if x<1596 then 1 else 0) else (if x<1626 then 1 else 0))) else (if x<1748 then (if x<1734 then (if x<1714 then 2 else 2) else (if x<1738 then 2 else 3)) else (if x<2614 then (if x<1752 then 3 else 2) else (if x<2618 then 4 else 5)))) else (if x<3132 then (if x<2758 then (if x<2732 then (if x<2652 then 4 else 5) else (if x<2740 then 0 else 1)) else (if x<2776 then (if x<2762 then 3 else 0) else (if x<3118 then 3 else 4))) else (if x<3252 then (if x<3162 then (if x<3158 then 5 else 4) else (if x<3238 then 5 else 2)) else (if x<3274 then (if x<3256 then 0 else 2) else (if x<3276 then 1 else (if x<3282 then 2 else 0)))))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
