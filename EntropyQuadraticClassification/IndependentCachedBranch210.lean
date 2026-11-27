/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch209
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9504 : Finset ℕ := ([132,136,192,222,238,252,1686,1690,1702,1706,1716,1720,1740,1746,1762,1776,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9504 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9504 132 4
  · have he : independentCachedBranchMembers9504.erase 132=independentCachedBranchMembers9502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9502
  · have he : independentCachedBranchMembers9504.filter (independentCachedEdge 132)=independentCachedBranchMembers9503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9503
def independentCachedBranchMembers9505 : Finset ℕ := ([132,136,144,160,192,222,238,246,250,252,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9505 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9505 1714 5
  · have he : independentCachedBranchMembers9505.erase 1714=independentCachedBranchMembers9475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9475
  · have he : independentCachedBranchMembers9505.filter (independentCachedEdge 1714)=independentCachedBranchMembers9504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9504
def independentCachedBranchMembers9506 : Finset ℕ := ([192,252,1690,1692,1702,1708,1734,1738,1740,1776,2702,2740,2770,2776,2788,2792,3214,3250,3256,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9506 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9506 5 (fun x => (if x<2770 then (if x<1734 then (if x<1692 then (if x<252 then 0 else (if x<1690 then 0 else 1)) else (if x<1702 then 2 else (if x<1708 then 1 else 3))) else (if x<1776 then (if x<1738 then 2 else (if x<1740 then 3 else 0)) else (if x<2702 then 0 else (if x<2740 then 1 else 3)))) else (if x<3256 then (if x<2792 then (if x<2776 then 3 else (if x<2788 then 0 else 0)) else (if x<3214 then 3 else (if x<3250 then 2 else 4))) else (if x<3298 then (if x<3284 then 2 else (if x<3288 then 0 else 4)) else (if x<3300 then 2 else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9507 : Finset ℕ := ([252,1690,1708,1740,2770,2788,2792,3214,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9507 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9507 4 (fun x => (if x<2792 then (if x<1740 then (if x<1690 then 0 else (if x<1708 then 1 else 0)) else (if x<2770 then 1 else (if x<2788 then 2 else 0))) else (if x<3284 then (if x<3214 then 2 else (if x<3256 then 1 else 3)) else (if x<3288 then 3 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9508 : Finset ℕ := ([192,252,1690,1692,1702,1708,1734,1738,1740,1776,2702,2740,2770,2776,2786,2788,2792,3214,3250,3256,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9508 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9508 2786 4
  · have he : independentCachedBranchMembers9508.erase 2786=independentCachedBranchMembers9506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9506
  · have he : independentCachedBranchMembers9508.filter (independentCachedEdge 2786)=independentCachedBranchMembers9507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9507
def independentCachedBranchMembers9509 : Finset ℕ := ([192,1702,1738,1740,2740,2776,2792,3214,3256,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9509 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9509 4 (fun x => (if x<2792 then (if x<1740 then (if x<1702 then 0 else (if x<1738 then 1 else 0)) else (if x<2740 then 1 else (if x<2776 then 2 else 0))) else (if x<3284 then (if x<3214 then 2 else (if x<3256 then 1 else 2)) else (if x<3298 then 3 else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9510 : Finset ℕ := ([192,252,1690,1692,1702,1708,1734,1738,1740,1776,2702,2740,2744,2770,2776,2786,2788,2792,3214,3250,3256,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9510 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9510 2744 4
  · have he : independentCachedBranchMembers9510.erase 2744=independentCachedBranchMembers9508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9508
  · have he : independentCachedBranchMembers9510.filter (independentCachedEdge 2744)=independentCachedBranchMembers9509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9509
def independentCachedBranchMembers9511 : Finset ℕ := ([192,252,1690,1702,1708,1738,2740,2770,2776,2788,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9511 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9511 4 (fun x => (if x<2740 then (if x<1702 then (if x<252 then 0 else (if x<1690 then 0 else 1)) else (if x<1708 then 1 else (if x<1738 then 2 else 2))) else (if x<2788 then (if x<2770 then 2 else (if x<2776 then 2 else 0)) else (if x<3288 then 0 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9512 : Finset ℕ := ([192,252,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2740,2744,2770,2776,2786,2788,2792,3214,3250,3256,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9512 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9512 1706 4
  · have he : independentCachedBranchMembers9512.erase 1706=independentCachedBranchMembers9510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9510
  · have he : independentCachedBranchMembers9512.filter (independentCachedEdge 1706)=independentCachedBranchMembers9511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9511
def independentCachedBranchMembers9513 : Finset ℕ := ([252,1692,1702,1708,1734,1740,2702,2740,2788,3214,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9513 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9513 4 (fun x => (if x<2702 then (if x<1708 then (if x<1692 then 0 else (if x<1702 then 0 else 1)) else (if x<1734 then 2 else (if x<1740 then 2 else 1))) else (if x<3214 then (if x<2740 then 1 else (if x<2788 then 0 else 1)) else (if x<3284 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9514 : Finset ℕ := ([192,250,252,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2740,2744,2770,2776,2786,2788,2792,3214,3250,3256,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9514 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9514 250 4
  · have he : independentCachedBranchMembers9514.erase 250=independentCachedBranchMembers9512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9512
  · have he : independentCachedBranchMembers9514.filter (independentCachedEdge 250)=independentCachedBranchMembers9513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9513
def independentCachedBranchMembers9515 : Finset ℕ := ([192,1690,1692,1734,1738,1740,2702,2770,2776,3214,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9515 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9515 4 (fun x => (if x<2702 then (if x<1734 then (if x<1690 then 0 else (if x<1692 then 1 else 2)) else (if x<1738 then 0 else (if x<1740 then 2 else 1))) else (if x<3214 then (if x<2770 then 1 else (if x<2776 then 0 else 1)) else (if x<3284 then 2 else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9516 : Finset ℕ := ([160,192,250,252,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2740,2744,2770,2776,2786,2788,2792,3214,3250,3256,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9516 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9516 160 4
  · have he : independentCachedBranchMembers9516.erase 160=independentCachedBranchMembers9514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9514
  · have he : independentCachedBranchMembers9516.filter (independentCachedEdge 160)=independentCachedBranchMembers9515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9515
def independentCachedBranchMembers9517 : Finset ℕ := ([252,1692,1702,1706,1740,2702,2740,2744,2770,2788,2792,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9517 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9517 4 (fun x => (if x<2744 then (if x<1706 then (if x<1692 then 0 else (if x<1702 then 0 else 1)) else (if x<2702 then (if x<1740 then 2 else 1) else (if x<2740 then 1 else 0))) else (if x<3250 then (if x<2788 then (if x<2770 then 2 else 3) else (if x<2792 then 1 else 3)) else (if x<3288 then (if x<3284 then 2 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9518 : Finset ℕ := ([1692,1740,2702,2770,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9518 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9518 3 (fun x => (if x<2770 then (if x<1740 then 0 else (if x<2702 then 1 else 0)) else (if x<3284 then 2 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9519 : Finset ℕ := ([160,252,1692,1702,1706,1740,2702,2740,2744,2770,2788,2792,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9519 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9519 160 3
  · have he : independentCachedBranchMembers9519.erase 160=independentCachedBranchMembers9517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9517
  · have he : independentCachedBranchMembers9519.filter (independentCachedEdge 160)=independentCachedBranchMembers9518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9518
def independentCachedBranchMembers9520 : Finset ℕ := ([160,192,250,252,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2740,2744,2770,2776,2786,2788,2792,3214,3250,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9520 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9520 3282 4
  · have he : independentCachedBranchMembers9520.erase 3282=independentCachedBranchMembers9516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9516
  · have he : independentCachedBranchMembers9520.filter (independentCachedEdge 3282)=independentCachedBranchMembers9519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9519
def independentCachedBranchMembers9521 : Finset ℕ := ([250,1690,1706,1734,1740,2702,2740,2770,2776,2786,2792,3250,3256,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9521 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9521 4 (fun x => (if x<2770 then (if x<1734 then (if x<1690 then 0 else (if x<1706 then 0 else 1)) else (if x<2702 then (if x<1740 then 1 else 2) else (if x<2740 then 1 else 3))) else (if x<3250 then (if x<2786 then (if x<2776 then 0 else 2) else (if x<2792 then 1 else 3)) else (if x<3284 then (if x<3256 then 0 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9522 : Finset ℕ := ([1690,1706,2702,2740,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9522 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9522 3 (fun x => (if x<2740 then (if x<1706 then 0 else (if x<2702 then 1 else 0)) else (if x<3250 then 2 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9523 : Finset ℕ := ([192,250,1690,1706,1734,1740,2702,2740,2770,2776,2786,2792,3250,3256,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9523 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9523 192 3
  · have he : independentCachedBranchMembers9523.erase 192=independentCachedBranchMembers9521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9521
  · have he : independentCachedBranchMembers9523.filter (independentCachedEdge 192)=independentCachedBranchMembers9522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9522
def independentCachedBranchMembers9524 : Finset ℕ := ([160,192,250,252,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2740,2744,2770,2776,2786,2788,2792,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9524 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9524 3252 4
  · have he : independentCachedBranchMembers9524.erase 3252=independentCachedBranchMembers9520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9520
  · have he : independentCachedBranchMembers9524.filter (independentCachedEdge 3252)=independentCachedBranchMembers9523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9523
def independentCachedBranchMembers9525 : Finset ℕ := ([160,250,1690,1702,1708,1738,2740,2770,2776,2788,3214,3250,3256,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9525 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9525 4 (fun x => (if x<2776 then (if x<1708 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2740 then (if x<1738 then 2 else 2) else (if x<2770 then 2 else 2))) else (if x<3256 then (if x<3214 then (if x<2788 then 1 else 1) else (if x<3250 then 3 else 0)) else (if x<3298 then (if x<3284 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9526 : Finset ℕ := ([160,192,250,252,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2740,2744,2770,2772,2776,2786,2788,2792,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9526 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9526 2772 4
  · have he : independentCachedBranchMembers9526.erase 2772=independentCachedBranchMembers9524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9524
  · have he : independentCachedBranchMembers9526.filter (independentCachedEdge 2772)=independentCachedBranchMembers9525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9525
def independentCachedBranchMembers9527 : Finset ℕ := ([192,252,1692,1708,1734,1738,2740,2744,2770,2786,3214,3250,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9527 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9527 4 (fun x => (if x<2770 then (if x<1734 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2740 then (if x<1738 then 1 else 2) else (if x<2744 then 2 else 1))) else (if x<3284 then (if x<3214 then (if x<2786 then 2 else 1) else (if x<3250 then 3 else 3)) else (if x<3300 then (if x<3288 then 0 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9528 : Finset ℕ := ([160,192,250,252,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2738,2740,2744,2770,2772,2776,2786,2788,2792,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9528 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9528 2738 4
  · have he : independentCachedBranchMembers9528.erase 2738=independentCachedBranchMembers9526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9526
  · have he : independentCachedBranchMembers9528.filter (independentCachedEdge 2738)=independentCachedBranchMembers9527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9527
def independentCachedBranchMembers9529 : Finset ℕ := ([160,192,250,252,1690,1692,1702,1734,2744,2776,2786,2788,3256,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9529 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9529 4 (fun x => (if x<2744 then (if x<1690 then (if x<250 then (if x<192 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1702 then (if x<1692 then 2 else 3) else (if x<1734 then 2 else 3))) else (if x<3256 then (if x<2786 then (if x<2776 then 0 else 1) else (if x<2788 then 0 else 1)) else (if x<3298 then (if x<3288 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9530 : Finset ℕ := ([160,192,250,252,1686,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2738,2740,2744,2770,2772,2776,2786,2788,2792,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9530 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9530 1686 4
  · have he : independentCachedBranchMembers9530.erase 1686=independentCachedBranchMembers9528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9528
  · have he : independentCachedBranchMembers9530.filter (independentCachedEdge 1686)=independentCachedBranchMembers9529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9529
def independentCachedBranchMembers9531 : Finset ℕ := ([250,252,1690,1692,1706,1708,1738,1740,2702,2744,2776,2792,3214,3256,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9531 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9531 4 (fun x => (if x<2702 then (if x<1706 then (if x<1690 then (if x<252 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<1738 then (if x<1708 then 2 else 3) else (if x<1740 then 3 else 2))) else (if x<3214 then (if x<2776 then (if x<2744 then 2 else 0) else (if x<2792 then 1 else 2)) else (if x<3288 then (if x<3256 then 3 else 1) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9532 : Finset ℕ := ([160,192,246,250,252,1686,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2738,2740,2744,2770,2772,2776,2786,2788,2792,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9532 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9532 246 4
  · have he : independentCachedBranchMembers9532.erase 246=independentCachedBranchMembers9530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9530
  · have he : independentCachedBranchMembers9532.filter (independentCachedEdge 246)=independentCachedBranchMembers9531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9531
def independentCachedBranchMembers9533 : Finset ℕ := ([160,192,1702,1706,1708,1734,1738,1740,2702,2786,2788,2792,3214,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9533 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9533 4 (fun x => (if x<2702 then (if x<1708 then (if x<1702 then (if x<192 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<1738 then (if x<1734 then 3 else 1) else (if x<1740 then 3 else 2))) else (if x<3214 then (if x<2788 then (if x<2786 then 2 else 0) else (if x<2792 then 1 else 2)) else (if x<3300 then (if x<3298 then 3 else 1) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9534 : Finset ℕ := ([144,160,192,246,250,252,1686,1690,1692,1702,1706,1708,1734,1738,1740,1776,2702,2738,2740,2744,2770,2772,2776,2786,2788,2792,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9534 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9534 144 4
  · have he : independentCachedBranchMembers9534.erase 144=independentCachedBranchMembers9532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9532
  · have he : independentCachedBranchMembers9534.filter (independentCachedEdge 144)=independentCachedBranchMembers9533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9533
def independentCachedBranchMembers9535 : Finset ℕ := ([132,136,144,160,192,222,238,246,250,252,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9535 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9535 1678 5
  · have he : independentCachedBranchMembers9535.erase 1678=independentCachedBranchMembers9505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9505
  · have he : independentCachedBranchMembers9535.filter (independentCachedEdge 1678)=independentCachedBranchMembers9534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9534
end EntropyDesigns.QuadraticRefinement
