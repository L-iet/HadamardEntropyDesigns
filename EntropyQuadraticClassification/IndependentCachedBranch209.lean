/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch208
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9472 : Finset ℕ := ([160,192,238,250,252,1686,1706,1708,1720,1738,1740,1752,1762,1764,1776,2702,2714,2716,2726,2738,2740,2758,2770,2772,2792,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9472 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9472 238 4
  · have he : independentCachedBranchMembers9472.erase 238=independentCachedBranchMembers9470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9470
  · have he : independentCachedBranchMembers9472.filter (independentCachedEdge 238)=independentCachedBranchMembers9471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9471
def independentCachedBranchMembers9473 : Finset ℕ := ([160,192,1686,1762,1764,1776,2726,2738,2740,2758,2770,2772,3222,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9473 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9473 4 (fun x => (if x<2740 then (if x<1764 then (if x<1686 then (if x<192 then 0 else 1) else (if x<1762 then 2 else 0)) else (if x<2726 then (if x<1776 then 1 else 2) else (if x<2738 then 0 else 2))) else (if x<3222 then (if x<2770 then (if x<2758 then 3 else 1) else (if x<2772 then 3 else 2)) else (if x<3300 then (if x<3298 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9474 : Finset ℕ := ([136,160,192,238,250,252,1686,1706,1708,1720,1738,1740,1752,1762,1764,1776,2702,2714,2716,2726,2738,2740,2758,2770,2772,2792,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9474 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9474 136 4
  · have he : independentCachedBranchMembers9474.erase 136=independentCachedBranchMembers9472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9472
  · have he : independentCachedBranchMembers9474.filter (independentCachedEdge 136)=independentCachedBranchMembers9473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9473
def independentCachedBranchMembers9475 : Finset ℕ := ([132,136,144,160,192,222,238,246,250,252,1686,1690,1692,1702,1706,1708,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9475 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9475 2710 5
  · have he : independentCachedBranchMembers9475.erase 2710=independentCachedBranchMembers9459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9459
  · have he : independentCachedBranchMembers9475.filter (independentCachedEdge 2710)=independentCachedBranchMembers9474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9474
def independentCachedBranchMembers9476 : Finset ℕ := ([192,252,1690,1702,1716,1720,1740,1746,1762,1776,2716,2738,2758,2776,2788,2792,3214,3244,3250,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9476 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9476 5 (fun x => (if x<2758 then (if x<1740 then (if x<1702 then (if x<252 then 0 else (if x<1690 then 0 else 1)) else (if x<1716 then 1 else (if x<1720 then 2 else 3))) else (if x<1776 then (if x<1746 then 0 else (if x<1762 then 2 else 3)) else (if x<2716 then 0 else (if x<2738 then 3 else 1)))) else (if x<3250 then (if x<2792 then (if x<2776 then 3 else (if x<2788 then 0 else 0)) else (if x<3214 then 3 else (if x<3244 then 4 else 2))) else (if x<3288 then (if x<3274 then 2 else (if x<3284 then 2 else 0)) else (if x<3300 then 4 else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9477 : Finset ℕ := ([252,1702,1720,1776,2758,2776,2792,3244,3250,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9477 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9477 4 (fun x => (if x<2792 then (if x<1776 then (if x<1702 then 0 else (if x<1720 then 1 else 0)) else (if x<2758 then 1 else (if x<2776 then 2 else 0))) else (if x<3274 then (if x<3244 then 2 else (if x<3250 then 3 else 1)) else (if x<3284 then 2 else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9478 : Finset ℕ := ([192,252,1690,1702,1716,1720,1740,1746,1762,1776,2716,2738,2758,2762,2776,2788,2792,3214,3244,3250,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9478 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9478 2762 4
  · have he : independentCachedBranchMembers9478.erase 2762=independentCachedBranchMembers9476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9476
  · have he : independentCachedBranchMembers9478.filter (independentCachedEdge 2762)=independentCachedBranchMembers9477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9477
def independentCachedBranchMembers9479 : Finset ℕ := ([192,1690,1762,1776,2716,2788,2792,3244,3250,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9479 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9479 4 (fun x => (if x<2792 then (if x<1776 then (if x<1690 then 0 else (if x<1762 then 1 else 0)) else (if x<2716 then 1 else (if x<2788 then 2 else 0))) else (if x<3274 then (if x<3244 then 2 else (if x<3250 then 2 else 1)) else (if x<3284 then 3 else (if x<3288 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9480 : Finset ℕ := ([192,252,1690,1702,1716,1720,1740,1746,1762,1776,2716,2732,2738,2758,2762,2776,2788,2792,3214,3244,3250,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9480 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9480 2732 4
  · have he : independentCachedBranchMembers9480.erase 2732=independentCachedBranchMembers9478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9478
  · have he : independentCachedBranchMembers9480.filter (independentCachedEdge 2732)=independentCachedBranchMembers9479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9479
def independentCachedBranchMembers9481 : Finset ℕ := ([192,252,1690,1702,1720,1762,2716,2758,2776,2788,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9481 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9481 4 (fun x => (if x<2716 then (if x<1702 then (if x<252 then 0 else (if x<1690 then 0 else 1)) else (if x<1720 then 1 else (if x<1762 then 2 else 2))) else (if x<2788 then (if x<2758 then 2 else (if x<2776 then 2 else 0)) else (if x<3288 then 0 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9482 : Finset ℕ := ([192,252,1690,1702,1706,1716,1720,1740,1746,1762,1776,2716,2732,2738,2758,2762,2776,2788,2792,3214,3244,3250,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9482 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9482 1706 4
  · have he : independentCachedBranchMembers9482.erase 1706=independentCachedBranchMembers9480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9480
  · have he : independentCachedBranchMembers9482.filter (independentCachedEdge 1706)=independentCachedBranchMembers9481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9481
def independentCachedBranchMembers9483 : Finset ℕ := ([252,1690,1716,1720,1746,1776,2716,2738,2776,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9483 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9483 4 (fun x => (if x<2716 then (if x<1720 then (if x<1690 then 0 else (if x<1716 then 1 else 0)) else (if x<1746 then 2 else (if x<1776 then 2 else 1))) else (if x<3250 then (if x<2738 then 0 else (if x<2776 then 1 else 1)) else (if x<3284 then 2 else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9484 : Finset ℕ := ([192,238,252,1690,1702,1706,1716,1720,1740,1746,1762,1776,2716,2732,2738,2758,2762,2776,2788,2792,3214,3244,3250,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9484 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9484 238 4
  · have he : independentCachedBranchMembers9484.erase 238=independentCachedBranchMembers9482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9482
  · have he : independentCachedBranchMembers9484.filter (independentCachedEdge 238)=independentCachedBranchMembers9483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9483
def independentCachedBranchMembers9485 : Finset ℕ := ([192,1702,1716,1746,1762,1776,2738,2758,2788,3250,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9485 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9485 4 (fun x => (if x<2738 then (if x<1746 then (if x<1702 then 0 else (if x<1716 then 1 else 2)) else (if x<1762 then 0 else (if x<1776 then 2 else 1))) else (if x<3250 then (if x<2758 then 1 else (if x<2788 then 0 else 1)) else (if x<3284 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9486 : Finset ℕ := ([136,192,238,252,1690,1702,1706,1716,1720,1740,1746,1762,1776,2716,2732,2738,2758,2762,2776,2788,2792,3214,3244,3250,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9486 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9486 136 4
  · have he : independentCachedBranchMembers9486.erase 136=independentCachedBranchMembers9484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9484
  · have he : independentCachedBranchMembers9486.filter (independentCachedEdge 136)=independentCachedBranchMembers9485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9485
def independentCachedBranchMembers9487 : Finset ℕ := ([252,1690,1706,1716,1776,2716,2732,2738,2758,2776,2792,3214,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9487 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9487 4 (fun x => (if x<2738 then (if x<1716 then (if x<1690 then 0 else (if x<1706 then 1 else 2)) else (if x<2716 then (if x<1776 then 0 else 1) else (if x<2732 then 0 else 2))) else (if x<3214 then (if x<2776 then (if x<2758 then 1 else 3) else (if x<2792 then 1 else 3)) else (if x<3284 then (if x<3274 then 2 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9488 : Finset ℕ := ([1716,1776,2738,2758,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9488 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9488 3 (fun x => (if x<2758 then (if x<1776 then 0 else (if x<2738 then 1 else 0)) else (if x<3284 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9489 : Finset ℕ := ([136,252,1690,1706,1716,1776,2716,2732,2738,2758,2776,2792,3214,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9489 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9489 136 3
  · have he : independentCachedBranchMembers9489.erase 136=independentCachedBranchMembers9487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9487
  · have he : independentCachedBranchMembers9489.filter (independentCachedEdge 136)=independentCachedBranchMembers9488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9488
def independentCachedBranchMembers9490 : Finset ℕ := ([136,192,238,252,1690,1702,1706,1716,1720,1740,1746,1762,1776,2716,2732,2738,2758,2762,2776,2788,2792,3214,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9490 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9490 3270 4
  · have he : independentCachedBranchMembers9490.erase 3270=independentCachedBranchMembers9486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9486
  · have he : independentCachedBranchMembers9490.filter (independentCachedEdge 3270)=independentCachedBranchMembers9489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9489
def independentCachedBranchMembers9491 : Finset ℕ := ([238,1702,1706,1746,1776,2716,2738,2758,2762,2788,2792,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9491 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9491 4 (fun x => (if x<2758 then (if x<1746 then (if x<1702 then 0 else (if x<1706 then 0 else 1)) else (if x<2716 then (if x<1776 then 1 else 2) else (if x<2738 then 3 else 1))) else (if x<3214 then (if x<2788 then (if x<2762 then 0 else 1) else (if x<2792 then 2 else 3)) else (if x<3284 then (if x<3244 then 0 else 3) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9492 : Finset ℕ := ([1702,1706,2716,2738,3214,3244] : List ℕ).toFinset
theorem independentCachedBranchBound9492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9492 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9492 3 (fun x => (if x<2738 then (if x<1706 then 0 else (if x<2716 then 1 else 2)) else (if x<3214 then 0 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9493 : Finset ℕ := ([192,238,1702,1706,1746,1776,2716,2738,2758,2762,2788,2792,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9493 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9493 192 3
  · have he : independentCachedBranchMembers9493.erase 192=independentCachedBranchMembers9491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9491
  · have he : independentCachedBranchMembers9493.filter (independentCachedEdge 192)=independentCachedBranchMembers9492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9492
def independentCachedBranchMembers9494 : Finset ℕ := ([136,192,238,252,1690,1702,1706,1716,1720,1740,1746,1762,1776,2716,2732,2738,2758,2762,2776,2788,2792,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9494 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9494 3228 4
  · have he : independentCachedBranchMembers9494.erase 3228=independentCachedBranchMembers9490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9490
  · have he : independentCachedBranchMembers9494.filter (independentCachedEdge 3228)=independentCachedBranchMembers9493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9493
def independentCachedBranchMembers9495 : Finset ℕ := ([136,238,1690,1702,1720,1762,2716,2758,2776,2788,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9495 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9495 4 (fun x => (if x<2776 then (if x<1720 then (if x<1690 then (if x<238 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2716 then (if x<1762 then 2 else 2) else (if x<2758 then 2 else 2))) else (if x<3250 then (if x<3214 then (if x<2788 then 1 else 1) else (if x<3244 then 0 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9496 : Finset ℕ := ([136,192,238,252,1690,1702,1706,1716,1720,1740,1746,1762,1776,2716,2732,2738,2758,2762,2772,2776,2788,2792,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9496 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9496 2772 4
  · have he : independentCachedBranchMembers9496.erase 2772=independentCachedBranchMembers9494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9494
  · have he : independentCachedBranchMembers9496.filter (independentCachedEdge 2772)=independentCachedBranchMembers9495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9495
def independentCachedBranchMembers9497 : Finset ℕ := ([192,252,1716,1720,1746,1762,2716,2732,2758,2762,3214,3250,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9497 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9497 4 (fun x => (if x<2758 then (if x<1746 then (if x<1716 then (if x<252 then 0 else 0) else (if x<1720 then 1 else 2)) else (if x<2716 then (if x<1762 then 1 else 2) else (if x<2732 then 2 else 1))) else (if x<3284 then (if x<3214 then (if x<2762 then 2 else 1) else (if x<3250 then 3 else 3)) else (if x<3300 then (if x<3288 then 0 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9498 : Finset ℕ := ([136,192,238,252,1690,1702,1706,1716,1720,1740,1746,1762,1776,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9498 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9498 2702 4
  · have he : independentCachedBranchMembers9498.erase 2702=independentCachedBranchMembers9496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9496
  · have he : independentCachedBranchMembers9498.filter (independentCachedEdge 2702)=independentCachedBranchMembers9497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9497
def independentCachedBranchMembers9499 : Finset ℕ := ([136,192,238,252,1690,1702,1716,1746,2732,2762,2776,2788,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9499 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9499 4 (fun x => (if x<2732 then (if x<1690 then (if x<238 then (if x<192 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1716 then (if x<1702 then 2 else 2) else (if x<1746 then 3 else 3))) else (if x<3244 then (if x<2776 then (if x<2762 then 0 else 0) else (if x<2788 then 1 else 1)) else (if x<3288 then (if x<3274 then 3 else 3) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9500 : Finset ℕ := ([136,192,238,252,1686,1690,1702,1706,1716,1720,1740,1746,1762,1776,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9500 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9500 1686 4
  · have he : independentCachedBranchMembers9500.erase 1686=independentCachedBranchMembers9498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9498
  · have he : independentCachedBranchMembers9500.filter (independentCachedEdge 1686)=independentCachedBranchMembers9499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9499
def independentCachedBranchMembers9501 : Finset ℕ := ([238,252,1702,1706,1716,1720,1762,1776,2732,2738,2788,2792,3244,3250,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9501 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9501 4 (fun x => (if x<2732 then (if x<1716 then (if x<1702 then (if x<252 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<1762 then (if x<1720 then 1 else 3) else (if x<1776 then 3 else 2))) else (if x<3244 then (if x<2788 then (if x<2738 then 0 else 2) else (if x<2792 then 1 else 2)) else (if x<3300 then (if x<3250 then 1 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9502 : Finset ℕ := ([136,192,222,238,252,1686,1690,1702,1706,1716,1720,1740,1746,1762,1776,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9502 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9502 222 4
  · have he : independentCachedBranchMembers9502.erase 222=independentCachedBranchMembers9500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9500
  · have he : independentCachedBranchMembers9502.filter (independentCachedEdge 222)=independentCachedBranchMembers9501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9501
def independentCachedBranchMembers9503 : Finset ℕ := ([136,192,1690,1706,1720,1746,1762,1776,2738,2762,2776,2792,3250,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9503 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9503 4 (fun x => (if x<2738 then (if x<1720 then (if x<1690 then (if x<192 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<1762 then (if x<1746 then 3 else 1) else (if x<1776 then 3 else 2))) else (if x<3250 then (if x<2776 then (if x<2762 then 2 else 0) else (if x<2792 then 1 else 2)) else (if x<3288 then (if x<3274 then 3 else 1) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
