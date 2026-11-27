/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch80
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5376 : Finset ℕ := ([1642,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5376 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5376 1776 4
  · have he : independentCachedBranchMembers5376.erase 1776=independentCachedBranchMembers5374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5374
  · have he : independentCachedBranchMembers5376.filter (independentCachedEdge 1776)=independentCachedBranchMembers5375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5375
def independentCachedBranchMembers5377 : Finset ℕ := ([1714,1752,2606,2638,2674,2680,2740,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5377 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5377 4 (fun x => (if x<2680 then (if x<2606 then (if x<1752 then 0 else 0) else (if x<2638 then 1 else (if x<2674 then 2 else 1))) else (if x<2772 then (if x<2740 then 2 else 1) else (if x<2786 then 2 else (if x<2792 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5378 : Finset ℕ := ([1642,1690,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5378 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5378 1690 4
  · have he : independentCachedBranchMembers5378.erase 1690=independentCachedBranchMembers5376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5376
  · have he : independentCachedBranchMembers5378.filter (independentCachedEdge 1690)=independentCachedBranchMembers5377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5377
def independentCachedBranchMembers5379 : Finset ℕ := ([1708,1734,2606,2618,2668,2680,2716,2740,2762,2786] : List ℕ).toFinset
theorem independentCachedBranchBound5379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5379 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5379 4 (fun x => (if x<2680 then (if x<2606 then (if x<1734 then 0 else 0) else (if x<2618 then 1 else (if x<2668 then 2 else 2))) else (if x<2740 then (if x<2716 then 1 else 1) else (if x<2762 then 2 else (if x<2786 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5380 : Finset ℕ := ([1622,1642,1690,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5380 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5380 1622 4
  · have he : independentCachedBranchMembers5380.erase 1622=independentCachedBranchMembers5378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5378
  · have he : independentCachedBranchMembers5380.filter (independentCachedEdge 1622)=independentCachedBranchMembers5379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5379
def independentCachedBranchMembers5381 : Finset ℕ := ([1708,1734,2638,2650,2662,2674,2710,2730,2772,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5381 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5381 4 (fun x => (if x<2674 then (if x<2638 then (if x<1734 then 0 else 0) else (if x<2650 then 1 else (if x<2662 then 2 else 2))) else (if x<2730 then (if x<2710 then 1 else 1) else (if x<2772 then 1 else (if x<2792 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5382 : Finset ℕ := ([1596,1622,1642,1690,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5382 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5382 1596 4
  · have he : independentCachedBranchMembers5382.erase 1596=independentCachedBranchMembers5380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5380
  · have he : independentCachedBranchMembers5382.filter (independentCachedEdge 1596)=independentCachedBranchMembers5381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5381
def independentCachedBranchMembers5383 : Finset ℕ := ([1690,1708,1734,1776,2606,2638,2674,2680,2710,2716,2730,2762] : List ℕ).toFinset
theorem independentCachedBranchBound5383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5383 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5383 4 (fun x => (if x<2674 then (if x<1776 then (if x<1708 then 0 else (if x<1734 then 0 else 0)) else (if x<2606 then 0 else (if x<2638 then 1 else 2))) else (if x<2716 then (if x<2680 then 1 else (if x<2710 then 2 else 1)) else (if x<2730 then 2 else (if x<2762 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5384 : Finset ℕ := ([1596,1622,1642,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5384 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5384 1764 4
  · have he : independentCachedBranchMembers5384.erase 1764=independentCachedBranchMembers5382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5382
  · have he : independentCachedBranchMembers5384.filter (independentCachedEdge 1764)=independentCachedBranchMembers5383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5383
def independentCachedBranchMembers5385 : Finset ℕ := ([1690,1708,1734,1776,2618,2650,2662,2668,2740,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5385 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5385 4 (fun x => (if x<2662 then (if x<1776 then (if x<1708 then 0 else (if x<1734 then 0 else 0)) else (if x<2618 then 0 else (if x<2650 then 1 else 2))) else (if x<2772 then (if x<2668 then 1 else (if x<2740 then 2 else 1)) else (if x<2786 then 2 else (if x<2792 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5386 : Finset ℕ := ([1596,1622,1642,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5386 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5386 1678 4
  · have he : independentCachedBranchMembers5386.erase 1678=independentCachedBranchMembers5384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5384
  · have he : independentCachedBranchMembers5386.filter (independentCachedEdge 1678)=independentCachedBranchMembers5385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5385
def independentCachedBranchMembers5387 : Finset ℕ := ([1596,1622,1714,1752,2606,2618,2662,2674,2710,2740,2762,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5387 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5387 4 (fun x => (if x<2662 then (if x<1752 then (if x<1622 then 0 else (if x<1714 then 0 else 0)) else (if x<2606 then 0 else (if x<2618 then 1 else 2))) else (if x<2740 then (if x<2674 then 2 else (if x<2710 then 1 else 1)) else (if x<2762 then 2 else (if x<2792 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5388 : Finset ℕ := ([1596,1622,1628,1642,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5388 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5388 1628 4
  · have he : independentCachedBranchMembers5388.erase 1628=independentCachedBranchMembers5386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5386
  · have he : independentCachedBranchMembers5388.filter (independentCachedEdge 1628)=independentCachedBranchMembers5387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5387
def independentCachedBranchMembers5389 : Finset ℕ := ([1596,1622,1714,1752,2638,2650,2668,2680,2716,2730,2772,2786] : List ℕ).toFinset
theorem independentCachedBranchBound5389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5389 4 (fun x => (if x<2668 then (if x<1752 then (if x<1622 then 0 else (if x<1714 then 0 else 0)) else (if x<2638 then 0 else (if x<2650 then 1 else 2))) else (if x<2730 then (if x<2680 then 2 else (if x<2716 then 1 else 1)) else (if x<2772 then 1 else (if x<2786 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5390 : Finset ℕ := ([1590,1596,1622,1628,1642,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5390 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5390 1590 4
  · have he : independentCachedBranchMembers5390.erase 1590=independentCachedBranchMembers5388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5388
  · have he : independentCachedBranchMembers5390.filter (independentCachedEdge 1590)=independentCachedBranchMembers5389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5389
def independentCachedBranchMembers5391 : Finset ℕ := ([1590,1596,1622,1628,1678,1690,1764,1776,2606,2618,2638,2650,2710,2716,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5391 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5391 4 (fun x => (if x<2606 then (if x<1678 then (if x<1622 then (if x<1596 then 0 else 1) else (if x<1628 then 1 else 0)) else (if x<1764 then (if x<1690 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<2710 then (if x<2638 then (if x<2618 then 2 else 3) else (if x<2650 then 3 else 2)) else (if x<2786 then (if x<2716 then 2 else 3) else (if x<2792 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5392 : Finset ℕ := ([1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5392 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5392 1652 4
  · have he : independentCachedBranchMembers5392.erase 1652=independentCachedBranchMembers5390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5390
  · have he : independentCachedBranchMembers5392.filter (independentCachedEdge 1652)=independentCachedBranchMembers5391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5391
def independentCachedBranchMembers5393 : Finset ℕ := ([36,48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3072,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5393 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5393 3072 5
  · have he : independentCachedBranchMembers5393.erase 3072=independentCachedBranchMembers5373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5373
  · have he : independentCachedBranchMembers5393.filter (independentCachedEdge 3072)=independentCachedBranchMembers5392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5392
def independentCachedBranchMembers5394 : Finset ℕ := ([136,252,1596,1622,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2716,2730,2740,2792,3126,3164,3178,3188,3214,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5394 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5394 5 (fun x => (if x<2680 then (if x<1714 then (if x<1622 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1690 then 1 else (if x<1708 then 1 else 0))) else (if x<1776 then (if x<1734 then 2 else (if x<1752 then 2 else 0)) else (if x<2638 then (if x<2618 then 1 else 2) else (if x<2662 then 2 else 3)))) else (if x<3178 then (if x<2740 then (if x<2716 then 3 else (if x<2730 then 0 else 3)) else (if x<3126 then (if x<2792 then 3 else 0) else (if x<3164 then 4 else 4))) else (if x<3256 then (if x<3188 then 3 else (if x<3214 then 1 else 4)) else (if x<3282 then (if x<3276 then 0 else 0) else (if x<3300 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5395 : Finset ℕ := ([1596,1708,1752,1776,2680,2716,2740,2792,3126,3178,3214,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5395 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5395 4 (fun x => (if x<2740 then (if x<1776 then (if x<1708 then 0 else (if x<1752 then 1 else 0)) else (if x<2680 then 1 else (if x<2716 then 0 else 0))) else (if x<3178 then (if x<2792 then 1 else (if x<3126 then 1 else 2)) else (if x<3214 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5396 : Finset ℕ := ([68,136,252,1596,1622,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2716,2730,2740,2792,3126,3164,3178,3188,3214,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5396 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5396 68 4
  · have he : independentCachedBranchMembers5396.erase 68=independentCachedBranchMembers5394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5394
  · have he : independentCachedBranchMembers5396.filter (independentCachedEdge 68)=independentCachedBranchMembers5395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5395
def independentCachedBranchMembers5397 : Finset ℕ := ([1622,1690,1708,1752,2662,2716,2730,2792,3164,3178,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5397 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5397 4 (fun x => (if x<2730 then (if x<1752 then (if x<1690 then 0 else (if x<1708 then 0 else 1)) else (if x<2662 then 1 else (if x<2716 then 0 else 1))) else (if x<3178 then (if x<2792 then 0 else (if x<3164 then 1 else 2)) else (if x<3282 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5398 : Finset ℕ := ([48,68,136,252,1596,1622,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2716,2730,2740,2792,3126,3164,3178,3188,3214,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5398 48 4
  · have he : independentCachedBranchMembers5398.erase 48=independentCachedBranchMembers5396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5396
  · have he : independentCachedBranchMembers5398.filter (independentCachedEdge 48)=independentCachedBranchMembers5397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5397
def independentCachedBranchMembers5399 : Finset ℕ := ([48,68,136,252,1596,1622,1690,1776,2618,2638,2716,2792,3126,3164,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5399 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5399 4 (fun x => (if x<2618 then (if x<1596 then (if x<136 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3126 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5400 : Finset ℕ := ([48,68,136,252,1596,1622,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2716,2730,2740,2792,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5400 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5400 3238 4
  · have he : independentCachedBranchMembers5400.erase 3238=independentCachedBranchMembers5398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5398
  · have he : independentCachedBranchMembers5400.filter (independentCachedEdge 3238)=independentCachedBranchMembers5399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5399
def independentCachedBranchMembers5401 : Finset ℕ := ([48,68,136,252,1708,1714,1734,1752,2662,2680,2730,2740,3126,3164,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5401 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5401 4 (fun x => (if x<2662 then (if x<1708 then (if x<136 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3126 then (if x<2730 then (if x<2680 then 2 else 2) else (if x<2740 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5402 : Finset ℕ := ([48,68,136,252,1596,1622,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2716,2730,2740,2792,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5402 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5402 3102 4
  · have he : independentCachedBranchMembers5402.erase 3102=independentCachedBranchMembers5400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5400
  · have he : independentCachedBranchMembers5402.filter (independentCachedEdge 3102)=independentCachedBranchMembers5401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5401
def independentCachedBranchMembers5403 : Finset ℕ := ([1596,1622,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2716,2730,2740,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5403 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5403 4 (fun x => (if x<2618 then (if x<1714 then (if x<1690 then (if x<1622 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<2716 then (if x<2662 then (if x<2638 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<2740 then (if x<2730 then 2 else 3) else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5404 : Finset ℕ := ([48,68,136,252,1596,1622,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2716,2730,2740,2792,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5404 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5404 3072 4
  · have he : independentCachedBranchMembers5404.erase 3072=independentCachedBranchMembers5402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5402
  · have he : independentCachedBranchMembers5404.filter (independentCachedEdge 3072)=independentCachedBranchMembers5403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5403
def independentCachedBranchMembers5405 : Finset ℕ := ([36,48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3072,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5405 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5405 1746 5
  · have he : independentCachedBranchMembers5405.erase 1746=independentCachedBranchMembers5393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5393
  · have he : independentCachedBranchMembers5405.filter (independentCachedEdge 1746)=independentCachedBranchMembers5404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5404
def independentCachedBranchMembers5406 : Finset ℕ := ([130,246,1590,1628,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2710,2730,2740,2786,3132,3158,3178,3188,3226,3238,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5406 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5406 5 (fun x => (if x<2680 then (if x<1714 then (if x<1628 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1678 then 1 else (if x<1708 then 1 else 2))) else (if x<1764 then (if x<1734 then 0 else (if x<1752 then 0 else 2)) else (if x<2650 then (if x<2606 then 1 else 2) else (if x<2662 then 2 else 3)))) else (if x<3178 then (if x<2740 then (if x<2710 then 3 else (if x<2730 then 0 else 3)) else (if x<3132 then (if x<2786 then 3 else 0) else (if x<3158 then 4 else 4))) else (if x<3238 then (if x<3188 then 3 else (if x<3226 then 1 else 4)) else (if x<3282 then (if x<3276 then 0 else 1) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5407 : Finset ℕ := ([1590,1714,1734,1764,2662,2710,2740,2786,3132,3178,3226,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5407 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5407 4 (fun x => (if x<2740 then (if x<1764 then (if x<1714 then 0 else (if x<1734 then 1 else 0)) else (if x<2662 then 1 else (if x<2710 then 0 else 0))) else (if x<3178 then (if x<2786 then 1 else (if x<3132 then 1 else 2)) else (if x<3226 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
