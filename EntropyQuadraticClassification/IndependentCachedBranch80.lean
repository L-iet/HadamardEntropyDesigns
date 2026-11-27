/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch79
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5344 : Finset ℕ := ([246,1590,1628,1642,1652,1690,1708,1714,1734,1776,2618,2638,2662,2680,2710,2762,2772,2786,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5344 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5344 246 4
  · have he : independentCachedBranchMembers5344.erase 246=independentCachedBranchMembers5342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5342
  · have he : independentCachedBranchMembers5344.filter (independentCachedEdge 246)=independentCachedBranchMembers5343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5343
def independentCachedBranchMembers5345 : Finset ℕ := ([1590,1642,1708,1776,2618,2638,2662,2772,3158,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5345 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5345 4 (fun x => (if x<2662 then (if x<1776 then (if x<1642 then 0 else (if x<1708 then 0 else 0)) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<3256 then (if x<2772 then 2 else (if x<3158 then 2 else 2)) else (if x<3276 then 1 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5346 : Finset ℕ := ([130,246,1590,1628,1642,1652,1690,1708,1714,1734,1776,2618,2638,2662,2680,2710,2762,2772,2786,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5346 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5346 130 4
  · have he : independentCachedBranchMembers5346.erase 130=independentCachedBranchMembers5344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5344
  · have he : independentCachedBranchMembers5346.filter (independentCachedEdge 130)=independentCachedBranchMembers5345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5345
def independentCachedBranchMembers5347 : Finset ℕ := ([1590,1642,1708,1776,2680,2710,2762,2786,3132,3214,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5347 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5347 4 (fun x => (if x<2762 then (if x<1776 then (if x<1642 then 0 else (if x<1708 then 0 else 0)) else (if x<2680 then 0 else (if x<2710 then 1 else 2))) else (if x<3214 then (if x<2786 then 1 else (if x<3132 then 2 else 1)) else (if x<3238 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5348 : Finset ℕ := ([68,130,246,1590,1628,1642,1652,1690,1708,1714,1734,1776,2618,2638,2662,2680,2710,2762,2772,2786,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5348 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5348 68 4
  · have he : independentCachedBranchMembers5348.erase 68=independentCachedBranchMembers5346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5346
  · have he : independentCachedBranchMembers5348.filter (independentCachedEdge 68)=independentCachedBranchMembers5347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5347
def independentCachedBranchMembers5349 : Finset ℕ := ([1628,1642,1690,1708,2662,2710,2772,2786,3158,3238,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5349 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5349 4 (fun x => (if x<2772 then (if x<1708 then (if x<1642 then 0 else (if x<1690 then 0 else 0)) else (if x<2662 then 0 else (if x<2710 then 1 else 1))) else (if x<3238 then (if x<2786 then 2 else (if x<3158 then 2 else 1)) else (if x<3282 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5350 : Finset ℕ := ([48,68,130,246,1590,1628,1642,1652,1690,1708,1714,1734,1776,2618,2638,2662,2680,2710,2762,2772,2786,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5350 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5350 48 4
  · have he : independentCachedBranchMembers5350.erase 48=independentCachedBranchMembers5348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5348
  · have he : independentCachedBranchMembers5350.filter (independentCachedEdge 48)=independentCachedBranchMembers5349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5349
def independentCachedBranchMembers5351 : Finset ℕ := ([48,68,130,246,1590,1628,1690,1776,2618,2638,2710,2786,3132,3158,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5351 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5351 4 (fun x => (if x<2618 then (if x<1590 then (if x<130 then (if x<68 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1690 then (if x<1628 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3132 then (if x<2710 then (if x<2638 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3214 then (if x<3158 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5352 : Finset ℕ := ([48,68,130,246,1590,1628,1642,1652,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2710,2762,2772,2786,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5352 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5352 1752 4
  · have he : independentCachedBranchMembers5352.erase 1752=independentCachedBranchMembers5350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5350
  · have he : independentCachedBranchMembers5352.filter (independentCachedEdge 1752)=independentCachedBranchMembers5351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5351
def independentCachedBranchMembers5353 : Finset ℕ := ([36,48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5353 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5353 3244 5
  · have he : independentCachedBranchMembers5353.erase 3244=independentCachedBranchMembers5339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5339
  · have he : independentCachedBranchMembers5353.filter (independentCachedEdge 3244)=independentCachedBranchMembers5352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5352
def independentCachedBranchMembers5354 : Finset ℕ := ([1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5354 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5354 5 (fun x => (if x<2740 then (if x<2662 then (if x<1714 then (if x<1708 then 0 else 0) else (if x<1734 then 0 else (if x<1752 then 0 else 0))) else (if x<2674 then (if x<2668 then 1 else 2) else (if x<2680 then 2 else (if x<2730 then 1 else 1)))) else (if x<3158 then (if x<2772 then (if x<2762 then 1 else 2) else (if x<3126 then 2 else (if x<3132 then 3 else 4))) else (if x<3226 then (if x<3164 then 4 else (if x<3214 then 3 else 3)) else (if x<3300 then 4 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5355 : Finset ℕ := ([1714,1734,2662,2674,2730,2762,3126,3158,3214,3226] : List ℕ).toFinset
theorem independentCachedBranchBound5355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5355 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5355 4 (fun x => (if x<2762 then (if x<2662 then (if x<1734 then 0 else 0) else (if x<2674 then 1 else (if x<2730 then 2 else 1))) else (if x<3158 then (if x<3126 then 2 else 2) else (if x<3214 then 1 else (if x<3226 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5356 : Finset ℕ := ([252,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5356 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5356 252 4
  · have he : independentCachedBranchMembers5356.erase 252=independentCachedBranchMembers5354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5354
  · have he : independentCachedBranchMembers5356.filter (independentCachedEdge 252)=independentCachedBranchMembers5355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5355
def independentCachedBranchMembers5357 : Finset ℕ := ([1714,1734,2668,2680,2740,2772,3132,3164,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5357 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5357 4 (fun x => (if x<2772 then (if x<2668 then (if x<1734 then 0 else 0) else (if x<2680 then 1 else (if x<2740 then 2 else 1))) else (if x<3164 then (if x<3132 then 2 else 1) else (if x<3300 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5358 : Finset ℕ := ([136,252,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5358 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5358 136 4
  · have he : independentCachedBranchMembers5358.erase 136=independentCachedBranchMembers5356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5356
  · have he : independentCachedBranchMembers5358.filter (independentCachedEdge 136)=independentCachedBranchMembers5357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5357
def independentCachedBranchMembers5359 : Finset ℕ := ([1708,1752,2674,2680,2740,2762,3126,3132,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5359 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5359 4 (fun x => (if x<2762 then (if x<2674 then (if x<1752 then 0 else 0) else (if x<2680 then 1 else (if x<2740 then 2 else 1))) else (if x<3132 then (if x<3126 then 2 else 1) else (if x<3214 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5360 : Finset ℕ := ([68,136,252,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5360 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5360 68 4
  · have he : independentCachedBranchMembers5360.erase 68=independentCachedBranchMembers5358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5358
  · have he : independentCachedBranchMembers5360.filter (independentCachedEdge 68)=independentCachedBranchMembers5359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5359
def independentCachedBranchMembers5361 : Finset ℕ := ([1708,1752,2662,2668,2730,2772,3158,3164,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5361 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5361 4 (fun x => (if x<2772 then (if x<2662 then (if x<1752 then 0 else 0) else (if x<2668 then 1 else (if x<2730 then 2 else 1))) else (if x<3164 then (if x<3158 then 2 else 1) else (if x<3226 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5362 : Finset ℕ := ([48,68,136,252,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5362 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5362 48 4
  · have he : independentCachedBranchMembers5362.erase 48=independentCachedBranchMembers5360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5360
  · have he : independentCachedBranchMembers5362.filter (independentCachedEdge 48)=independentCachedBranchMembers5361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5361
def independentCachedBranchMembers5363 : Finset ℕ := ([136,252,1708,1752,2668,2680,2730,2762,3132,3164,3214,3226] : List ℕ).toFinset
theorem independentCachedBranchBound5363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5363 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5363 4 (fun x => (if x<2730 then (if x<1752 then (if x<252 then 0 else (if x<1708 then 0 else 0)) else (if x<2668 then 0 else (if x<2680 then 1 else 2))) else (if x<3164 then (if x<2762 then 1 else (if x<3132 then 2 else 2)) else (if x<3214 then 1 else (if x<3226 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5364 : Finset ℕ := ([48,68,136,246,252,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5364 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5364 246 4
  · have he : independentCachedBranchMembers5364.erase 246=independentCachedBranchMembers5362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5362
  · have he : independentCachedBranchMembers5364.filter (independentCachedEdge 246)=independentCachedBranchMembers5363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5363
def independentCachedBranchMembers5365 : Finset ℕ := ([136,252,1708,1752,2662,2674,2740,2772,3126,3158,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5365 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5365 4 (fun x => (if x<2740 then (if x<1752 then (if x<252 then 0 else (if x<1708 then 0 else 0)) else (if x<2662 then 0 else (if x<2674 then 1 else 2))) else (if x<3158 then (if x<2772 then 1 else (if x<3126 then 2 else 1)) else (if x<3300 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5366 : Finset ℕ := ([48,68,130,136,246,252,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5366 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5366 130 4
  · have he : independentCachedBranchMembers5366.erase 130=independentCachedBranchMembers5364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5364
  · have he : independentCachedBranchMembers5366.filter (independentCachedEdge 130)=independentCachedBranchMembers5365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5365
def independentCachedBranchMembers5367 : Finset ℕ := ([48,68,1714,1734,2662,2668,2740,2762,3126,3132,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5367 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5367 4 (fun x => (if x<2740 then (if x<1734 then (if x<68 then 0 else (if x<1714 then 0 else 0)) else (if x<2662 then 0 else (if x<2668 then 1 else 2))) else (if x<3132 then (if x<2762 then 1 else (if x<3126 then 2 else 1)) else (if x<3226 then 2 else (if x<3300 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5368 : Finset ℕ := ([48,68,80,130,136,246,252,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5368 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5368 80 4
  · have he : independentCachedBranchMembers5368.erase 80=independentCachedBranchMembers5366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5366
  · have he : independentCachedBranchMembers5368.filter (independentCachedEdge 80)=independentCachedBranchMembers5367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5367
def independentCachedBranchMembers5369 : Finset ℕ := ([48,68,1714,1734,2674,2680,2730,2772,3158,3164,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5369 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5369 4 (fun x => (if x<2730 then (if x<1734 then (if x<68 then 0 else (if x<1714 then 0 else 0)) else (if x<2674 then 0 else (if x<2680 then 1 else 2))) else (if x<3164 then (if x<2772 then 1 else (if x<3158 then 2 else 1)) else (if x<3214 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5370 : Finset ℕ := ([36,48,68,80,130,136,246,252,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5370 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5370 36 4
  · have he : independentCachedBranchMembers5370.erase 36=independentCachedBranchMembers5368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5368
  · have he : independentCachedBranchMembers5370.filter (independentCachedEdge 36)=independentCachedBranchMembers5369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5369
def independentCachedBranchMembers5371 : Finset ℕ := ([36,48,68,80,130,136,246,252,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5371 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5371 4 (fun x => (if x<3126 then (if x<130 then (if x<68 then (if x<48 then 0 else 1) else (if x<80 then 1 else 0)) else (if x<246 then (if x<136 then 0 else 1) else (if x<252 then 0 else 1))) else (if x<3214 then (if x<3158 then (if x<3132 then 2 else 3) else (if x<3164 then 3 else 2)) else (if x<3300 then (if x<3226 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5372 : Finset ℕ := ([36,48,68,80,130,136,246,252,1642,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5372 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5372 1642 4
  · have he : independentCachedBranchMembers5372.erase 1642=independentCachedBranchMembers5370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5370
  · have he : independentCachedBranchMembers5372.filter (independentCachedEdge 1642)=independentCachedBranchMembers5371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5371
def independentCachedBranchMembers5373 : Finset ℕ := ([36,48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5373 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5373 3102 5
  · have he : independentCachedBranchMembers5373.erase 3102=independentCachedBranchMembers5353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5353
  · have he : independentCachedBranchMembers5373.filter (independentCachedEdge 3102)=independentCachedBranchMembers5372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5372
def independentCachedBranchMembers5374 : Finset ℕ := ([1642,1708,1714,1734,1752,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5374 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5374 5 (fun x => (if x<2668 then (if x<2606 then (if x<1714 then (if x<1708 then 0 else 0) else (if x<1734 then 0 else (if x<1752 then 0 else 0))) else (if x<2638 then (if x<2618 then 1 else 2) else (if x<2650 then 2 else (if x<2662 then 1 else 3)))) else (if x<2730 then (if x<2680 then (if x<2674 then 4 else 4) else (if x<2710 then 3 else (if x<2716 then 1 else 2))) else (if x<2772 then (if x<2740 then 3 else (if x<2762 then 3 else 4)) else (if x<2786 then 4 else (if x<2792 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5375 : Finset ℕ := ([1714,1752,2618,2650,2662,2668,2710,2716,2730,2762] : List ℕ).toFinset
theorem independentCachedBranchBound5375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5375 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5375 4 (fun x => (if x<2668 then (if x<2618 then (if x<1752 then 0 else 0) else (if x<2650 then 1 else (if x<2662 then 2 else 1))) else (if x<2716 then (if x<2710 then 2 else 1) else (if x<2730 then 2 else (if x<2762 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
