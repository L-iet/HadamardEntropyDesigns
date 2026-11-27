/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch83
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5472 : Finset ℕ := ([136,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3132,3158,3178,3188,3226,3238,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5472 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5472 5 (fun x => (if x<2674 then (if x<1714 then (if x<1628 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1678 then 1 else (if x<1708 then 1 else 0))) else (if x<1764 then (if x<1734 then 2 else (if x<1752 then 2 else 0)) else (if x<2638 then (if x<2618 then 1 else 2) else (if x<2668 then 2 else 3)))) else (if x<3178 then (if x<2772 then (if x<2716 then 3 else (if x<2762 then 0 else 3)) else (if x<3132 then (if x<2792 then 3 else 0) else (if x<3158 then 4 else 4))) else (if x<3238 then (if x<3188 then 3 else (if x<3226 then 1 else 4)) else (if x<3276 then (if x<3256 then 1 else 0) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5473 : Finset ℕ := ([1590,1678,1708,1752,2674,2716,2762,2792,3132,3178,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5473 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5473 4 (fun x => (if x<2762 then (if x<1752 then (if x<1678 then 0 else (if x<1708 then 0 else 1)) else (if x<2674 then 1 else (if x<2716 then 0 else 1))) else (if x<3178 then (if x<2792 then 0 else (if x<3132 then 1 else 2)) else (if x<3238 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5474 : Finset ℕ := ([68,136,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3132,3158,3178,3188,3226,3238,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5474 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5474 68 4
  · have he : independentCachedBranchMembers5474.erase 68=independentCachedBranchMembers5472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5472
  · have he : independentCachedBranchMembers5474.filter (independentCachedEdge 68)=independentCachedBranchMembers5473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5473
def independentCachedBranchMembers5475 : Finset ℕ := ([1628,1708,1752,1764,2668,2716,2772,2792,3158,3178,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound5475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5475 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5475 4 (fun x => (if x<2772 then (if x<1764 then (if x<1708 then 0 else (if x<1752 then 0 else 1)) else (if x<2668 then 1 else (if x<2716 then 0 else 0))) else (if x<3178 then (if x<2792 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5476 : Finset ℕ := ([48,68,136,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3132,3158,3178,3188,3226,3238,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5476 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5476 48 4
  · have he : independentCachedBranchMembers5476.erase 48=independentCachedBranchMembers5474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5474
  · have he : independentCachedBranchMembers5476.filter (independentCachedEdge 48)=independentCachedBranchMembers5475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5475
def independentCachedBranchMembers5477 : Finset ℕ := ([48,68,136,252,1590,1628,1678,1764,2618,2638,2716,2792,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5477 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5477 4 (fun x => (if x<2618 then (if x<1590 then (if x<136 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5478 : Finset ℕ := ([48,68,136,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5478 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5478 3282 4
  · have he : independentCachedBranchMembers5478.erase 3282=independentCachedBranchMembers5476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5476
  · have he : independentCachedBranchMembers5478.filter (independentCachedEdge 3282)=independentCachedBranchMembers5477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5477
def independentCachedBranchMembers5479 : Finset ℕ := ([48,68,136,252,1708,1714,1734,1752,2668,2674,2762,2772,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5479 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5479 4 (fun x => (if x<2668 then (if x<1708 then (if x<136 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3132 then (if x<2762 then (if x<2674 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5480 : Finset ℕ := ([48,68,136,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5480 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5480 3102 4
  · have he : independentCachedBranchMembers5480.erase 3102=independentCachedBranchMembers5478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5478
  · have he : independentCachedBranchMembers5480.filter (independentCachedEdge 3102)=independentCachedBranchMembers5479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5479
def independentCachedBranchMembers5481 : Finset ℕ := ([1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5481 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5481 4 (fun x => (if x<2618 then (if x<1714 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<2716 then (if x<2668 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2772 then (if x<2762 then 2 else 3) else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5482 : Finset ℕ := ([48,68,136,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5482 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5482 3072 4
  · have he : independentCachedBranchMembers5482.erase 3072=independentCachedBranchMembers5480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5480
  · have he : independentCachedBranchMembers5482.filter (independentCachedEdge 3072)=independentCachedBranchMembers5481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5481
def independentCachedBranchMembers5483 : Finset ℕ := ([48,252,1590,1708,1714,1764,2618,2668,2674,2792,3132,3178,3188,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5483 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5483 4 (fun x => (if x<2674 then (if x<1714 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1708 then 1 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2668 then 2 else 2))) else (if x<3188 then (if x<3132 then (if x<2792 then 1 else 1) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5484 : Finset ℕ := ([48,68,136,222,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5484 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5484 222 4
  · have he : independentCachedBranchMembers5484.erase 222=independentCachedBranchMembers5482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5482
  · have he : independentCachedBranchMembers5484.filter (independentCachedEdge 222)=independentCachedBranchMembers5483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5483
def independentCachedBranchMembers5485 : Finset ℕ := ([68,136,1628,1678,1708,1714,2638,2668,2674,2716,3158,3178,3188,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5485 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5485 4 (fun x => (if x<2674 then (if x<1708 then (if x<1628 then (if x<136 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3188 then (if x<3158 then (if x<2716 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3226 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5486 : Finset ℕ := ([48,68,136,192,222,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5486 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5486 192 4
  · have he : independentCachedBranchMembers5486.erase 192=independentCachedBranchMembers5484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5484
  · have he : independentCachedBranchMembers5486.filter (independentCachedEdge 192)=independentCachedBranchMembers5485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5485
def independentCachedBranchMembers5487 : Finset ℕ := ([48,252,1628,1678,1734,1752,2638,2716,2762,2772,3132,3178,3188,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5487 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5487 4 (fun x => (if x<2762 then (if x<1734 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1752 then 2 else 2) else (if x<2716 then 1 else 1))) else (if x<3188 then (if x<3132 then (if x<2772 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5488 : Finset ℕ := ([18,48,68,136,192,222,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5488 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5488 18 4
  · have he : independentCachedBranchMembers5488.erase 18=independentCachedBranchMembers5486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5486
  · have he : independentCachedBranchMembers5488.filter (independentCachedEdge 18)=independentCachedBranchMembers5487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5487
def independentCachedBranchMembers5489 : Finset ℕ := ([68,136,1590,1734,1752,1764,2618,2762,2772,2792,3158,3178,3188,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5489 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5489 4 (fun x => (if x<2772 then (if x<1752 then (if x<1590 then (if x<136 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2762 then 1 else 1))) else (if x<3188 then (if x<3158 then (if x<2792 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3226 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5490 : Finset ℕ := ([12,18,48,68,136,192,222,252,1590,1628,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2716,2762,2772,2792,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5490 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5490 12 4
  · have he : independentCachedBranchMembers5490.erase 12=independentCachedBranchMembers5488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5488
  · have he : independentCachedBranchMembers5490.filter (independentCachedEdge 12)=independentCachedBranchMembers5489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5489
def independentCachedBranchMembers5491 : Finset ℕ := ([12,18,36,48,68,80,130,136,192,222,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3072,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5491 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5491 1702 5
  · have he : independentCachedBranchMembers5491.erase 1702=independentCachedBranchMembers5471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5471
  · have he : independentCachedBranchMembers5491.filter (independentCachedEdge 1702)=independentCachedBranchMembers5490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5490
def independentCachedBranchMembers5492 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5492 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5492 2666 6
  · have he : independentCachedBranchMembers5492.erase 2666=independentCachedBranchMembers5230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5230
  · have he : independentCachedBranchMembers5492.filter (independentCachedEdge 2666)=independentCachedBranchMembers5491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5491
def independentCachedBranchMembers5493 : Finset ℕ := ([1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3192,3242,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5493 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5493 6 (fun x => (if x<2650 then (if x<1738 then (if x<1708 then (if x<1652 then (if x<1650 then 0 else 0) else (if x<1702 then 1 else 0)) else (if x<1720 then (if x<1714 then 1 else 1) else (if x<1734 then 0 else 1))) else (if x<2614 then (if x<1752 then (if x<1748 then 0 else 0) else (if x<2606 then 1 else 2)) else (if x<2620 then (if x<2618 then 3 else 4) else (if x<2638 then 5 else (if x<2646 then 3 else 2))))) else (if x<2792 then (if x<2714 then (if x<2702 then (if x<2652 then 5 else 4) else (if x<2710 then 4 else 5)) else (if x<2786 then (if x<2716 then 2 else 3) else (if x<2788 then 2 else 3))) else (if x<3192 then (if x<3102 then (if x<2800 then 4 else 5) else (if x<3174 then 2 else 2)) else (if x<3252 then (if x<3242 then 4 else 2) else (if x<3276 then 3 else (if x<3282 then 3 else 2)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5494 : Finset ℕ := ([1644,1650,1738,1748,2614,2620,2646,2652,2702,2714,2788,2800,3102,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5494 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5494 5 (fun x => (if x<2652 then (if x<1748 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<2620 then (if x<2614 then 0 else 1) else (if x<2646 then 2 else 2))) else (if x<2800 then (if x<2714 then (if x<2702 then 1 else 1) else (if x<2788 then 2 else 1)) else (if x<3276 then (if x<3102 then 2 else 1) else (if x<3282 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5495 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3192,3242,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5495 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5495 1642 5
  · have he : independentCachedBranchMembers5495.erase 1642=independentCachedBranchMembers5493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5493
  · have he : independentCachedBranchMembers5495.filter (independentCachedEdge 1642)=independentCachedBranchMembers5494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5494
def independentCachedBranchMembers5496 : Finset ℕ := ([1644,1650,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2702,2714,2786,2792,3242,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5496 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5496 5 (fun x => (if x<2638 then (if x<1720 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1708 then 0 else (if x<1714 then 1 else 1))) else (if x<1748 then (if x<1738 then 0 else 0) else (if x<2614 then 0 else (if x<2620 then 2 else 3)))) else (if x<2792 then (if x<2702 then (if x<2650 then 2 else 3) else (if x<2714 then 3 else (if x<2786 then 2 else 2))) else (if x<3252 then (if x<3242 then 3 else 1) else (if x<3276 then 1 else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5497 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3192,3242,3252,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5497 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5497 3284 5
  · have he : independentCachedBranchMembers5497.erase 3284=independentCachedBranchMembers5495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5495
  · have he : independentCachedBranchMembers5497.filter (independentCachedEdge 3284)=independentCachedBranchMembers5496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5496
def independentCachedBranchMembers5498 : Finset ℕ := ([1644,1650,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2710,2716,2788,2800,3242,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5498 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5498 5 (fun x => (if x<2646 then (if x<1720 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1708 then 0 else (if x<1714 then 1 else 1))) else (if x<1748 then (if x<1738 then 0 else 0) else (if x<2606 then 0 else (if x<2618 then 2 else 3)))) else (if x<2800 then (if x<2710 then (if x<2652 then 2 else 3) else (if x<2716 then 3 else (if x<2788 then 2 else 2))) else (if x<3252 then (if x<3242 then 3 else 1) else (if x<3276 then 1 else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5499 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3192,3242,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5499 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5499 3274 5
  · have he : independentCachedBranchMembers5499.erase 3274=independentCachedBranchMembers5497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5497
  · have he : independentCachedBranchMembers5499.filter (independentCachedEdge 3274)=independentCachedBranchMembers5498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5498
def independentCachedBranchMembers5500 : Finset ℕ := ([1642,1652,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2702,2716,2788,2792,3242,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5500 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5500 5 (fun x => (if x<2646 then (if x<1738 then (if x<1708 then (if x<1652 then 0 else 0) else (if x<1714 then 0 else (if x<1734 then 0 else 0))) else (if x<1752 then (if x<1748 then 1 else 1) else (if x<2606 then 0 else (if x<2620 then 2 else 3)))) else (if x<2792 then (if x<2702 then (if x<2650 then 2 else 3) else (if x<2716 then 3 else (if x<2788 then 2 else 2))) else (if x<3252 then (if x<3242 then 3 else 1) else (if x<3276 then 1 else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5501 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3192,3242,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5501 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5501 3250 5
  · have he : independentCachedBranchMembers5501.erase 3250=independentCachedBranchMembers5499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5499
  · have he : independentCachedBranchMembers5501.filter (independentCachedEdge 3250)=independentCachedBranchMembers5500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5500
def independentCachedBranchMembers5502 : Finset ℕ := ([1642,1652,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2710,2714,2786,2800,3242,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5502 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5502 5 (fun x => (if x<2638 then (if x<1738 then (if x<1708 then (if x<1652 then 0 else 0) else (if x<1714 then 0 else (if x<1734 then 0 else 0))) else (if x<1752 then (if x<1748 then 1 else 1) else (if x<2614 then 0 else (if x<2618 then 2 else 3)))) else (if x<2800 then (if x<2710 then (if x<2652 then 2 else 3) else (if x<2714 then 3 else (if x<2786 then 2 else 2))) else (if x<3252 then (if x<3242 then 3 else 1) else (if x<3276 then 1 else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5503 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5503 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5503 3244 5
  · have he : independentCachedBranchMembers5503.erase 3244=independentCachedBranchMembers5501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5501
  · have he : independentCachedBranchMembers5503.filter (independentCachedEdge 3244)=independentCachedBranchMembers5502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5502
end EntropyDesigns.QuadraticRefinement
