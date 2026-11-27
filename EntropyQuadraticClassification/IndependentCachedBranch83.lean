/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch82
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5440 : Finset ℕ := ([68,246,1590,1622,1642,1652,1690,1734,1752,1764,2618,2650,2662,2710,2730,2740,2762,2772,2792,3126,3158,3178,3188,3226,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5440 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5440 5 (fun x => (if x<2710 then (if x<1690 then (if x<1622 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1642 then 0 else (if x<1652 then 1 else 2))) else (if x<1764 then (if x<1734 then 1 else (if x<1752 then 1 else 2)) else (if x<2650 then (if x<2618 then 0 else 1) else (if x<2662 then 3 else 0)))) else (if x<3158 then (if x<2762 then (if x<2730 then 1 else (if x<2740 then 3 else 4)) else (if x<2792 then (if x<2772 then 1 else 0) else (if x<3126 then 4 else 2))) else (if x<3226 then (if x<3178 then 3 else (if x<3188 then 3 else 0)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3300 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5441 : Finset ℕ := ([246,1642,1734,1764,2618,2650,2710,2740,2772,3178,3238,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5441 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5441 4 (fun x => (if x<2710 then (if x<1764 then (if x<1642 then 0 else (if x<1734 then 1 else 0)) else (if x<2618 then 1 else (if x<2650 then 1 else 2))) else (if x<3178 then (if x<2740 then 0 else (if x<2772 then 1 else 2)) else (if x<3238 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5442 : Finset ℕ := ([68,136,246,1590,1622,1642,1652,1690,1734,1752,1764,2618,2650,2662,2710,2730,2740,2762,2772,2792,3126,3158,3178,3188,3226,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5442 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5442 136 4
  · have he : independentCachedBranchMembers5442.erase 136=independentCachedBranchMembers5440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5440
  · have he : independentCachedBranchMembers5442.filter (independentCachedEdge 136)=independentCachedBranchMembers5441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5441
def independentCachedBranchMembers5443 : Finset ℕ := ([68,1622,1642,1734,2618,2710,2730,2772,2792,3158,3178,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5443 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5443 4 (fun x => (if x<2730 then (if x<1734 then (if x<1622 then 0 else (if x<1642 then 0 else 1)) else (if x<2618 then 1 else (if x<2710 then 1 else 1))) else (if x<3158 then (if x<2772 then 0 else (if x<2792 then 2 else 2)) else (if x<3178 then 2 else (if x<3256 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5444 : Finset ℕ := ([36,68,136,246,1590,1622,1642,1652,1690,1734,1752,1764,2618,2650,2662,2710,2730,2740,2762,2772,2792,3126,3158,3178,3188,3226,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5444 36 4
  · have he : independentCachedBranchMembers5444.erase 36=independentCachedBranchMembers5442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5442
  · have he : independentCachedBranchMembers5444.filter (independentCachedEdge 36)=independentCachedBranchMembers5443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5443
def independentCachedBranchMembers5445 : Finset ℕ := ([68,246,1622,1642,1652,1734,1752,1764,2618,2710,2730,2740,3126,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5445 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5445 4 (fun x => (if x<2618 then (if x<1652 then (if x<1622 then (if x<246 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3126 then (if x<2730 then (if x<2710 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3238 then (if x<3226 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5446 : Finset ℕ := ([36,68,136,246,1590,1622,1642,1652,1690,1734,1752,1764,2618,2650,2662,2710,2730,2740,2762,2772,2792,3126,3158,3178,3188,3226,3238,3256,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5446 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5446 3288 4
  · have he : independentCachedBranchMembers5446.erase 3288=independentCachedBranchMembers5444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5444
  · have he : independentCachedBranchMembers5446.filter (independentCachedEdge 3288)=independentCachedBranchMembers5445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5445
def independentCachedBranchMembers5447 : Finset ℕ := ([36,136,1590,1642,1652,1690,1734,1752,2650,2730,2740,2792,3158,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5447 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5447 4 (fun x => (if x<2650 then (if x<1652 then (if x<1590 then (if x<136 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1734 then (if x<1690 then 1 else 0) else (if x<1752 then 1 else 1))) else (if x<3158 then (if x<2740 then (if x<2730 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5448 : Finset ℕ := ([36,68,136,246,1590,1622,1642,1652,1690,1734,1752,1764,2618,2650,2662,2710,2730,2740,2762,2772,2792,3126,3158,3178,3188,3226,3238,3256,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5448 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5448 3270 4
  · have he : independentCachedBranchMembers5448.erase 3270=independentCachedBranchMembers5446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5446
  · have he : independentCachedBranchMembers5448.filter (independentCachedEdge 3270)=independentCachedBranchMembers5447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5447
def independentCachedBranchMembers5449 : Finset ℕ := ([36,68,136,246,1590,1622,1690,1764,2618,2650,2710,2792,3126,3158,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5449 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5449 4 (fun x => (if x<2618 then (if x<1590 then (if x<136 then (if x<68 then 0 else 1) else (if x<246 then 0 else 1)) else (if x<1690 then (if x<1622 then 0 else 1) else (if x<1764 then 0 else 1))) else (if x<3126 then (if x<2710 then (if x<2650 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3226 then (if x<3158 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5450 : Finset ℕ := ([36,68,136,246,1590,1622,1642,1652,1690,1734,1752,1764,2618,2650,2662,2680,2710,2730,2740,2762,2772,2792,3126,3158,3178,3188,3226,3238,3256,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5450 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5450 2680 4
  · have he : independentCachedBranchMembers5450.erase 2680=independentCachedBranchMembers5448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5448
  · have he : independentCachedBranchMembers5450.filter (independentCachedEdge 2680)=independentCachedBranchMembers5449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5449
def independentCachedBranchMembers5451 : Finset ℕ := ([12,18,36,48,68,80,130,136,192,222,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3072,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5451 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5451 12 5
  · have he : independentCachedBranchMembers5451.erase 12=independentCachedBranchMembers5439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5439
  · have he : independentCachedBranchMembers5451.filter (independentCachedEdge 12)=independentCachedBranchMembers5450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5450
def independentCachedBranchMembers5452 : Finset ℕ := ([130,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3126,3164,3178,3188,3214,3238,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5452 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5452 5 (fun x => (if x<2674 then (if x<1714 then (if x<1622 then (if x<246 then 0 else (if x<1596 then 0 else 1)) else (if x<1690 then 1 else (if x<1708 then 1 else 2))) else (if x<1776 then (if x<1734 then 0 else (if x<1752 then 0 else 2)) else (if x<2650 then (if x<2606 then 1 else 2) else (if x<2668 then 2 else 3)))) else (if x<3178 then (if x<2772 then (if x<2710 then 3 else (if x<2762 then 0 else 3)) else (if x<3126 then (if x<2786 then 3 else 0) else (if x<3164 then 4 else 4))) else (if x<3238 then (if x<3188 then 3 else (if x<3214 then 1 else 4)) else (if x<3282 then (if x<3256 then 0 else 1) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5453 : Finset ℕ := ([1596,1690,1714,1734,2668,2710,2762,2786,3126,3178,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5453 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5453 4 (fun x => (if x<2762 then (if x<1734 then (if x<1690 then 0 else (if x<1714 then 0 else 1)) else (if x<2668 then 1 else (if x<2710 then 0 else 1))) else (if x<3178 then (if x<2786 then 0 else (if x<3126 then 1 else 2)) else (if x<3256 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5454 : Finset ℕ := ([80,130,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3126,3164,3178,3188,3214,3238,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5454 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5454 80 4
  · have he : independentCachedBranchMembers5454.erase 80=independentCachedBranchMembers5452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5452
  · have he : independentCachedBranchMembers5454.filter (independentCachedEdge 80)=independentCachedBranchMembers5453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5453
def independentCachedBranchMembers5455 : Finset ℕ := ([1622,1714,1734,1776,2674,2710,2772,2786,3164,3178,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5455 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5455 4 (fun x => (if x<2772 then (if x<1776 then (if x<1714 then 0 else (if x<1734 then 0 else 1)) else (if x<2674 then 1 else (if x<2710 then 0 else 0))) else (if x<3178 then (if x<2786 then 1 else (if x<3164 then 1 else 2)) else (if x<3214 then 2 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5456 : Finset ℕ := ([36,80,130,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3126,3164,3178,3188,3214,3238,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5456 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5456 36 4
  · have he : independentCachedBranchMembers5456.erase 36=independentCachedBranchMembers5454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5454
  · have he : independentCachedBranchMembers5456.filter (independentCachedEdge 36)=independentCachedBranchMembers5455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5455
def independentCachedBranchMembers5457 : Finset ℕ := ([36,80,130,246,1596,1622,1690,1776,2606,2650,2710,2786,3126,3164,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5457 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5457 4 (fun x => (if x<2606 then (if x<1596 then (if x<130 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5458 : Finset ℕ := ([36,80,130,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5458 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5458 3276 4
  · have he : independentCachedBranchMembers5458.erase 3276=independentCachedBranchMembers5456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5456
  · have he : independentCachedBranchMembers5458.filter (independentCachedEdge 3276)=independentCachedBranchMembers5457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5457
def independentCachedBranchMembers5459 : Finset ℕ := ([36,80,130,246,1708,1714,1734,1752,2668,2674,2762,2772,3126,3164,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5459 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5459 4 (fun x => (if x<2668 then (if x<1708 then (if x<130 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3126 then (if x<2762 then (if x<2674 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5460 : Finset ℕ := ([36,80,130,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5460 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5460 3102 4
  · have he : independentCachedBranchMembers5460.erase 3102=independentCachedBranchMembers5458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5458
  · have he : independentCachedBranchMembers5460.filter (independentCachedEdge 3102)=independentCachedBranchMembers5459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5459
def independentCachedBranchMembers5461 : Finset ℕ := ([1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786] : List ℕ).toFinset
theorem independentCachedBranchBound5461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5461 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5461 4 (fun x => (if x<2606 then (if x<1714 then (if x<1690 then (if x<1622 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<2710 then (if x<2668 then (if x<2650 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2772 then (if x<2762 then 2 else 3) else (if x<2786 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5462 : Finset ℕ := ([36,80,130,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5462 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5462 3072 4
  · have he : independentCachedBranchMembers5462.erase 3072=independentCachedBranchMembers5460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5460
  · have he : independentCachedBranchMembers5462.filter (independentCachedEdge 3072)=independentCachedBranchMembers5461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5461
def independentCachedBranchMembers5463 : Finset ℕ := ([36,246,1596,1708,1714,1776,2606,2668,2674,2786,3126,3178,3188,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5463 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5463 4 (fun x => (if x<2674 then (if x<1714 then (if x<1596 then (if x<246 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3188 then (if x<3126 then (if x<2786 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5464 : Finset ℕ := ([36,80,130,222,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5464 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5464 222 4
  · have he : independentCachedBranchMembers5464.erase 222=independentCachedBranchMembers5462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5462
  · have he : independentCachedBranchMembers5464.filter (independentCachedEdge 222)=independentCachedBranchMembers5463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5463
def independentCachedBranchMembers5465 : Finset ℕ := ([80,130,1622,1690,1708,1714,2650,2668,2674,2710,3164,3178,3188,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5465 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5465 4 (fun x => (if x<2674 then (if x<1708 then (if x<1622 then (if x<130 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3188 then (if x<3164 then (if x<2710 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3214 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5466 : Finset ℕ := ([36,80,130,192,222,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5466 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5466 192 4
  · have he : independentCachedBranchMembers5466.erase 192=independentCachedBranchMembers5464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5464
  · have he : independentCachedBranchMembers5466.filter (independentCachedEdge 192)=independentCachedBranchMembers5465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5465
def independentCachedBranchMembers5467 : Finset ℕ := ([80,130,1596,1734,1752,1776,2606,2762,2772,2786,3164,3178,3188,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5467 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5467 4 (fun x => (if x<2772 then (if x<1752 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1734 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2762 then 1 else 1))) else (if x<3188 then (if x<3164 then (if x<2786 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3214 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5468 : Finset ℕ := ([18,36,80,130,192,222,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5468 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5468 18 4
  · have he : independentCachedBranchMembers5468.erase 18=independentCachedBranchMembers5466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5466
  · have he : independentCachedBranchMembers5468.filter (independentCachedEdge 18)=independentCachedBranchMembers5467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5467
def independentCachedBranchMembers5469 : Finset ℕ := ([36,246,1622,1690,1734,1752,2650,2710,2762,2772,3126,3178,3188,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5469 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5469 4 (fun x => (if x<2762 then (if x<1734 then (if x<1622 then (if x<246 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1752 then 2 else 2) else (if x<2710 then 1 else 1))) else (if x<3188 then (if x<3126 then (if x<2772 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5470 : Finset ℕ := ([12,18,36,80,130,192,222,246,1596,1622,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2710,2762,2772,2786,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5470 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5470 12 4
  · have he : independentCachedBranchMembers5470.erase 12=independentCachedBranchMembers5468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5468
  · have he : independentCachedBranchMembers5470.filter (independentCachedEdge 12)=independentCachedBranchMembers5469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5469
def independentCachedBranchMembers5471 : Finset ℕ := ([12,18,36,48,68,80,130,136,192,222,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3072,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5471 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5471 1720 5
  · have he : independentCachedBranchMembers5471.erase 1720=independentCachedBranchMembers5451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5451
  · have he : independentCachedBranchMembers5471.filter (independentCachedEdge 1720)=independentCachedBranchMembers5470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5470
end EntropyDesigns.QuadraticRefinement
