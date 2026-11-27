/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch81
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5408 : Finset ℕ := ([80,130,246,1590,1628,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2710,2730,2740,2786,3132,3158,3178,3188,3226,3238,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5408 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5408 80 4
  · have he : independentCachedBranchMembers5408.erase 80=independentCachedBranchMembers5406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5406
  · have he : independentCachedBranchMembers5408.filter (independentCachedEdge 80)=independentCachedBranchMembers5407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5407
def independentCachedBranchMembers5409 : Finset ℕ := ([1628,1678,1714,1734,2680,2710,2730,2786,3158,3178,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5409 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5409 4 (fun x => (if x<2730 then (if x<1734 then (if x<1678 then 0 else (if x<1714 then 0 else 1)) else (if x<2680 then 1 else (if x<2710 then 0 else 1))) else (if x<3178 then (if x<2786 then 0 else (if x<3158 then 1 else 2)) else (if x<3276 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5410 : Finset ℕ := ([36,80,130,246,1590,1628,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2710,2730,2740,2786,3132,3158,3178,3188,3226,3238,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5410 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5410 36 4
  · have he : independentCachedBranchMembers5410.erase 36=independentCachedBranchMembers5408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5408
  · have he : independentCachedBranchMembers5410.filter (independentCachedEdge 36)=independentCachedBranchMembers5409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5409
def independentCachedBranchMembers5411 : Finset ℕ := ([36,80,130,246,1590,1628,1678,1764,2606,2650,2710,2786,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5411 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5411 4 (fun x => (if x<2606 then (if x<1590 then (if x<130 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3132 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5412 : Finset ℕ := ([36,80,130,246,1590,1628,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2710,2730,2740,2786,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5412 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5412 3256 4
  · have he : independentCachedBranchMembers5412.erase 3256=independentCachedBranchMembers5410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5410
  · have he : independentCachedBranchMembers5412.filter (independentCachedEdge 3256)=independentCachedBranchMembers5411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5411
def independentCachedBranchMembers5413 : Finset ℕ := ([36,80,130,246,1708,1714,1734,1752,2662,2680,2730,2740,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5413 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5413 4 (fun x => (if x<2662 then (if x<1708 then (if x<130 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3132 then (if x<2730 then (if x<2680 then 2 else 2) else (if x<2740 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5414 : Finset ℕ := ([36,80,130,246,1590,1628,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2710,2730,2740,2786,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5414 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5414 3102 4
  · have he : independentCachedBranchMembers5414.erase 3102=independentCachedBranchMembers5412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5412
  · have he : independentCachedBranchMembers5414.filter (independentCachedEdge 3102)=independentCachedBranchMembers5413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5413
def independentCachedBranchMembers5415 : Finset ℕ := ([1590,1628,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2710,2730,2740,2786] : List ℕ).toFinset
theorem independentCachedBranchBound5415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5415 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5415 4 (fun x => (if x<2606 then (if x<1714 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<2710 then (if x<2662 then (if x<2650 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<2740 then (if x<2730 then 2 else 3) else (if x<2786 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5416 : Finset ℕ := ([36,80,130,246,1590,1628,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2710,2730,2740,2786,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5416 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5416 3072 4
  · have he : independentCachedBranchMembers5416.erase 3072=independentCachedBranchMembers5414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5414
  · have he : independentCachedBranchMembers5416.filter (independentCachedEdge 3072)=independentCachedBranchMembers5415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5415
def independentCachedBranchMembers5417 : Finset ℕ := ([36,48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3072,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5417 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5417 1740 5
  · have he : independentCachedBranchMembers5417.erase 1740=independentCachedBranchMembers5405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5405
  · have he : independentCachedBranchMembers5417.filter (independentCachedEdge 1740)=independentCachedBranchMembers5416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5416
def independentCachedBranchMembers5418 : Finset ℕ := ([36,48,246,252,1590,1596,1642,1652,1708,1714,1764,1776,2606,2618,2662,2668,2674,2680,2740,2786,2792,3126,3132,3178,3188,3238,3256,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5418 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5418 5 (fun x => (if x<2662 then (if x<1652 then (if x<252 then (if x<48 then 0 else (if x<246 then 1 else 0)) else (if x<1596 then (if x<1590 then 1 else 0) else (if x<1642 then 1 else 2))) else (if x<1764 then (if x<1708 then 2 else (if x<1714 then 2 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2618 then 3 else 4)))) else (if x<3126 then (if x<2680 then (if x<2668 then 0 else (if x<2674 then 2 else 2)) else (if x<2786 then (if x<2740 then 1 else 0) else (if x<2792 then 3 else 4))) else (if x<3238 then (if x<3178 then (if x<3132 then 4 else 3) else (if x<3188 then 3 else 0)) else (if x<3300 then (if x<3256 then 0 else 1) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5419 : Finset ℕ := ([36,252,1596,1642,1652,1708,1714,1764,2606,2662,2680,2792,3126,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5419 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5419 4 (fun x => (if x<2606 then (if x<1652 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1714 then (if x<1708 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3126 then (if x<2680 then (if x<2662 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3256 then (if x<3238 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5420 : Finset ℕ := ([36,48,246,252,1590,1596,1642,1652,1708,1714,1764,1776,2606,2618,2662,2668,2674,2680,2740,2786,2792,3126,3132,3178,3188,3238,3250,3256,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5420 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5420 3250 4
  · have he : independentCachedBranchMembers5420.erase 3250=independentCachedBranchMembers5418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5418
  · have he : independentCachedBranchMembers5420.filter (independentCachedEdge 3250)=independentCachedBranchMembers5419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5419
def independentCachedBranchMembers5421 : Finset ℕ := ([48,246,1590,1642,1652,1708,1714,1776,2618,2662,2680,2786,3132,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5421 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5421 4 (fun x => (if x<2618 then (if x<1652 then (if x<1590 then (if x<246 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1714 then (if x<1708 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3132 then (if x<2680 then (if x<2662 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5422 : Finset ℕ := ([36,48,246,252,1590,1596,1642,1652,1708,1714,1764,1776,2606,2618,2662,2668,2674,2680,2740,2786,2792,3126,3132,3178,3188,3238,3244,3250,3256,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5422 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5422 3244 4
  · have he : independentCachedBranchMembers5422.erase 3244=independentCachedBranchMembers5420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5420
  · have he : independentCachedBranchMembers5422.filter (independentCachedEdge 3244)=independentCachedBranchMembers5421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5421
def independentCachedBranchMembers5423 : Finset ℕ := ([36,48,246,252,1590,1596,1764,1776,2606,2618,2786,2792,3126,3132,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5423 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5423 4 (fun x => (if x<2606 then (if x<1590 then (if x<246 then (if x<48 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1764 then (if x<1596 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3126 then (if x<2786 then (if x<2618 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3300 then (if x<3132 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5424 : Finset ℕ := ([36,48,246,252,1590,1596,1642,1652,1708,1714,1764,1776,2606,2618,2662,2668,2674,2680,2730,2740,2786,2792,3126,3132,3178,3188,3238,3244,3250,3256,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5424 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5424 2730 4
  · have he : independentCachedBranchMembers5424.erase 2730=independentCachedBranchMembers5422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5422
  · have he : independentCachedBranchMembers5424.filter (independentCachedEdge 2730)=independentCachedBranchMembers5423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5423
def independentCachedBranchMembers5425 : Finset ℕ := ([36,48,68,80,130,136,222,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3072,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5425 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5425 222 5
  · have he : independentCachedBranchMembers5425.erase 222=independentCachedBranchMembers5417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5417
  · have he : independentCachedBranchMembers5425.filter (independentCachedEdge 222)=independentCachedBranchMembers5424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5424
def independentCachedBranchMembers5426 : Finset ℕ := ([68,80,130,136,1622,1628,1642,1652,1678,1690,1708,1714,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5426 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5426 5 (fun x => (if x<2674 then (if x<1678 then (if x<1622 then (if x<130 then (if x<80 then 0 else 1) else (if x<136 then 0 else 1)) else (if x<1642 then (if x<1628 then 1 else 0) else (if x<1652 then 2 else 2))) else (if x<2638 then (if x<1708 then (if x<1690 then 1 else 0) else (if x<1714 then 2 else 2)) else (if x<2662 then (if x<2650 then 3 else 4) else (if x<2668 then 4 else 0)))) else (if x<3178 then (if x<2730 then (if x<2710 then (if x<2680 then 1 else 3) else (if x<2716 then 4 else 3)) else (if x<3158 then (if x<2740 then 0 else 2) else (if x<3164 then 4 else 3))) else (if x<3238 then (if x<3214 then (if x<3188 then 3 else 0) else (if x<3226 then 3 else 4)) else (if x<3250 then (if x<3244 then 4 else 1) else (if x<3256 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5427 : Finset ℕ := ([36,48,68,80,130,136,192,222,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3072,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5427 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5427 192 5
  · have he : independentCachedBranchMembers5427.erase 192=independentCachedBranchMembers5425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5425
  · have he : independentCachedBranchMembers5427.filter (independentCachedEdge 192)=independentCachedBranchMembers5426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5426
def independentCachedBranchMembers5428 : Finset ℕ := ([80,252,1596,1628,1642,1652,1678,1734,1752,1776,2606,2638,2680,2716,2730,2740,2762,2772,2786,3132,3164,3178,3188,3214,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5428 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5428 5 (fun x => (if x<2716 then (if x<1678 then (if x<1628 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1642 then 0 else (if x<1652 then 1 else 2))) else (if x<1776 then (if x<1734 then 1 else (if x<1752 then 2 else 1)) else (if x<2638 then (if x<2606 then 0 else 1) else (if x<2680 then 3 else 0)))) else (if x<3164 then (if x<2762 then (if x<2730 then 1 else (if x<2740 then 3 else 4)) else (if x<2786 then (if x<2772 then 1 else 0) else (if x<3132 then 4 else 2))) else (if x<3214 then (if x<3178 then 3 else (if x<3188 then 3 else 0)) else (if x<3256 then (if x<3238 then 2 else 4) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5429 : Finset ℕ := ([252,1642,1752,1776,2606,2638,2716,2740,2772,3178,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5429 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5429 4 (fun x => (if x<2716 then (if x<1776 then (if x<1642 then 0 else (if x<1752 then 1 else 0)) else (if x<2606 then 1 else (if x<2638 then 1 else 2))) else (if x<3178 then (if x<2740 then 0 else (if x<2772 then 1 else 2)) else (if x<3256 then 2 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5430 : Finset ℕ := ([80,130,252,1596,1628,1642,1652,1678,1734,1752,1776,2606,2638,2680,2716,2730,2740,2762,2772,2786,3132,3164,3178,3188,3214,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5430 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5430 130 4
  · have he : independentCachedBranchMembers5430.erase 130=independentCachedBranchMembers5428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5428
  · have he : independentCachedBranchMembers5430.filter (independentCachedEdge 130)=independentCachedBranchMembers5429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5429
def independentCachedBranchMembers5431 : Finset ℕ := ([80,1628,1642,1752,2606,2716,2730,2772,2786,3164,3178,3238] : List ℕ).toFinset
theorem independentCachedBranchBound5431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5431 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5431 4 (fun x => (if x<2730 then (if x<1752 then (if x<1628 then 0 else (if x<1642 then 0 else 1)) else (if x<2606 then 1 else (if x<2716 then 1 else 1))) else (if x<3164 then (if x<2772 then 0 else (if x<2786 then 2 else 2)) else (if x<3178 then 2 else (if x<3238 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5432 : Finset ℕ := ([48,80,130,252,1596,1628,1642,1652,1678,1734,1752,1776,2606,2638,2680,2716,2730,2740,2762,2772,2786,3132,3164,3178,3188,3214,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5432 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5432 48 4
  · have he : independentCachedBranchMembers5432.erase 48=independentCachedBranchMembers5430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5430
  · have he : independentCachedBranchMembers5432.filter (independentCachedEdge 48)=independentCachedBranchMembers5431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5431
def independentCachedBranchMembers5433 : Finset ℕ := ([48,130,1596,1642,1652,1678,1734,1752,2638,2730,2740,2786,3164,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5433 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5433 4 (fun x => (if x<2638 then (if x<1652 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1734 then (if x<1678 then 1 else 0) else (if x<1752 then 1 else 1))) else (if x<3164 then (if x<2740 then (if x<2730 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5434 : Finset ℕ := ([48,80,130,252,1596,1628,1642,1652,1678,1734,1752,1776,2606,2638,2680,2716,2730,2740,2762,2772,2786,3132,3164,3178,3188,3214,3238,3256,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5434 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5434 3288 4
  · have he : independentCachedBranchMembers5434.erase 3288=independentCachedBranchMembers5432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5432
  · have he : independentCachedBranchMembers5434.filter (independentCachedEdge 3288)=independentCachedBranchMembers5433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5433
def independentCachedBranchMembers5435 : Finset ℕ := ([80,252,1628,1642,1652,1734,1752,1776,2606,2716,2730,2740,3132,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5435 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5435 4 (fun x => (if x<2606 then (if x<1652 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3132 then (if x<2730 then (if x<2716 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3238 then (if x<3214 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5436 : Finset ℕ := ([48,80,130,252,1596,1628,1642,1652,1678,1734,1752,1776,2606,2638,2680,2716,2730,2740,2762,2772,2786,3132,3164,3178,3188,3214,3238,3256,3270,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5436 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5436 3270 4
  · have he : independentCachedBranchMembers5436.erase 3270=independentCachedBranchMembers5434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5434
  · have he : independentCachedBranchMembers5436.filter (independentCachedEdge 3270)=independentCachedBranchMembers5435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5435
def independentCachedBranchMembers5437 : Finset ℕ := ([48,80,130,252,1596,1628,1678,1776,2606,2638,2716,2786,3132,3164,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5437 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5437 4 (fun x => (if x<2606 then (if x<1596 then (if x<130 then (if x<80 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1678 then (if x<1628 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3132 then (if x<2716 then (if x<2638 then 2 else 3) else (if x<2786 then 2 else 3)) else (if x<3214 then (if x<3164 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5438 : Finset ℕ := ([48,80,130,252,1596,1628,1642,1652,1678,1734,1752,1776,2606,2638,2662,2680,2716,2730,2740,2762,2772,2786,3132,3164,3178,3188,3214,3238,3256,3270,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5438 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5438 2662 4
  · have he : independentCachedBranchMembers5438.erase 2662=independentCachedBranchMembers5436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5436
  · have he : independentCachedBranchMembers5438.filter (independentCachedEdge 2662)=independentCachedBranchMembers5437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5437
def independentCachedBranchMembers5439 : Finset ℕ := ([18,36,48,68,80,130,136,192,222,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3072,3102,3126,3132,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5439 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5439 18 5
  · have he : independentCachedBranchMembers5439.erase 18=independentCachedBranchMembers5427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5427
  · have he : independentCachedBranchMembers5439.filter (independentCachedEdge 18)=independentCachedBranchMembers5438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5438
end EntropyDesigns.QuadraticRefinement
