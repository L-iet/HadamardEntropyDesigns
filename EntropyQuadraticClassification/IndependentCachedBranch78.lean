/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch77
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5280 : Finset ℕ := ([136,252,1590,1622,1642,1708,1752,1764,1776,2606,2618,2638,2650,2662,2674,2716,2740,2772,2792,3126,3158,3178,3256,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5280 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5280 136 4
  · have he : independentCachedBranchMembers5280.erase 136=independentCachedBranchMembers5278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5278
  · have he : independentCachedBranchMembers5280.filter (independentCachedEdge 136)=independentCachedBranchMembers5279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5279
def independentCachedBranchMembers5281 : Finset ℕ := ([48,68,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5281 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5281 130 5
  · have he : independentCachedBranchMembers5281.erase 130=independentCachedBranchMembers5275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5275
  · have he : independentCachedBranchMembers5281.filter (independentCachedEdge 130)=independentCachedBranchMembers5280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5280
def independentCachedBranchMembers5282 : Finset ℕ := ([1590,1596,1642,1690,1714,1734,1764,2618,2638,2662,2668,2710,2716,2740,2762,2786,2792,3126,3132,3178,3226,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5282 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5282 5 (fun x => (if x<2716 then (if x<1764 then (if x<1690 then (if x<1596 then 0 else (if x<1642 then 1 else 0)) else (if x<1714 then 0 else (if x<1734 then 1 else 0))) else (if x<2662 then (if x<2618 then 1 else (if x<2638 then 0 else 2)) else (if x<2668 then 0 else (if x<2710 then 1 else 0)))) else (if x<3132 then (if x<2786 then (if x<2740 then 2 else (if x<2762 then 1 else 0)) else (if x<2792 then 1 else (if x<3126 then 2 else 3))) else (if x<3256 then (if x<3178 then 4 else (if x<3226 then 2 else 3)) else (if x<3276 then 2 else (if x<3300 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5283 : Finset ℕ := ([1590,1596,1642,2710,2716,2740,2762,2786,2792,3126,3132,3178] : List ℕ).toFinset
theorem independentCachedBranchBound5283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5283 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5283 4 (fun x => (if x<2762 then (if x<2710 then (if x<1596 then 0 else (if x<1642 then 1 else 0)) else (if x<2716 then 0 else (if x<2740 then 1 else 2))) else (if x<3126 then (if x<2786 then 0 else (if x<2792 then 2 else 3)) else (if x<3132 then 3 else (if x<3178 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5284 : Finset ℕ := ([68,1590,1596,1642,1690,1714,1734,1764,2618,2638,2662,2668,2710,2716,2740,2762,2786,2792,3126,3132,3178,3226,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5284 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5284 68 4
  · have he : independentCachedBranchMembers5284.erase 68=independentCachedBranchMembers5282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5282
  · have he : independentCachedBranchMembers5284.filter (independentCachedEdge 68)=independentCachedBranchMembers5283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5283
def independentCachedBranchMembers5285 : Finset ℕ := ([1642,1764,2662,2668,2710,2716,2786,2792,3178,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5285 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5285 4 (fun x => (if x<2716 then (if x<2662 then (if x<1764 then 0 else 0) else (if x<2668 then 0 else (if x<2710 then 1 else 2))) else (if x<3178 then (if x<2786 then 1 else (if x<2792 then 2 else 0)) else (if x<3226 then 1 else (if x<3300 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5286 : Finset ℕ := ([1764,2786,2792,3178,3226] : List ℕ).toFinset
theorem independentCachedBranchBound5286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5286 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5286 3 (fun x => (if x<2792 then (if x<2786 then 0 else 0) else (if x<3178 then 1 else (if x<3226 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5287 : Finset ℕ := ([1642,1690,1764,2662,2668,2710,2716,2786,2792,3178,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5287 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5287 1690 3
  · have he : independentCachedBranchMembers5287.erase 1690=independentCachedBranchMembers5285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5285
  · have he : independentCachedBranchMembers5287.filter (independentCachedEdge 1690)=independentCachedBranchMembers5286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5286
def independentCachedBranchMembers5288 : Finset ℕ := ([48,68,1590,1596,1642,1690,1714,1734,1764,2618,2638,2662,2668,2710,2716,2740,2762,2786,2792,3126,3132,3178,3226,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5288 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5288 48 4
  · have he : independentCachedBranchMembers5288.erase 48=independentCachedBranchMembers5284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5284
  · have he : independentCachedBranchMembers5288.filter (independentCachedEdge 48)=independentCachedBranchMembers5287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5287
def independentCachedBranchMembers5289 : Finset ℕ := ([48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5289 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5289 80 5
  · have he : independentCachedBranchMembers5289.erase 80=independentCachedBranchMembers5281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5281
  · have he : independentCachedBranchMembers5289.filter (independentCachedEdge 80)=independentCachedBranchMembers5288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5288
def independentCachedBranchMembers5290 : Finset ℕ := ([1622,1628,1642,1678,1714,1734,1776,2618,2638,2674,2680,2710,2716,2730,2772,2786,2792,3158,3164,3178,3214,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5290 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5290 5 (fun x => (if x<2716 then (if x<1776 then (if x<1678 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<1714 then 0 else (if x<1734 then 0 else 1))) else (if x<2674 then (if x<2618 then 1 else (if x<2638 then 2 else 0)) else (if x<2680 then 0 else (if x<2710 then 1 else 0)))) else (if x<3164 then (if x<2786 then (if x<2730 then 2 else (if x<2772 then 0 else 1)) else (if x<2792 then 1 else (if x<3158 then 2 else 3))) else (if x<3256 then (if x<3178 then 4 else (if x<3214 then 2 else 3)) else (if x<3276 then 2 else (if x<3312 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5291 : Finset ℕ := ([1642,1776,2674,2680,2710,2716,2786,2792,3178,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5291 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5291 4 (fun x => (if x<2716 then (if x<2674 then (if x<1776 then 0 else 0) else (if x<2680 then 0 else (if x<2710 then 1 else 2))) else (if x<3178 then (if x<2786 then 1 else (if x<2792 then 2 else 0)) else (if x<3214 then 1 else (if x<3312 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5292 : Finset ℕ := ([1776,2786,2792,3178,3214] : List ℕ).toFinset
theorem independentCachedBranchBound5292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5292 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5292 3 (fun x => (if x<2792 then (if x<2786 then 0 else 0) else (if x<3178 then 1 else (if x<3214 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5293 : Finset ℕ := ([1642,1678,1776,2674,2680,2710,2716,2786,2792,3178,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5293 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5293 1678 3
  · have he : independentCachedBranchMembers5293.erase 1678=independentCachedBranchMembers5291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5291
  · have he : independentCachedBranchMembers5293.filter (independentCachedEdge 1678)=independentCachedBranchMembers5292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5292
def independentCachedBranchMembers5294 : Finset ℕ := ([68,1622,1628,1642,1678,1714,1734,1776,2618,2638,2674,2680,2710,2716,2730,2772,2786,2792,3158,3164,3178,3214,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5294 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5294 68 4
  · have he : independentCachedBranchMembers5294.erase 68=independentCachedBranchMembers5290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5290
  · have he : independentCachedBranchMembers5294.filter (independentCachedEdge 68)=independentCachedBranchMembers5293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5293
def independentCachedBranchMembers5295 : Finset ℕ := ([1622,1628,1642,2710,2716,2730,2772,2786,2792,3158,3164,3178] : List ℕ).toFinset
theorem independentCachedBranchBound5295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5295 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5295 4 (fun x => (if x<2772 then (if x<2710 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<2716 then 0 else (if x<2730 then 1 else 0))) else (if x<3158 then (if x<2786 then 2 else (if x<2792 then 2 else 3)) else (if x<3164 then 3 else (if x<3178 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5296 : Finset ℕ := ([48,68,1622,1628,1642,1678,1714,1734,1776,2618,2638,2674,2680,2710,2716,2730,2772,2786,2792,3158,3164,3178,3214,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5296 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5296 48 4
  · have he : independentCachedBranchMembers5296.erase 48=independentCachedBranchMembers5294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5294
  · have he : independentCachedBranchMembers5296.filter (independentCachedEdge 48)=independentCachedBranchMembers5295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5295
def independentCachedBranchMembers5297 : Finset ℕ := ([36,48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5297 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5297 36 5
  · have he : independentCachedBranchMembers5297.erase 36=independentCachedBranchMembers5289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5289
  · have he : independentCachedBranchMembers5297.filter (independentCachedEdge 36)=independentCachedBranchMembers5296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5296
def independentCachedBranchMembers5298 : Finset ℕ := ([1596,1622,1642,1678,1714,1734,1752,1764,2618,2638,2668,2674,2710,2730,2740,2786,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5298 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5298 5 (fun x => (if x<2710 then (if x<1752 then (if x<1678 then (if x<1622 then 0 else (if x<1642 then 0 else 0)) else (if x<1714 then 0 else (if x<1734 then 0 else 1))) else (if x<2638 then (if x<1764 then 0 else (if x<2618 then 0 else 1)) else (if x<2668 then 1 else (if x<2674 then 2 else 2)))) else (if x<3226 then (if x<2786 then (if x<2730 then 1 else (if x<2740 then 2 else 2)) else (if x<3126 then 1 else (if x<3164 then 3 else 3))) else (if x<3276 then (if x<3238 then 3 else (if x<3256 then 4 else 4)) else (if x<3282 then 4 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5299 : Finset ℕ := ([1596,1622,1678,1764,2618,2638,2710,2786,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5299 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5299 4 (fun x => (if x<2710 then (if x<1764 then (if x<1622 then 0 else (if x<1678 then 0 else 0)) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<3256 then (if x<2786 then 1 else (if x<3238 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5300 : Finset ℕ := ([1596,1622,1642,1652,1678,1714,1734,1752,1764,2618,2638,2668,2674,2710,2730,2740,2786,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5300 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5300 1652 4
  · have he : independentCachedBranchMembers5300.erase 1652=independentCachedBranchMembers5298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5298
  · have he : independentCachedBranchMembers5300.filter (independentCachedEdge 1652)=independentCachedBranchMembers5299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5299
def independentCachedBranchMembers5301 : Finset ℕ := ([1596,1642,1678,1752,2618,2638,2668,2730,3164,3226,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5301 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5301 4 (fun x => (if x<2668 then (if x<1752 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<3226 then (if x<2730 then 2 else (if x<3164 then 2 else 2)) else (if x<3256 then 2 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5302 : Finset ℕ := ([246,1596,1622,1642,1652,1678,1714,1734,1752,1764,2618,2638,2668,2674,2710,2730,2740,2786,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5302 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5302 246 4
  · have he : independentCachedBranchMembers5302.erase 246=independentCachedBranchMembers5300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5300
  · have he : independentCachedBranchMembers5302.filter (independentCachedEdge 246)=independentCachedBranchMembers5301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5301
def independentCachedBranchMembers5303 : Finset ℕ := ([1622,1642,1752,1764,2618,2638,2674,2740,3126,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5303 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5303 4 (fun x => (if x<2674 then (if x<1764 then (if x<1642 then 0 else (if x<1752 then 0 else 0)) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<3256 then (if x<2740 then 2 else (if x<3126 then 2 else 2)) else (if x<3276 then 1 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5304 : Finset ℕ := ([130,246,1596,1622,1642,1652,1678,1714,1734,1752,1764,2618,2638,2668,2674,2710,2730,2740,2786,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5304 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5304 130 4
  · have he : independentCachedBranchMembers5304.erase 130=independentCachedBranchMembers5302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5302
  · have he : independentCachedBranchMembers5304.filter (independentCachedEdge 130)=independentCachedBranchMembers5303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5303
def independentCachedBranchMembers5305 : Finset ℕ := ([1596,1642,1678,1752,2674,2710,2740,2786,3126,3238,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5305 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5305 4 (fun x => (if x<2740 then (if x<1752 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<2674 then 0 else (if x<2710 then 1 else 1))) else (if x<3238 then (if x<2786 then 2 else (if x<3126 then 2 else 1)) else (if x<3282 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5306 : Finset ℕ := ([68,130,246,1596,1622,1642,1652,1678,1714,1734,1752,1764,2618,2638,2668,2674,2710,2730,2740,2786,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5306 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5306 68 4
  · have he : independentCachedBranchMembers5306.erase 68=independentCachedBranchMembers5304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5304
  · have he : independentCachedBranchMembers5306.filter (independentCachedEdge 68)=independentCachedBranchMembers5305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5305
def independentCachedBranchMembers5307 : Finset ℕ := ([1622,1642,1752,1764,2668,2710,2730,2786,3164,3226,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5307 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5307 4 (fun x => (if x<2730 then (if x<1764 then (if x<1642 then 0 else (if x<1752 then 0 else 0)) else (if x<2668 then 0 else (if x<2710 then 1 else 2))) else (if x<3226 then (if x<2786 then 1 else (if x<3164 then 2 else 1)) else (if x<3238 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5308 : Finset ℕ := ([48,68,130,246,1596,1622,1642,1652,1678,1714,1734,1752,1764,2618,2638,2668,2674,2710,2730,2740,2786,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5308 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5308 48 4
  · have he : independentCachedBranchMembers5308.erase 48=independentCachedBranchMembers5306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5306
  · have he : independentCachedBranchMembers5308.filter (independentCachedEdge 48)=independentCachedBranchMembers5307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5307
def independentCachedBranchMembers5309 : Finset ℕ := ([48,68,130,246,1596,1622,1678,1764,2618,2638,2710,2786,3126,3164,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5309 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5309 4 (fun x => (if x<2618 then (if x<1596 then (if x<130 then (if x<68 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1678 then (if x<1622 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2638 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3226 then (if x<3164 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5310 : Finset ℕ := ([48,68,130,246,1596,1622,1642,1652,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2710,2730,2740,2786,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5310 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5310 1708 4
  · have he : independentCachedBranchMembers5310.erase 1708=independentCachedBranchMembers5308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5308
  · have he : independentCachedBranchMembers5310.filter (independentCachedEdge 1708)=independentCachedBranchMembers5309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5309
def independentCachedBranchMembers5311 : Finset ℕ := ([36,48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5311 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5311 3288 5
  · have he : independentCachedBranchMembers5311.erase 3288=independentCachedBranchMembers5297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5297
  · have he : independentCachedBranchMembers5311.filter (independentCachedEdge 3288)=independentCachedBranchMembers5310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5310
end EntropyDesigns.QuadraticRefinement
