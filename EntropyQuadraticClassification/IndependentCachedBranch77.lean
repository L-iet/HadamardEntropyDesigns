/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch76
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5248 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2606,2618,2638,2650,2710,2716,2786,2792,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5248 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5248 5 (fun x => (if x<2716 then (if x<1752 then (if x<1708 then (if x<1652 then 0 else 0) else (if x<1714 then 0 else (if x<1734 then 0 else 0))) else (if x<2638 then (if x<2606 then 0 else (if x<2618 then 1 else 2)) else (if x<2650 then 2 else (if x<2710 then 1 else 1)))) else (if x<3158 then (if x<2792 then (if x<2786 then 2 else 1) else (if x<3126 then 2 else (if x<3132 then 3 else 4))) else (if x<3226 then (if x<3164 then 4 else (if x<3214 then 3 else 3)) else (if x<3300 then 4 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5249 : Finset ℕ := ([1596,1622,1642,1652,1690,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5249 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5249 3188 5
  · have he : independentCachedBranchMembers5249.erase 3188=independentCachedBranchMembers5247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5247
  · have he : independentCachedBranchMembers5249.filter (independentCachedEdge 3188)=independentCachedBranchMembers5248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5248
def independentCachedBranchMembers5250 : Finset ℕ := ([1652,1690,1708,1734,1776,2606,2638,2674,2680,2710,2716,2730,2762,3126,3132,3158,3164,3178,3214,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5250 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5250 5 (fun x => (if x<2730 then (if x<2606 then (if x<1708 then (if x<1690 then 0 else 1) else (if x<1734 then 0 else (if x<1776 then 0 else 1))) else (if x<2680 then (if x<2638 then 2 else (if x<2674 then 3 else 2)) else (if x<2710 then 3 else (if x<2716 then 2 else 3)))) else (if x<3164 then (if x<3126 then (if x<2762 then 3 else 2) else (if x<3132 then 2 else (if x<3158 then 0 else 0))) else (if x<3256 then (if x<3178 then 3 else (if x<3214 then 2 else 0)) else (if x<3282 then 1 else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5251 : Finset ℕ := ([1596,1622,1642,1652,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5251 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5251 1764 5
  · have he : independentCachedBranchMembers5251.erase 1764=independentCachedBranchMembers5249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5249
  · have he : independentCachedBranchMembers5251.filter (independentCachedEdge 1764)=independentCachedBranchMembers5250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5250
def independentCachedBranchMembers5252 : Finset ℕ := ([1652,1690,1708,1734,1776,2618,2650,2662,2668,2740,2772,2786,2792,3126,3132,3158,3164,3178,3214,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5252 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5252 5 (fun x => (if x<2786 then (if x<2618 then (if x<1708 then (if x<1690 then 0 else 1) else (if x<1734 then 0 else (if x<1776 then 0 else 1))) else (if x<2668 then (if x<2650 then 2 else (if x<2662 then 3 else 2)) else (if x<2740 then 3 else (if x<2772 then 2 else 3)))) else (if x<3164 then (if x<3126 then (if x<2792 then 3 else 2) else (if x<3132 then 2 else (if x<3158 then 0 else 0))) else (if x<3256 then (if x<3178 then 3 else (if x<3214 then 2 else 0)) else (if x<3282 then 1 else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5253 : Finset ℕ := ([1596,1622,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5253 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5253 1678 5
  · have he : independentCachedBranchMembers5253.erase 1678=independentCachedBranchMembers5251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5251
  · have he : independentCachedBranchMembers5253.filter (independentCachedEdge 1678)=independentCachedBranchMembers5252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5252
def independentCachedBranchMembers5254 : Finset ℕ := ([1596,1622,1652,1714,1752,2606,2618,2662,2674,2710,2740,2762,2792,3126,3164,3178,3214,3226,3256,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5254 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5254 5 (fun x => (if x<2762 then (if x<2606 then (if x<1652 then (if x<1622 then 0 else 0) else (if x<1714 then 1 else (if x<1752 then 0 else 0))) else (if x<2674 then (if x<2618 then 2 else (if x<2662 then 3 else 1)) else (if x<2710 then 2 else (if x<2740 then 2 else 1)))) else (if x<3214 then (if x<3126 then (if x<2792 then 2 else 3) else (if x<3164 then 0 else (if x<3178 then 0 else 2))) else (if x<3282 then (if x<3226 then 2 else (if x<3256 then 4 else 0)) else (if x<3300 then 0 else (if x<3312 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5255 : Finset ℕ := ([1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5255 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5255 1628 5
  · have he : independentCachedBranchMembers5255.erase 1628=independentCachedBranchMembers5253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5253
  · have he : independentCachedBranchMembers5255.filter (independentCachedEdge 1628)=independentCachedBranchMembers5254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5254
def independentCachedBranchMembers5256 : Finset ℕ := ([1596,1622,1652,1714,1752,2638,2650,2668,2680,2716,2730,2772,2786,3126,3164,3178,3214,3226,3256,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5256 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5256 5 (fun x => (if x<2772 then (if x<2638 then (if x<1652 then (if x<1622 then 0 else 0) else (if x<1714 then 1 else (if x<1752 then 0 else 0))) else (if x<2680 then (if x<2650 then 2 else (if x<2668 then 3 else 1)) else (if x<2716 then 2 else (if x<2730 then 2 else 1)))) else (if x<3214 then (if x<3126 then (if x<2786 then 3 else 3) else (if x<3164 then 0 else (if x<3178 then 0 else 2))) else (if x<3282 then (if x<3226 then 2 else (if x<3256 then 1 else 0)) else (if x<3300 then 0 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5257 : Finset ℕ := ([1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5257 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5257 1590 5
  · have he : independentCachedBranchMembers5257.erase 1590=independentCachedBranchMembers5255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5255
  · have he : independentCachedBranchMembers5257.filter (independentCachedEdge 1590)=independentCachedBranchMembers5256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5256
def independentCachedBranchMembers5258 : Finset ℕ := ([1590,1622,1642,1678,1690,1714,1734,2606,2618,2638,2650,2662,2674,2710,2730,2762,2786,3126,3158,3178,3214,3226,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5258 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5258 5 (fun x => (if x<2674 then (if x<1734 then (if x<1678 then (if x<1622 then 0 else (if x<1642 then 1 else 0)) else (if x<1690 then 0 else (if x<1714 then 1 else 2))) else (if x<2638 then (if x<2606 then 2 else (if x<2618 then 0 else 2)) else (if x<2650 then 2 else (if x<2662 then 1 else 1)))) else (if x<3158 then (if x<2762 then (if x<2710 then 0 else (if x<2730 then 0 else 1)) else (if x<2786 then 0 else (if x<3126 then 2 else 3))) else (if x<3226 then (if x<3178 then 4 else (if x<3214 then 3 else 3)) else (if x<3238 then 4 else (if x<3282 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5259 : Finset ℕ := ([252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5259 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5259 252 5
  · have he : independentCachedBranchMembers5259.erase 252=independentCachedBranchMembers5257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5257
  · have he : independentCachedBranchMembers5259.filter (independentCachedEdge 252)=independentCachedBranchMembers5258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5258
def independentCachedBranchMembers5260 : Finset ℕ := ([1596,1628,1642,1714,1734,1764,1776,2606,2618,2638,2650,2668,2680,2710,2740,2772,2786,3132,3164,3178,3238,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5260 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5260 5 (fun x => (if x<2680 then (if x<1776 then (if x<1714 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<1734 then 0 else (if x<1764 then 1 else 0))) else (if x<2638 then (if x<2606 then 1 else (if x<2618 then 2 else 0)) else (if x<2650 then 1 else (if x<2668 then 2 else 0)))) else (if x<3164 then (if x<2772 then (if x<2710 then 1 else (if x<2740 then 2 else 0)) else (if x<2786 then 1 else (if x<3132 then 0 else 3))) else (if x<3282 then (if x<3178 then 4 else (if x<3238 then 2 else 2)) else (if x<3300 then 2 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5261 : Finset ℕ := ([136,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5261 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5261 136 5
  · have he : independentCachedBranchMembers5261.erase 136=independentCachedBranchMembers5259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5259
  · have he : independentCachedBranchMembers5261.filter (independentCachedEdge 136)=independentCachedBranchMembers5260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5260
def independentCachedBranchMembers5262 : Finset ℕ := ([1590,1596,1642,1678,1708,1752,1776,2606,2674,2680,2710,2716,2740,2762,2786,2792,3126,3132,3178,3214,3238,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5262 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5262 5 (fun x => (if x<2716 then (if x<1752 then (if x<1642 then (if x<1596 then 0 else 1) else (if x<1678 then 0 else (if x<1708 then 0 else 2))) else (if x<2674 then (if x<1776 then 1 else (if x<2606 then 2 else 0)) else (if x<2680 then 0 else (if x<2710 then 1 else 0)))) else (if x<3132 then (if x<2786 then (if x<2740 then 1 else (if x<2762 then 2 else 0)) else (if x<2792 then 3 else (if x<3126 then 2 else 4))) else (if x<3238 then (if x<3178 then 3 else (if x<3214 then 3 else 4)) else (if x<3282 then 3 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5263 : Finset ℕ := ([1590,1596,1678,1776,2674,2680,2740,2762,3126,3132,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5263 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5263 4 (fun x => (if x<2740 then (if x<1776 then (if x<1596 then 0 else (if x<1678 then 1 else 0)) else (if x<2674 then 1 else (if x<2680 then 0 else 1))) else (if x<3132 then (if x<2762 then 1 else (if x<3126 then 0 else 2)) else (if x<3214 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5264 : Finset ℕ := ([1590,1596,1642,1678,1708,1752,1776,2606,2650,2674,2680,2710,2716,2740,2762,2786,2792,3126,3132,3178,3214,3238,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5264 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5264 2650 4
  · have he : independentCachedBranchMembers5264.erase 2650=independentCachedBranchMembers5262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5262
  · have he : independentCachedBranchMembers5264.filter (independentCachedEdge 2650)=independentCachedBranchMembers5263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5263
def independentCachedBranchMembers5265 : Finset ℕ := ([68,136,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5265 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5265 68 5
  · have he : independentCachedBranchMembers5265.erase 68=independentCachedBranchMembers5261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5261
  · have he : independentCachedBranchMembers5265.filter (independentCachedEdge 68)=independentCachedBranchMembers5264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5264
def independentCachedBranchMembers5266 : Finset ℕ := ([1622,1628,1642,1690,1708,1752,1764,2650,2662,2668,2710,2716,2730,2772,2786,2792,3158,3164,3178,3226,3238,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5266 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5266 5 (fun x => (if x<2716 then (if x<1752 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1690 then 0 else (if x<1708 then 0 else 1))) else (if x<2662 then (if x<1764 then 2 else (if x<2650 then 2 else 0)) else (if x<2668 then 0 else (if x<2710 then 1 else 0)))) else (if x<3164 then (if x<2786 then (if x<2730 then 1 else (if x<2772 then 0 else 2)) else (if x<2792 then 3 else (if x<3158 then 2 else 4))) else (if x<3238 then (if x<3178 then 3 else (if x<3226 then 3 else 4)) else (if x<3282 then 4 else (if x<3300 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5267 : Finset ℕ := ([1622,1628,1690,1764,2662,2668,2730,2772,3158,3164,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5267 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5267 4 (fun x => (if x<2730 then (if x<1764 then (if x<1628 then 0 else (if x<1690 then 1 else 0)) else (if x<2662 then 1 else (if x<2668 then 0 else 1))) else (if x<3164 then (if x<2772 then 0 else (if x<3158 then 1 else 2)) else (if x<3226 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5268 : Finset ℕ := ([1622,1628,1642,1690,1708,1752,1764,2606,2650,2662,2668,2710,2716,2730,2772,2786,2792,3158,3164,3178,3226,3238,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5268 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5268 2606 4
  · have he : independentCachedBranchMembers5268.erase 2606=independentCachedBranchMembers5266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5266
  · have he : independentCachedBranchMembers5268.filter (independentCachedEdge 2606)=independentCachedBranchMembers5267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5267
def independentCachedBranchMembers5269 : Finset ℕ := ([48,68,136,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5269 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5269 48 5
  · have he : independentCachedBranchMembers5269.erase 48=independentCachedBranchMembers5265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5265
  · have he : independentCachedBranchMembers5269.filter (independentCachedEdge 48)=independentCachedBranchMembers5268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5268
def independentCachedBranchMembers5270 : Finset ℕ := ([1596,1628,1642,1678,1690,1708,1752,2606,2618,2638,2650,2668,2680,2716,2730,2762,2792,3132,3164,3178,3214,3226,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5270 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5270 5 (fun x => (if x<2680 then (if x<1752 then (if x<1678 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<1690 then 0 else (if x<1708 then 1 else 1))) else (if x<2638 then (if x<2606 then 0 else (if x<2618 then 0 else 2)) else (if x<2650 then 2 else (if x<2668 then 1 else 1)))) else (if x<3164 then (if x<2762 then (if x<2716 then 0 else (if x<2730 then 0 else 1)) else (if x<2792 then 0 else (if x<3132 then 2 else 3))) else (if x<3226 then (if x<3178 then 4 else (if x<3214 then 2 else 3)) else (if x<3256 then 4 else (if x<3276 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5271 : Finset ℕ := ([1642,1678,1690,2606,2618,2638,2650,2730,2762,3178,3214,3226] : List ℕ).toFinset
theorem independentCachedBranchBound5271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5271 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5271 4 (fun x => (if x<2650 then (if x<2606 then (if x<1678 then 0 else (if x<1690 then 0 else 1)) else (if x<2618 then 0 else (if x<2638 then 1 else 2))) else (if x<3178 then (if x<2730 then 3 else (if x<2762 then 2 else 0)) else (if x<3214 then 2 else (if x<3226 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5272 : Finset ℕ := ([252,1596,1628,1642,1678,1690,1708,1752,2606,2618,2638,2650,2668,2680,2716,2730,2762,2792,3132,3164,3178,3214,3226,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5272 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5272 252 4
  · have he : independentCachedBranchMembers5272.erase 252=independentCachedBranchMembers5270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5270
  · have he : independentCachedBranchMembers5272.filter (independentCachedEdge 252)=independentCachedBranchMembers5271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5271
def independentCachedBranchMembers5273 : Finset ℕ := ([1596,1628,1642,2606,2618,2638,2650,2668,2680,3132,3164,3178] : List ℕ).toFinset
theorem independentCachedBranchBound5273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5273 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5273 4 (fun x => (if x<2650 then (if x<2606 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<2618 then 0 else (if x<2638 then 2 else 1))) else (if x<3132 then (if x<2668 then 3 else (if x<2680 then 2 else 0)) else (if x<3164 then 2 else (if x<3178 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5274 : Finset ℕ := ([136,252,1596,1628,1642,1678,1690,1708,1752,2606,2618,2638,2650,2668,2680,2716,2730,2762,2792,3132,3164,3178,3214,3226,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5274 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5274 136 4
  · have he : independentCachedBranchMembers5274.erase 136=independentCachedBranchMembers5272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5272
  · have he : independentCachedBranchMembers5274.filter (independentCachedEdge 136)=independentCachedBranchMembers5273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5273
def independentCachedBranchMembers5275 : Finset ℕ := ([48,68,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5275 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5275 246 5
  · have he : independentCachedBranchMembers5275.erase 246=independentCachedBranchMembers5269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5269
  · have he : independentCachedBranchMembers5275.filter (independentCachedEdge 246)=independentCachedBranchMembers5274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5274
def independentCachedBranchMembers5276 : Finset ℕ := ([1590,1622,1642,1708,1752,1764,1776,2606,2618,2638,2650,2662,2674,2716,2740,2772,2792,3126,3158,3178,3256,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5276 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5276 5 (fun x => (if x<2674 then (if x<1776 then (if x<1708 then (if x<1622 then 0 else (if x<1642 then 1 else 0)) else (if x<1752 then 0 else (if x<1764 then 1 else 1))) else (if x<2638 then (if x<2606 then 0 else (if x<2618 then 0 else 2)) else (if x<2650 then 2 else (if x<2662 then 1 else 1)))) else (if x<3158 then (if x<2772 then (if x<2716 then 0 else (if x<2740 then 2 else 0)) else (if x<2792 then 1 else (if x<3126 then 0 else 3))) else (if x<3276 then (if x<3178 then 4 else (if x<3256 then 2 else 2)) else (if x<3300 then 2 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5277 : Finset ℕ := ([1590,1622,1642,2606,2618,2638,2650,2662,2674,3126,3158,3178] : List ℕ).toFinset
theorem independentCachedBranchBound5277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5277 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5277 4 (fun x => (if x<2650 then (if x<2606 then (if x<1622 then 0 else (if x<1642 then 1 else 0)) else (if x<2618 then 0 else (if x<2638 then 2 else 1))) else (if x<3126 then (if x<2662 then 3 else (if x<2674 then 2 else 0)) else (if x<3158 then 2 else (if x<3178 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5278 : Finset ℕ := ([252,1590,1622,1642,1708,1752,1764,1776,2606,2618,2638,2650,2662,2674,2716,2740,2772,2792,3126,3158,3178,3256,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5278 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5278 252 4
  · have he : independentCachedBranchMembers5278.erase 252=independentCachedBranchMembers5276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5276
  · have he : independentCachedBranchMembers5278.filter (independentCachedEdge 252)=independentCachedBranchMembers5277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5277
def independentCachedBranchMembers5279 : Finset ℕ := ([1642,1764,1776,2606,2618,2638,2650,2740,2772,3178,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5279 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5279 4 (fun x => (if x<2650 then (if x<2606 then (if x<1764 then 0 else (if x<1776 then 0 else 1)) else (if x<2618 then 1 else (if x<2638 then 0 else 2))) else (if x<3178 then (if x<2740 then 3 else (if x<2772 then 0 else 2)) else (if x<3300 then 2 else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
