/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch78
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5312 : Finset ℕ := ([1590,1628,1642,1690,1708,1734,1752,1776,2606,2650,2668,2674,2716,2730,2740,2792,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5312 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5312 5 (fun x => (if x<2716 then (if x<1752 then (if x<1690 then (if x<1628 then 0 else (if x<1642 then 0 else 0)) else (if x<1708 then 0 else (if x<1734 then 0 else 0))) else (if x<2650 then (if x<1776 then 1 else (if x<2606 then 0 else 1)) else (if x<2668 then 1 else (if x<2674 then 2 else 2)))) else (if x<3214 then (if x<2792 then (if x<2730 then 1 else (if x<2740 then 2 else 2)) else (if x<3132 then 1 else (if x<3158 then 3 else 3))) else (if x<3276 then (if x<3238 then 3 else (if x<3256 then 4 else 4)) else (if x<3282 then 4 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5313 : Finset ℕ := ([1590,1628,1690,1776,2606,2650,2716,2792,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5313 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5313 4 (fun x => (if x<2716 then (if x<1776 then (if x<1628 then 0 else (if x<1690 then 0 else 0)) else (if x<2606 then 0 else (if x<2650 then 1 else 1))) else (if x<3256 then (if x<2792 then 1 else (if x<3238 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5314 : Finset ℕ := ([1590,1628,1642,1652,1690,1708,1734,1752,1776,2606,2650,2668,2674,2716,2730,2740,2792,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5314 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5314 1652 4
  · have he : independentCachedBranchMembers5314.erase 1652=independentCachedBranchMembers5312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5312
  · have he : independentCachedBranchMembers5314.filter (independentCachedEdge 1652)=independentCachedBranchMembers5313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5313
def independentCachedBranchMembers5315 : Finset ℕ := ([1590,1642,1690,1734,2606,2650,2674,2730,3158,3214,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5315 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5315 4 (fun x => (if x<2674 then (if x<1734 then (if x<1642 then 0 else (if x<1690 then 0 else 0)) else (if x<2606 then 0 else (if x<2650 then 1 else 1))) else (if x<3214 then (if x<2730 then 2 else (if x<3158 then 2 else 2)) else (if x<3238 then 2 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5316 : Finset ℕ := ([252,1590,1628,1642,1652,1690,1708,1734,1752,1776,2606,2650,2668,2674,2716,2730,2740,2792,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5316 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5316 252 4
  · have he : independentCachedBranchMembers5316.erase 252=independentCachedBranchMembers5314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5314
  · have he : independentCachedBranchMembers5316.filter (independentCachedEdge 252)=independentCachedBranchMembers5315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5315
def independentCachedBranchMembers5317 : Finset ℕ := ([1628,1642,1734,1776,2606,2650,2668,2740,3132,3238,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5317 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5317 4 (fun x => (if x<2668 then (if x<1776 then (if x<1642 then 0 else (if x<1734 then 0 else 0)) else (if x<2606 then 0 else (if x<2650 then 1 else 1))) else (if x<3238 then (if x<2740 then 2 else (if x<3132 then 2 else 2)) else (if x<3282 then 1 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5318 : Finset ℕ := ([136,252,1590,1628,1642,1652,1690,1708,1734,1752,1776,2606,2650,2668,2674,2716,2730,2740,2792,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5318 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5318 136 4
  · have he : independentCachedBranchMembers5318.erase 136=independentCachedBranchMembers5316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5316
  · have he : independentCachedBranchMembers5318.filter (independentCachedEdge 136)=independentCachedBranchMembers5317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5317
def independentCachedBranchMembers5319 : Finset ℕ := ([1590,1642,1690,1734,2668,2716,2740,2792,3132,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5319 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5319 4 (fun x => (if x<2740 then (if x<1734 then (if x<1642 then 0 else (if x<1690 then 0 else 0)) else (if x<2668 then 0 else (if x<2716 then 1 else 1))) else (if x<3256 then (if x<2792 then 2 else (if x<3132 then 2 else 1)) else (if x<3276 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5320 : Finset ℕ := ([80,136,252,1590,1628,1642,1652,1690,1708,1734,1752,1776,2606,2650,2668,2674,2716,2730,2740,2792,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5320 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5320 80 4
  · have he : independentCachedBranchMembers5320.erase 80=independentCachedBranchMembers5318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5318
  · have he : independentCachedBranchMembers5320.filter (independentCachedEdge 80)=independentCachedBranchMembers5319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5319
def independentCachedBranchMembers5321 : Finset ℕ := ([1628,1642,1734,1776,2674,2716,2730,2792,3158,3214,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5321 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5321 4 (fun x => (if x<2730 then (if x<1776 then (if x<1642 then 0 else (if x<1734 then 0 else 0)) else (if x<2674 then 0 else (if x<2716 then 1 else 2))) else (if x<3214 then (if x<2792 then 1 else (if x<3158 then 2 else 1)) else (if x<3256 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5322 : Finset ℕ := ([36,80,136,252,1590,1628,1642,1652,1690,1708,1734,1752,1776,2606,2650,2668,2674,2716,2730,2740,2792,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5322 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5322 36 4
  · have he : independentCachedBranchMembers5322.erase 36=independentCachedBranchMembers5320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5320
  · have he : independentCachedBranchMembers5322.filter (independentCachedEdge 36)=independentCachedBranchMembers5321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5321
def independentCachedBranchMembers5323 : Finset ℕ := ([36,80,136,252,1590,1628,1690,1776,2606,2650,2716,2792,3132,3158,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5323 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5323 4 (fun x => (if x<2606 then (if x<1590 then (if x<136 then (if x<80 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1690 then (if x<1628 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2650 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3214 then (if x<3158 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5324 : Finset ℕ := ([36,80,136,252,1590,1628,1642,1652,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2716,2730,2740,2792,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5324 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5324 1714 4
  · have he : independentCachedBranchMembers5324.erase 1714=independentCachedBranchMembers5322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5322
  · have he : independentCachedBranchMembers5324.filter (independentCachedEdge 1714)=independentCachedBranchMembers5323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5323
def independentCachedBranchMembers5325 : Finset ℕ := ([36,48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5325 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5325 3270 5
  · have he : independentCachedBranchMembers5325.erase 3270=independentCachedBranchMembers5311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5311
  · have he : independentCachedBranchMembers5325.filter (independentCachedEdge 3270)=independentCachedBranchMembers5324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5324
def independentCachedBranchMembers5326 : Finset ℕ := ([1596,1622,1642,1678,1708,1714,1752,1764,2606,2650,2662,2680,2716,2762,2772,2792,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5326 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5326 5 (fun x => (if x<2716 then (if x<1752 then (if x<1678 then (if x<1622 then 0 else (if x<1642 then 0 else 0)) else (if x<1708 then 0 else (if x<1714 then 1 else 0))) else (if x<2650 then (if x<1764 then 0 else (if x<2606 then 0 else 1)) else (if x<2662 then 1 else (if x<2680 then 2 else 2)))) else (if x<3226 then (if x<2792 then (if x<2762 then 1 else (if x<2772 then 2 else 2)) else (if x<3126 then 1 else (if x<3164 then 3 else 3))) else (if x<3276 then (if x<3238 then 3 else (if x<3256 then 4 else 4)) else (if x<3282 then 4 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5327 : Finset ℕ := ([1596,1622,1678,1764,2606,2650,2716,2792,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5327 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5327 4 (fun x => (if x<2716 then (if x<1764 then (if x<1622 then 0 else (if x<1678 then 0 else 0)) else (if x<2606 then 0 else (if x<2650 then 1 else 1))) else (if x<3256 then (if x<2792 then 1 else (if x<3238 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5328 : Finset ℕ := ([1596,1622,1642,1652,1678,1708,1714,1752,1764,2606,2650,2662,2680,2716,2762,2772,2792,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5328 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5328 1652 4
  · have he : independentCachedBranchMembers5328.erase 1652=independentCachedBranchMembers5326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5326
  · have he : independentCachedBranchMembers5328.filter (independentCachedEdge 1652)=independentCachedBranchMembers5327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5327
def independentCachedBranchMembers5329 : Finset ℕ := ([1622,1642,1678,1714,2606,2650,2662,2762,3126,3226,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5329 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5329 4 (fun x => (if x<2662 then (if x<1714 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<2606 then 0 else (if x<2650 then 1 else 1))) else (if x<3226 then (if x<2762 then 2 else (if x<3126 then 2 else 2)) else (if x<3238 then 2 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5330 : Finset ℕ := ([252,1596,1622,1642,1652,1678,1708,1714,1752,1764,2606,2650,2662,2680,2716,2762,2772,2792,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5330 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5330 252 4
  · have he : independentCachedBranchMembers5330.erase 252=independentCachedBranchMembers5328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5328
  · have he : independentCachedBranchMembers5330.filter (independentCachedEdge 252)=independentCachedBranchMembers5329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5329
def independentCachedBranchMembers5331 : Finset ℕ := ([1596,1642,1714,1764,2606,2650,2680,2772,3164,3238,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5331 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5331 4 (fun x => (if x<2680 then (if x<1764 then (if x<1642 then 0 else (if x<1714 then 0 else 0)) else (if x<2606 then 0 else (if x<2650 then 1 else 1))) else (if x<3238 then (if x<2772 then 2 else (if x<3164 then 2 else 2)) else (if x<3282 then 1 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5332 : Finset ℕ := ([136,252,1596,1622,1642,1652,1678,1708,1714,1752,1764,2606,2650,2662,2680,2716,2762,2772,2792,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5332 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5332 136 4
  · have he : independentCachedBranchMembers5332.erase 136=independentCachedBranchMembers5330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5330
  · have he : independentCachedBranchMembers5332.filter (independentCachedEdge 136)=independentCachedBranchMembers5331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5331
def independentCachedBranchMembers5333 : Finset ℕ := ([1596,1642,1714,1764,2662,2716,2762,2792,3126,3226,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5333 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5333 4 (fun x => (if x<2762 then (if x<1764 then (if x<1642 then 0 else (if x<1714 then 0 else 0)) else (if x<2662 then 0 else (if x<2716 then 1 else 2))) else (if x<3226 then (if x<2792 then 1 else (if x<3126 then 2 else 1)) else (if x<3256 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5334 : Finset ℕ := ([80,136,252,1596,1622,1642,1652,1678,1708,1714,1752,1764,2606,2650,2662,2680,2716,2762,2772,2792,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5334 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5334 80 4
  · have he : independentCachedBranchMembers5334.erase 80=independentCachedBranchMembers5332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5332
  · have he : independentCachedBranchMembers5334.filter (independentCachedEdge 80)=independentCachedBranchMembers5333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5333
def independentCachedBranchMembers5335 : Finset ℕ := ([1622,1642,1678,1714,2680,2716,2772,2792,3164,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5335 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5335 4 (fun x => (if x<2772 then (if x<1714 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<2680 then 0 else (if x<2716 then 1 else 1))) else (if x<3256 then (if x<2792 then 2 else (if x<3164 then 2 else 1)) else (if x<3276 then 1 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5336 : Finset ℕ := ([36,80,136,252,1596,1622,1642,1652,1678,1708,1714,1752,1764,2606,2650,2662,2680,2716,2762,2772,2792,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5336 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5336 36 4
  · have he : independentCachedBranchMembers5336.erase 36=independentCachedBranchMembers5334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5334
  · have he : independentCachedBranchMembers5336.filter (independentCachedEdge 36)=independentCachedBranchMembers5335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5335
def independentCachedBranchMembers5337 : Finset ℕ := ([36,80,136,252,1596,1622,1678,1764,2606,2650,2716,2792,3126,3164,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5337 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5337 4 (fun x => (if x<2606 then (if x<1596 then (if x<136 then (if x<80 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1622 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3126 then (if x<2716 then (if x<2650 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3226 then (if x<3164 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5338 : Finset ℕ := ([36,80,136,252,1596,1622,1642,1652,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2716,2762,2772,2792,3126,3164,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5338 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5338 1734 4
  · have he : independentCachedBranchMembers5338.erase 1734=independentCachedBranchMembers5336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5336
  · have he : independentCachedBranchMembers5338.filter (independentCachedEdge 1734)=independentCachedBranchMembers5337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5337
def independentCachedBranchMembers5339 : Finset ℕ := ([36,48,68,80,130,136,246,252,1590,1596,1622,1628,1642,1652,1678,1690,1708,1714,1734,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3188,3214,3226,3238,3250,3256,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5339 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5339 3250 5
  · have he : independentCachedBranchMembers5339.erase 3250=independentCachedBranchMembers5325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5325
  · have he : independentCachedBranchMembers5339.filter (independentCachedEdge 3250)=independentCachedBranchMembers5338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5338
def independentCachedBranchMembers5340 : Finset ℕ := ([1590,1628,1642,1690,1708,1714,1734,1776,2618,2638,2662,2680,2710,2762,2772,2786,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5340 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5340 5 (fun x => (if x<2710 then (if x<1734 then (if x<1690 then (if x<1628 then 0 else (if x<1642 then 0 else 0)) else (if x<1708 then 0 else (if x<1714 then 0 else 1))) else (if x<2638 then (if x<1776 then 0 else (if x<2618 then 0 else 1)) else (if x<2662 then 1 else (if x<2680 then 2 else 2)))) else (if x<3214 then (if x<2786 then (if x<2762 then 1 else (if x<2772 then 2 else 2)) else (if x<3132 then 1 else (if x<3158 then 3 else 3))) else (if x<3276 then (if x<3238 then 3 else (if x<3256 then 4 else 4)) else (if x<3282 then 4 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5341 : Finset ℕ := ([1590,1628,1690,1776,2618,2638,2710,2786,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5341 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5341 4 (fun x => (if x<2710 then (if x<1776 then (if x<1628 then 0 else (if x<1690 then 0 else 0)) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<3256 then (if x<2786 then 1 else (if x<3238 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5342 : Finset ℕ := ([1590,1628,1642,1652,1690,1708,1714,1734,1776,2618,2638,2662,2680,2710,2762,2772,2786,3132,3158,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5342 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5342 1652 4
  · have he : independentCachedBranchMembers5342.erase 1652=independentCachedBranchMembers5340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5340
  · have he : independentCachedBranchMembers5342.filter (independentCachedEdge 1652)=independentCachedBranchMembers5341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5341
def independentCachedBranchMembers5343 : Finset ℕ := ([1628,1642,1690,1708,2618,2638,2680,2762,3132,3214,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5343 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5343 4 (fun x => (if x<2680 then (if x<1708 then (if x<1642 then 0 else (if x<1690 then 0 else 0)) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<3214 then (if x<2762 then 2 else (if x<3132 then 2 else 2)) else (if x<3256 then 2 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
