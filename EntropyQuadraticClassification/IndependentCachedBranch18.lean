/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch17
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers2304 : Finset ℕ := ([18,132,192,252,1594,1626,1708,1740,1748,1768,1776,2606,2646,2674,2716,2776,2788,3102,3130,3244,3252,3276,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2304 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2304 5 (fun x => (if x<2646 then (if x<1708 then (if x<252 then (if x<132 then 0 else (if x<192 then 0 else 1)) else (if x<1594 then 1 else (if x<1626 then 0 else 2))) else (if x<1768 then (if x<1740 then 0 else (if x<1748 then 1 else 2)) else (if x<1776 then 2 else (if x<2606 then 1 else 3)))) else (if x<3130 then (if x<2776 then (if x<2674 then 2 else (if x<2716 then 0 else 3)) else (if x<2788 then 1 else (if x<3102 then 0 else 3))) else (if x<3276 then (if x<3244 then 4 else (if x<3252 then 3 else 4)) else (if x<3284 then 0 else (if x<3304 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2305 : Finset ℕ := ([18,132,1594,1626,1708,1740,1776,2646,2716,3102,3252,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2305 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2305 4 (fun x => (if x<1776 then (if x<1626 then (if x<132 then 0 else (if x<1594 then 0 else 0)) else (if x<1708 then 1 else (if x<1740 then 0 else 1))) else (if x<3102 then (if x<2646 then 1 else (if x<2716 then 2 else 2)) else (if x<3284 then (if x<3252 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2306 : Finset ℕ := ([18,132,192,252,1594,1626,1708,1740,1748,1768,1776,2606,2646,2674,2716,2776,2788,3102,3130,3244,3252,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2306 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2306 3312 4
  · have he : independentCachedBranchMembers2306.erase 3312=independentCachedBranchMembers2304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2304
  · have he : independentCachedBranchMembers2306.filter (independentCachedEdge 3312)=independentCachedBranchMembers2305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2305
def independentCachedBranchMembers2307 : Finset ℕ := ([192,252,1626,1740,1748,1768,1776,2606,2716,3102,3130,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2307 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2307 4 (fun x => (if x<1776 then (if x<1740 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1748 then 0 else (if x<1768 then 1 else 1))) else (if x<3102 then (if x<2606 then 0 else (if x<2716 then 2 else 2)) else (if x<3244 then (if x<3130 then 2 else 3) else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2308 : Finset ℕ := ([18,132,192,252,1594,1626,1708,1740,1748,1768,1776,2606,2646,2674,2716,2776,2788,3102,3130,3162,3244,3252,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2308 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2308 3162 4
  · have he : independentCachedBranchMembers2308.erase 3162=independentCachedBranchMembers2306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2306
  · have he : independentCachedBranchMembers2308.filter (independentCachedEdge 3162)=independentCachedBranchMembers2307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2307
def independentCachedBranchMembers2309 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2662,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3126,3130,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2309 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2309 2662 5
  · have he : independentCachedBranchMembers2309.erase 2662=independentCachedBranchMembers2303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2303
  · have he : independentCachedBranchMembers2309.filter (independentCachedEdge 2662)=independentCachedBranchMembers2308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2308
def independentCachedBranchMembers2310 : Finset ℕ := ([132,192,252,1594,1642,1692,1740,1752,1764,1776,2606,2618,2646,2716,2740,2764,2776,2788,2800,3102,3126,3162,3186,3244,3256,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2310 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2310 5 (fun x => (if x<2716 then (if x<1740 then (if x<1594 then (if x<192 then 0 else (if x<252 then 1 else 0)) else (if x<1642 then 1 else (if x<1692 then 2 else 0))) else (if x<1776 then (if x<1752 then 2 else (if x<1764 then 1 else 0)) else (if x<2618 then (if x<2606 then 2 else 1) else (if x<2646 then 3 else 3)))) else (if x<3126 then (if x<2776 then (if x<2740 then 3 else (if x<2764 then 0 else 0)) else (if x<2800 then (if x<2788 then 4 else 4) else (if x<3102 then 3 else 3))) else (if x<3244 then (if x<3162 then 1 else (if x<3186 then 4 else 2)) else (if x<3284 then (if x<3256 then 0 else 3) else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2311 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2662,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3126,3130,3158,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2311 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2311 3158 5
  · have he : independentCachedBranchMembers2311.erase 3158=independentCachedBranchMembers2309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2309
  · have he : independentCachedBranchMembers2311.filter (independentCachedEdge 3158)=independentCachedBranchMembers2310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2310
def independentCachedBranchMembers2312 : Finset ℕ := ([18,132,252,1626,1650,1720,1740,1764,1768,2606,2646,2650,2674,2716,2740,2764,2788,2792,3102,3126,3130,3178,3244,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2312 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2312 5 (fun x => (if x<2716 then (if x<1740 then (if x<1626 then (if x<132 then 0 else (if x<252 then 0 else 1)) else (if x<1650 then 0 else (if x<1720 then 2 else 1))) else (if x<2606 then (if x<1764 then 0 else (if x<1768 then 1 else 2)) else (if x<2650 then (if x<2646 then 3 else 2) else (if x<2674 then 3 else 0)))) else (if x<3126 then (if x<2788 then (if x<2740 then 3 else (if x<2764 then 1 else 2)) else (if x<2792 then 0 else (if x<3102 then 1 else 3))) else (if x<3244 then (if x<3130 then 2 else (if x<3178 then 0 else 3)) else (if x<3288 then (if x<3284 then 0 else 4) else (if x<3312 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2313 : Finset ℕ := ([18,1650,1720,1740,2606,2646,2650,2716,2788,2792,3126,3130,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2313 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2313 4 (fun x => (if x<2650 then (if x<1740 then (if x<1650 then 0 else (if x<1720 then 0 else 1)) else (if x<2606 then 1 else (if x<2646 then 2 else 0))) else (if x<2792 then (if x<2716 then 2 else (if x<2788 then 1 else 3)) else (if x<3130 then (if x<3126 then 1 else 0) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2314 : Finset ℕ := ([18,132,252,1626,1650,1692,1720,1740,1764,1768,2606,2646,2650,2674,2716,2740,2764,2788,2792,3102,3126,3130,3178,3244,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2314 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2314 1692 4
  · have he : independentCachedBranchMembers2314.erase 1692=independentCachedBranchMembers2312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2312
  · have he : independentCachedBranchMembers2314.filter (independentCachedEdge 1692)=independentCachedBranchMembers2313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2313
def independentCachedBranchMembers2315 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2662,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3158,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2315 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2315 3118 5
  · have he : independentCachedBranchMembers2315.erase 3118=independentCachedBranchMembers2311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2311
  · have he : independentCachedBranchMembers2315.filter (independentCachedEdge 3118)=independentCachedBranchMembers2314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2314
def independentCachedBranchMembers2316 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,2606,2646,2650,2662,2740,2764,2800,3126,3186,3244,3284,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2316 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2316 5 (fun x => (if x<1768 then (if x<1614 then (if x<252 then (if x<132 then 0 else (if x<192 then 0 else 1)) else (if x<1590 then 1 else (if x<1594 then 2 else 0))) else (if x<1708 then (if x<1650 then 2 else (if x<1692 then 3 else 2)) else (if x<1752 then (if x<1748 then 0 else 1) else (if x<1764 then 3 else 2)))) else (if x<2800 then (if x<2650 then (if x<2606 then 1 else (if x<2646 then 4 else 4)) else (if x<2740 then (if x<2662 then 0 else 2) else (if x<2764 then 2 else 0))) else (if x<3244 then (if x<3126 then 1 else (if x<3186 then 3 else 0)) else (if x<3288 then (if x<3284 then 4 else 4) else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2317 : Finset ℕ := ([132,1594,1614,1650,1692,1748,1768,2606,2650,2662,2740,3126,3244,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2317 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2317 4 (fun x => (if x<2606 then (if x<1650 then (if x<1594 then 0 else (if x<1614 then 0 else 1)) else (if x<1748 then (if x<1692 then 1 else 0) else (if x<1768 then 1 else 1))) else (if x<3126 then (if x<2662 then (if x<2650 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3288 then (if x<3244 then 3 else 2) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2318 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,2606,2646,2650,2662,2740,2764,2800,3126,3186,3244,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2318 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2318 3304 4
  · have he : independentCachedBranchMembers2318.erase 3304=independentCachedBranchMembers2316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2316
  · have he : independentCachedBranchMembers2318.filter (independentCachedEdge 3304)=independentCachedBranchMembers2317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2317
def independentCachedBranchMembers2319 : Finset ℕ := ([252,1594,1614,1692,1708,1752,1768,2646,2662,2740,2800,3126,3186,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2319 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2319 4 (fun x => (if x<2646 then (if x<1692 then (if x<1594 then 0 else (if x<1614 then 1 else 1)) else (if x<1752 then (if x<1708 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3126 then (if x<2740 then (if x<2662 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3284 then (if x<3186 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2320 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,2606,2646,2650,2662,2740,2764,2800,3126,3130,3186,3244,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2320 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2320 3130 4
  · have he : independentCachedBranchMembers2320.erase 3130=independentCachedBranchMembers2318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2318
  · have he : independentCachedBranchMembers2320.filter (independentCachedEdge 3130)=independentCachedBranchMembers2319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2319
def independentCachedBranchMembers2321 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2618,2638,2646,2650,2662,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3158,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2321 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2321 2638 5
  · have he : independentCachedBranchMembers2321.erase 2638=independentCachedBranchMembers2315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2315
  · have he : independentCachedBranchMembers2321.filter (independentCachedEdge 2638)=independentCachedBranchMembers2320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2320
def independentCachedBranchMembers2322 : Finset ℕ := ([132,252,1590,1626,1642,1692,1708,1720,1748,1764,1776,2606,2618,2646,2662,2674,2740,2764,2776,2792,3126,3162,3178,3244,3256,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2322 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2322 5 (fun x => (if x<2662 then (if x<1720 then (if x<1626 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1692 then (if x<1642 then 1 else 2) else (if x<1708 then 0 else 2))) else (if x<1776 then (if x<1748 then 1 else (if x<1764 then 1 else 0)) else (if x<2618 then (if x<2606 then 2 else 2) else (if x<2646 then 1 else 1)))) else (if x<3162 then (if x<2764 then (if x<2674 then 3 else (if x<2740 then 2 else 0)) else (if x<2792 then (if x<2776 then 0 else 1) else (if x<3126 then 2 else 3))) else (if x<3256 then (if x<3178 then 4 else (if x<3244 then 3 else 0)) else (if x<3300 then (if x<3284 then 3 else 0) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2323 : Finset ℕ := ([132,252,1626,1642,1720,1776,2618,2674,2776,2792,3126,3244,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2323 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2323 4 (fun x => (if x<2674 then (if x<1642 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1776 then (if x<1720 then 2 else 1) else (if x<2618 then 2 else 1))) else (if x<3126 then (if x<2776 then 2 else (if x<2792 then 1 else 2)) else (if x<3284 then (if x<3244 then 3 else 0) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2324 : Finset ℕ := ([132,252,1590,1614,1626,1642,1692,1708,1720,1748,1764,1776,2606,2618,2646,2662,2674,2740,2764,2776,2792,3126,3162,3178,3244,3256,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2324 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2324 1614 4
  · have he : independentCachedBranchMembers2324.erase 1614=independentCachedBranchMembers2322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2322
  · have he : independentCachedBranchMembers2324.filter (independentCachedEdge 1614)=independentCachedBranchMembers2323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2323
def independentCachedBranchMembers2325 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2614,2618,2638,2646,2650,2662,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3158,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2325 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2325 2614 5
  · have he : independentCachedBranchMembers2325.erase 2614=independentCachedBranchMembers2321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2321
  · have he : independentCachedBranchMembers2325.filter (independentCachedEdge 2614)=independentCachedBranchMembers2324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2324
def independentCachedBranchMembers2326 : Finset ℕ := ([132,252,1590,1614,1626,1650,1708,1720,1748,1768,2618,2646,2716,2740,2764,2800,3158,3178,3252,3276,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2326 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2326 5 (fun x => (if x<2646 then (if x<1650 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1614 then 1 else (if x<1626 then 1 else 2))) else (if x<1748 then (if x<1708 then 3 else (if x<1720 then 0 else 2)) else (if x<1768 then 0 else (if x<2618 then 3 else 2)))) else (if x<3158 then (if x<2740 then (if x<2716 then 1 else 0) else (if x<2764 then 1 else (if x<2800 then 1 else 3))) else (if x<3276 then (if x<3178 then 4 else (if x<3252 then 4 else 0)) else (if x<3288 then 0 else (if x<3300 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2327 : Finset ℕ := ([132,1590,1626,1708,2618,2646,2716,2764,2800,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2327 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2327 4 (fun x => (if x<2716 then (if x<1708 then (if x<1590 then 0 else (if x<1626 then 1 else 0)) else (if x<2618 then 1 else (if x<2646 then 0 else 1))) else (if x<3252 then (if x<2764 then 2 else (if x<2800 then 1 else 2)) else (if x<3288 then 2 else (if x<3300 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2328 : Finset ℕ := ([132,252,1590,1614,1626,1650,1708,1720,1748,1768,2618,2646,2716,2740,2764,2800,3158,3178,3252,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2328 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2328 3312 4
  · have he : independentCachedBranchMembers2328.erase 3312=independentCachedBranchMembers2326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2326
  · have he : independentCachedBranchMembers2328.filter (independentCachedEdge 3312)=independentCachedBranchMembers2327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2327
def independentCachedBranchMembers2329 : Finset ℕ := ([252,1614,1708,1768,2618,2646,2716,2740,2800,3178,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2329 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2329 4 (fun x => (if x<2716 then (if x<1768 then (if x<1614 then 0 else (if x<1708 then 1 else 0)) else (if x<2618 then 1 else (if x<2646 then 2 else 1))) else (if x<3178 then (if x<2740 then 0 else (if x<2800 then 2 else 1)) else (if x<3276 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2330 : Finset ℕ := ([132,252,1590,1614,1626,1650,1708,1720,1748,1768,2618,2646,2716,2740,2764,2800,3130,3158,3178,3252,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2330 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2330 3130 4
  · have he : independentCachedBranchMembers2330.erase 3130=independentCachedBranchMembers2328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2328
  · have he : independentCachedBranchMembers2330.filter (independentCachedEdge 3130)=independentCachedBranchMembers2329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2329
def independentCachedBranchMembers2331 : Finset ℕ := ([1590,1614,1650,1720,2618,2740,2764,2800,3158,3178,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2331 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2331 4 (fun x => (if x<2764 then (if x<1720 then (if x<1614 then 0 else (if x<1650 then 0 else 1)) else (if x<2618 then 1 else (if x<2740 then 1 else 0))) else (if x<3178 then (if x<2800 then 0 else (if x<3158 then 1 else 2)) else (if x<3288 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2332 : Finset ℕ := ([132,252,1590,1614,1626,1650,1708,1720,1748,1768,2618,2646,2716,2740,2764,2788,2800,3130,3158,3178,3252,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2332 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2332 2788 4
  · have he : independentCachedBranchMembers2332.erase 2788=independentCachedBranchMembers2330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2330
  · have he : independentCachedBranchMembers2332.filter (independentCachedEdge 2788)=independentCachedBranchMembers2331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2331
def independentCachedBranchMembers2333 : Finset ℕ := ([132,252,1626,1650,1720,1768,2618,2800,3158,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2333 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2333 4 (fun x => (if x<2618 then (if x<1650 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1720 then 2 else (if x<1768 then 1 else 2))) else (if x<3252 then (if x<2800 then 1 else (if x<3158 then 2 else 3)) else (if x<3276 then 0 else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2334 : Finset ℕ := ([132,252,1590,1614,1626,1650,1708,1720,1748,1768,2606,2618,2646,2716,2740,2764,2788,2800,3130,3158,3178,3252,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2334 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2334 2606 4
  · have he : independentCachedBranchMembers2334.erase 2606=independentCachedBranchMembers2332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2332
  · have he : independentCachedBranchMembers2334.filter (independentCachedEdge 2606)=independentCachedBranchMembers2333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2333
def independentCachedBranchMembers2335 : Finset ℕ := ([132,1614,1626,1650,1708,1720,2646,2716,2740,3158,3178,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2335 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2335 4 (fun x => (if x<2646 then (if x<1650 then (if x<1614 then 0 else (if x<1626 then 1 else 0)) else (if x<1708 then 1 else (if x<1720 then 2 else 3))) else (if x<3158 then (if x<2716 then 1 else (if x<2740 then 2 else 0)) else (if x<3178 then 3 else (if x<3252 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2336 : Finset ℕ := ([132,192,252,1590,1614,1626,1650,1708,1720,1748,1768,2606,2618,2646,2716,2740,2764,2788,2800,3130,3158,3178,3252,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2336 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2336 192 4
  · have he : independentCachedBranchMembers2336.erase 192=independentCachedBranchMembers2334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2334
  · have he : independentCachedBranchMembers2336.filter (independentCachedEdge 192)=independentCachedBranchMembers2335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2335
def independentCachedBranchMembers2337 : Finset ℕ := ([132,1614,1650,1708,2716,2764,2800,3158,3178,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2337 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2337 4 (fun x => (if x<2800 then (if x<1708 then (if x<1614 then 0 else (if x<1650 then 1 else 0)) else (if x<2716 then 1 else (if x<2764 then 0 else 1))) else (if x<3252 then (if x<3158 then 2 else (if x<3178 then 3 else 0)) else (if x<3288 then 2 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2338 : Finset ℕ := ([1614,1708,2716,2800,3178,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2338 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2338 3 (fun x => (if x<2800 then (if x<1708 then 0 else (if x<2716 then 0 else 1)) else (if x<3178 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2339 : Finset ℕ := ([132,1614,1650,1708,2716,2764,2800,3130,3158,3178,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2339 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2339 3130 3
  · have he : independentCachedBranchMembers2339.erase 3130=independentCachedBranchMembers2337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2337
  · have he : independentCachedBranchMembers2339.filter (independentCachedEdge 3130)=independentCachedBranchMembers2338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2338
def independentCachedBranchMembers2340 : Finset ℕ := ([132,1650,2800,3158,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2340 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2340 3 (fun x => (if x<3158 then (if x<1650 then 0 else (if x<2800 then 0 else 1)) else (if x<3252 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2341 : Finset ℕ := ([132,1614,1650,1708,2606,2716,2764,2800,3130,3158,3178,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2341 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2341 2606 3
  · have he : independentCachedBranchMembers2341.erase 2606=independentCachedBranchMembers2339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2339
  · have he : independentCachedBranchMembers2341.filter (independentCachedEdge 2606)=independentCachedBranchMembers2340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2340
def independentCachedBranchMembers2342 : Finset ℕ := ([132,192,252,1590,1614,1626,1650,1708,1720,1748,1768,2606,2618,2646,2716,2740,2764,2776,2788,2800,3130,3158,3178,3252,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2342 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2342 2776 4
  · have he : independentCachedBranchMembers2342.erase 2776=independentCachedBranchMembers2336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2336
  · have he : independentCachedBranchMembers2342.filter (independentCachedEdge 2776)=independentCachedBranchMembers2341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2341
def independentCachedBranchMembers2343 : Finset ℕ := ([252,1626,1650,1720,1768,2606,2646,2716,2740,2764,2788,3130,3178,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2343 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2343 4 (fun x => (if x<2716 then (if x<1720 then (if x<1626 then 0 else (if x<1650 then 1 else 2)) else (if x<2606 then (if x<1768 then 0 else 1) else (if x<2646 then 3 else 1))) else (if x<3130 then (if x<2764 then (if x<2740 then 0 else 3) else (if x<2788 then 2 else 1)) else (if x<3288 then (if x<3178 then 2 else 3) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2344 : Finset ℕ := ([1720,1768,2606,2646,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2344 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2344 3 (fun x => (if x<2646 then (if x<1768 then 0 else (if x<2606 then 1 else 2)) else (if x<3288 then 0 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2345 : Finset ℕ := ([132,252,1626,1650,1720,1768,2606,2646,2716,2740,2764,2788,3130,3178,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2345 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2345 132 3
  · have he : independentCachedBranchMembers2345.erase 132=independentCachedBranchMembers2343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2343
  · have he : independentCachedBranchMembers2345.filter (independentCachedEdge 132)=independentCachedBranchMembers2344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2344
def independentCachedBranchMembers2346 : Finset ℕ := ([132,192,252,1590,1614,1626,1650,1708,1720,1748,1768,2606,2618,2646,2716,2740,2764,2776,2788,2800,3118,3130,3158,3178,3252,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2346 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2346 3118 4
  · have he : independentCachedBranchMembers2346.erase 3118=independentCachedBranchMembers2342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2342
  · have he : independentCachedBranchMembers2346.filter (independentCachedEdge 3118)=independentCachedBranchMembers2345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2345
def independentCachedBranchMembers2347 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1622,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2614,2618,2638,2646,2650,2662,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3158,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2347 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2347 1622 5
  · have he : independentCachedBranchMembers2347.erase 1622=independentCachedBranchMembers2325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2325
  · have he : independentCachedBranchMembers2347.filter (independentCachedEdge 1622)=independentCachedBranchMembers2346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2346
def independentCachedBranchMembers2348 : Finset ℕ := ([132,252,1590,1594,1614,1642,1708,1748,1752,1776,2606,2650,2716,2740,2764,2792,3118,3186,3252,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2348 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2348 5 (fun x => (if x<2650 then (if x<1642 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1594 then 1 else (if x<1614 then 2 else 1))) else (if x<1752 then (if x<1708 then 3 else (if x<1748 then 0 else 0)) else (if x<1776 then 2 else (if x<2606 then 3 else 1)))) else (if x<3118 then (if x<2740 then (if x<2716 then 2 else 0) else (if x<2764 then 1 else (if x<2792 then 1 else 3))) else (if x<3256 then (if x<3186 then 4 else (if x<3252 then 4 else 0)) else (if x<3276 then 4 else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2349 : Finset ℕ := ([132,1594,1614,1748,2606,2650,2716,2740,2792,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2349 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2349 4 (fun x => (if x<2716 then (if x<1748 then (if x<1594 then 0 else (if x<1614 then 0 else 1)) else (if x<2606 then 1 else (if x<2650 then 1 else 0))) else (if x<3256 then (if x<2740 then 2 else (if x<2792 then 1 else 2)) else (if x<3276 then 2 else (if x<3300 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2350 : Finset ℕ := ([132,252,1590,1594,1614,1642,1708,1748,1752,1776,2606,2650,2716,2740,2764,2792,3118,3186,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2350 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2350 3304 4
  · have he : independentCachedBranchMembers2350.erase 3304=independentCachedBranchMembers2348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2348
  · have he : independentCachedBranchMembers2350.filter (independentCachedEdge 3304)=independentCachedBranchMembers2349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2349
def independentCachedBranchMembers2351 : Finset ℕ := ([252,1590,1748,1776,2606,2650,2716,2764,2792,3186,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2351 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2351 4 (fun x => (if x<2716 then (if x<1776 then (if x<1590 then 0 else (if x<1748 then 1 else 0)) else (if x<2606 then 1 else (if x<2650 then 1 else 2))) else (if x<3186 then (if x<2764 then 0 else (if x<2792 then 2 else 1)) else (if x<3252 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2352 : Finset ℕ := ([132,252,1590,1594,1614,1642,1708,1748,1752,1776,2606,2650,2716,2740,2764,2792,3118,3162,3186,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2352 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2352 3162 4
  · have he : independentCachedBranchMembers2352.erase 3162=independentCachedBranchMembers2350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2350
  · have he : independentCachedBranchMembers2352.filter (independentCachedEdge 3162)=independentCachedBranchMembers2351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2351
def independentCachedBranchMembers2353 : Finset ℕ := ([1590,1614,1642,1752,2650,2740,2764,2792,3118,3186,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2353 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2353 4 (fun x => (if x<2764 then (if x<1752 then (if x<1614 then 0 else (if x<1642 then 0 else 1)) else (if x<2650 then 1 else (if x<2740 then 1 else 0))) else (if x<3186 then (if x<2792 then 0 else (if x<3118 then 1 else 2)) else (if x<3256 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2354 : Finset ℕ := ([132,252,1590,1594,1614,1642,1708,1748,1752,1776,2606,2650,2716,2740,2764,2788,2792,3118,3162,3186,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2354 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2354 2788 4
  · have he : independentCachedBranchMembers2354.erase 2788=independentCachedBranchMembers2352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2352
  · have he : independentCachedBranchMembers2354.filter (independentCachedEdge 2788)=independentCachedBranchMembers2353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2353
def independentCachedBranchMembers2355 : Finset ℕ := ([132,252,1594,1642,1752,1776,2650,2792,3118,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2355 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2355 4 (fun x => (if x<2650 then (if x<1642 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1752 then 2 else (if x<1776 then 1 else 2))) else (if x<3252 then (if x<2792 then 1 else (if x<3118 then 2 else 3)) else (if x<3276 then 0 else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2356 : Finset ℕ := ([132,252,1590,1594,1614,1642,1708,1748,1752,1776,2606,2646,2650,2716,2740,2764,2788,2792,3118,3162,3186,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2356 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2356 2646 4
  · have he : independentCachedBranchMembers2356.erase 2646=independentCachedBranchMembers2354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2354
  · have he : independentCachedBranchMembers2356.filter (independentCachedEdge 2646)=independentCachedBranchMembers2355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2355
def independentCachedBranchMembers2357 : Finset ℕ := ([252,1614,1642,1748,1752,1776,2606,2716,2740,3118,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2357 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2357 4 (fun x => (if x<2606 then (if x<1748 then (if x<1614 then 0 else (if x<1642 then 1 else 2)) else (if x<1752 then 0 else (if x<1776 then 1 else 2))) else (if x<3118 then (if x<2716 then 1 else (if x<2740 then 0 else 2)) else (if x<3252 then 3 else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2358 : Finset ℕ := ([18,132,252,1590,1594,1614,1642,1708,1748,1752,1776,2606,2646,2650,2716,2740,2764,2788,2792,3118,3162,3186,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2358 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2358 18 4
  · have he : independentCachedBranchMembers2358.erase 18=independentCachedBranchMembers2356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2356
  · have he : independentCachedBranchMembers2358.filter (independentCachedEdge 18)=independentCachedBranchMembers2357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2357
def independentCachedBranchMembers2359 : Finset ℕ := ([252,1614,1748,1752,2650,2716,2764,3118,3186,3252,3256,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2359 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2359 4 (fun x => (if x<2764 then (if x<1752 then (if x<1614 then 0 else (if x<1748 then 1 else 0)) else (if x<2650 then 1 else (if x<2716 then 1 else 0))) else (if x<3252 then (if x<3118 then 1 else (if x<3186 then 2 else 2)) else (if x<3300 then (if x<3256 then 0 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2360 : Finset ℕ := ([252,1752,2650,3118,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2360 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2360 3 (fun x => (if x<3118 then (if x<1752 then 0 else (if x<2650 then 0 else 1)) else (if x<3252 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2361 : Finset ℕ := ([252,1614,1748,1752,2646,2650,2716,2764,3118,3186,3252,3256,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2361 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2361 2646 3
  · have he : independentCachedBranchMembers2361.erase 2646=independentCachedBranchMembers2359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2359
  · have he : independentCachedBranchMembers2361.filter (independentCachedEdge 2646)=independentCachedBranchMembers2360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2360
def independentCachedBranchMembers2362 : Finset ℕ := ([18,132,252,1590,1594,1614,1642,1708,1748,1752,1776,2606,2646,2650,2674,2716,2740,2764,2788,2792,3118,3162,3186,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2362 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2362 2674 4
  · have he : independentCachedBranchMembers2362.erase 2674=independentCachedBranchMembers2358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2358
  · have he : independentCachedBranchMembers2362.filter (independentCachedEdge 2674)=independentCachedBranchMembers2361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2361
def independentCachedBranchMembers2363 : Finset ℕ := ([252,1594,1642,1752,1776,2606,2646,2716,2740,2764,2788,3162,3186,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2363 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2363 4 (fun x => (if x<2716 then (if x<1752 then (if x<1594 then 0 else (if x<1642 then 1 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2646 then 1 else 3))) else (if x<3162 then (if x<2764 then (if x<2740 then 0 else 2) else (if x<2788 then 3 else 1)) else (if x<3256 then (if x<3186 then 2 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2364 : Finset ℕ := ([1752,1776,2606,2646,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2364 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2364 3 (fun x => (if x<2646 then (if x<1776 then 0 else (if x<2606 then 1 else 0)) else (if x<3256 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2365 : Finset ℕ := ([132,252,1594,1642,1752,1776,2606,2646,2716,2740,2764,2788,3162,3186,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2365 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2365 132 3
  · have he : independentCachedBranchMembers2365.erase 132=independentCachedBranchMembers2363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2363
  · have he : independentCachedBranchMembers2365.filter (independentCachedEdge 132)=independentCachedBranchMembers2364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2364
def independentCachedBranchMembers2366 : Finset ℕ := ([18,132,252,1590,1594,1614,1642,1708,1748,1752,1776,2606,2646,2650,2674,2716,2740,2764,2788,2792,3118,3158,3162,3186,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2366 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2366 3158 4
  · have he : independentCachedBranchMembers2366.erase 3158=independentCachedBranchMembers2362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2362
  · have he : independentCachedBranchMembers2366.filter (independentCachedEdge 3158)=independentCachedBranchMembers2365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2365
def independentCachedBranchMembers2367 : Finset ℕ := ([18,132,192,252,1582,1590,1594,1614,1622,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2614,2618,2638,2646,2650,2662,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3158,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2367 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2367 1582 5
  · have he : independentCachedBranchMembers2367.erase 1582=independentCachedBranchMembers2347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2347
  · have he : independentCachedBranchMembers2367.filter (independentCachedEdge 1582)=independentCachedBranchMembers2366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2366
def independentCachedBranchMembers2368 : Finset ℕ := ([18,192,1582,1594,1622,1626,1692,1764,1768,1776,2614,2618,2638,2650,2716,2788,2792,2800,3102,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2368 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2368 5 (fun x => (if x<2650 then (if x<1692 then (if x<1594 then (if x<192 then 0 else (if x<1582 then 0 else 1)) else (if x<1622 then 0 else (if x<1626 then 1 else 2))) else (if x<1776 then (if x<1764 then 1 else (if x<1768 then 1 else 0)) else (if x<2618 then (if x<2614 then 2 else 0) else (if x<2638 then 3 else 2)))) else (if x<3186 then (if x<2792 then (if x<2716 then 4 else (if x<2788 then 3 else 0)) else (if x<3102 then (if x<2800 then 3 else 4) else (if x<3178 then 0 else 3))) else (if x<3256 then (if x<3244 then 4 else (if x<3252 then 1 else 2)) else (if x<3284 then (if x<3276 then 3 else 0) else (if x<3288 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2369 : Finset ℕ := ([1582,1594,1622,1768,2614,2650,2716,2800,3178,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2369 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2369 4 (fun x => (if x<2716 then (if x<1768 then (if x<1594 then 0 else (if x<1622 then 1 else 0)) else (if x<2614 then 1 else (if x<2650 then 0 else 2))) else (if x<3244 then (if x<2800 then 2 else (if x<3178 then 2 else 1)) else (if x<3256 then 3 else (if x<3284 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2370 : Finset ℕ := ([1582,1622,2650,2800,3178,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2370 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2370 3 (fun x => (if x<2800 then (if x<1622 then 0 else (if x<2650 then 0 else 1)) else (if x<3178 then 1 else (if x<3256 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2371 : Finset ℕ := ([1582,1594,1622,1768,2614,2650,2716,2788,2800,3178,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2371 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2371 2788 3
  · have he : independentCachedBranchMembers2371.erase 2788=independentCachedBranchMembers2369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2369
  · have he : independentCachedBranchMembers2371.filter (independentCachedEdge 2788)=independentCachedBranchMembers2370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2370
def independentCachedBranchMembers2372 : Finset ℕ := ([1594,1768,2650,2800,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2372 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2372 3 (fun x => (if x<2800 then (if x<1768 then 0 else (if x<2650 then 0 else 1)) else (if x<3244 then 1 else (if x<3284 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2373 : Finset ℕ := ([1582,1594,1622,1768,2614,2638,2650,2716,2788,2800,3178,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2373 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2373 2638 3
  · have he : independentCachedBranchMembers2373.erase 2638=independentCachedBranchMembers2371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2371
  · have he : independentCachedBranchMembers2373.filter (independentCachedEdge 2638)=independentCachedBranchMembers2372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2372
def independentCachedBranchMembers2374 : Finset ℕ := ([18,192,1582,1590,1594,1622,1626,1692,1764,1768,1776,2614,2618,2638,2650,2716,2788,2792,2800,3102,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2374 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2374 1590 4
  · have he : independentCachedBranchMembers2374.erase 1590=independentCachedBranchMembers2368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2368
  · have he : independentCachedBranchMembers2374.filter (independentCachedEdge 1590)=independentCachedBranchMembers2373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2373
def independentCachedBranchMembers2375 : Finset ℕ := ([192,1582,1594,1622,1692,1764,1776,2614,2638,2650,2792,3178,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2375 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2375 4 (fun x => (if x<2614 then (if x<1622 then (if x<1582 then 0 else (if x<1594 then 0 else 1)) else (if x<1764 then (if x<1692 then 1 else 1) else (if x<1776 then 0 else 1))) else (if x<3178 then (if x<2650 then (if x<2638 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3276 then (if x<3252 then 3 else 2) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2376 : Finset ℕ := ([18,192,1582,1590,1594,1622,1626,1692,1764,1768,1776,2614,2618,2638,2646,2650,2716,2788,2792,2800,3102,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2376 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2376 2646 4
  · have he : independentCachedBranchMembers2376.erase 2646=independentCachedBranchMembers2374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2374
  · have he : independentCachedBranchMembers2376.filter (independentCachedEdge 2646)=independentCachedBranchMembers2375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2375
def independentCachedBranchMembers2377 : Finset ℕ := ([18,1582,1622,1626,1692,1764,1768,2614,2618,2638,2800,3186,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2377 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2377 4 (fun x => (if x<2614 then (if x<1626 then (if x<1582 then 0 else (if x<1622 then 1 else 0)) else (if x<1764 then (if x<1692 then 1 else 1) else (if x<1768 then 0 else 1))) else (if x<3186 then (if x<2638 then (if x<2618 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3256 then (if x<3252 then 3 else 2) else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2378 : Finset ℕ := ([18,192,1582,1590,1594,1622,1626,1692,1764,1768,1776,2606,2614,2618,2638,2646,2650,2716,2788,2792,2800,3102,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2378 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2378 2606 4
  · have he : independentCachedBranchMembers2378.erase 2606=independentCachedBranchMembers2376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2376
  · have he : independentCachedBranchMembers2378.filter (independentCachedEdge 2606)=independentCachedBranchMembers2377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2377
def independentCachedBranchMembers2379 : Finset ℕ := ([192,1582,1622,1626,1776,2614,2618,2638,2716,2788,2792,3186,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2379 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2379 4 (fun x => (if x<2638 then (if x<1626 then (if x<1582 then 0 else (if x<1622 then 0 else 1)) else (if x<2614 then (if x<1776 then 2 else 1) else (if x<2618 then 0 else 2))) else (if x<3186 then (if x<2788 then (if x<2716 then 1 else 3) else (if x<2792 then 3 else 1)) else (if x<3284 then (if x<3244 then 2 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2380 : Finset ℕ := ([1582,1776,2638,2716,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2380 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2380 3 (fun x => (if x<2716 then (if x<1776 then 0 else (if x<2638 then 1 else 0)) else (if x<3284 then 2 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2381 : Finset ℕ := ([18,192,1582,1622,1626,1776,2614,2618,2638,2716,2788,2792,3186,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2381 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2381 18 3
  · have he : independentCachedBranchMembers2381.erase 18=independentCachedBranchMembers2379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2379
  · have he : independentCachedBranchMembers2381.filter (independentCachedEdge 18)=independentCachedBranchMembers2380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2380
def independentCachedBranchMembers2382 : Finset ℕ := ([18,192,1582,1590,1594,1614,1622,1626,1692,1764,1768,1776,2606,2614,2618,2638,2646,2650,2716,2788,2792,2800,3102,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2382 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2382 1614 4
  · have he : independentCachedBranchMembers2382.erase 1614=independentCachedBranchMembers2378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2378
  · have he : independentCachedBranchMembers2382.filter (independentCachedEdge 1614)=independentCachedBranchMembers2381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2381
def independentCachedBranchMembers2383 : Finset ℕ := ([18,132,192,252,1582,1590,1594,1614,1622,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2614,2618,2638,2646,2650,2662,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3158,3162,3178,3186,3228,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2383 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2383 3228 5
  · have he : independentCachedBranchMembers2383.erase 3228=independentCachedBranchMembers2367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2367
  · have he : independentCachedBranchMembers2383.filter (independentCachedEdge 3228)=independentCachedBranchMembers2382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2382
def independentCachedBranchMembers2384 : Finset ℕ := ([132,192,252,1594,1614,1650,1708,1748,1752,1764,1768,2614,2618,2638,2716,2732,2772,2788,2792,3102,3118,3158,3162,3178,3252,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2384 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2384 5 (fun x => (if x<2716 then (if x<1748 then (if x<1594 then (if x<192 then 0 else (if x<252 then 1 else 0)) else (if x<1650 then (if x<1614 then 1 else 2) else (if x<1708 then 2 else 0))) else (if x<1768 then (if x<1752 then 0 else (if x<1764 then 1 else 2)) else (if x<2618 then (if x<2614 then 3 else 1) else (if x<2638 then 4 else 4)))) else (if x<3158 then (if x<2788 then (if x<2732 then 0 else (if x<2772 then 3 else 1)) else (if x<3102 then (if x<2792 then 0 else 4) else (if x<3118 then 4 else 1))) else (if x<3252 then (if x<3162 then 3 else (if x<3178 then 2 else 4)) else (if x<3276 then (if x<3256 then 0 else 4) else (if x<3312 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2385 : Finset ℕ := ([252,1614,1748,1752,2638,2716,2772,3118,3178,3252,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2385 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2385 4 (fun x => (if x<2772 then (if x<1752 then (if x<1614 then 0 else (if x<1748 then 1 else 0)) else (if x<2638 then 1 else (if x<2716 then 2 else 0))) else (if x<3252 then (if x<3118 then 2 else (if x<3178 then 1 else 2)) else (if x<3256 then 0 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2386 : Finset ℕ := ([18,132,192,252,1594,1614,1650,1708,1748,1752,1764,1768,2614,2618,2638,2716,2732,2772,2788,2792,3102,3118,3158,3162,3178,3252,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2386 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2386 18 4
  · have he : independentCachedBranchMembers2386.erase 18=independentCachedBranchMembers2384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2384
  · have he : independentCachedBranchMembers2386.filter (independentCachedEdge 18)=independentCachedBranchMembers2385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2385
def independentCachedBranchMembers2387 : Finset ℕ := ([18,132,1594,1614,1650,1708,1752,1764,2614,2716,2772,2792,3102,3158,3178,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2387 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2387 4 (fun x => (if x<2614 then (if x<1650 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1614 then 0 else 1)) else (if x<1752 then (if x<1708 then 1 else 0) else (if x<1764 then 1 else 1))) else (if x<3102 then (if x<2772 then (if x<2716 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3178 then (if x<3158 then 2 else 3) else (if x<3252 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2388 : Finset ℕ := ([18,132,192,252,1594,1614,1650,1708,1748,1752,1764,1768,2614,2618,2638,2716,2732,2772,2776,2788,2792,3102,3118,3158,3162,3178,3252,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2388 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2388 2776 4
  · have he : independentCachedBranchMembers2388.erase 2776=independentCachedBranchMembers2386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2386
  · have he : independentCachedBranchMembers2388.filter (independentCachedEdge 2776)=independentCachedBranchMembers2387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2387
def independentCachedBranchMembers2389 : Finset ℕ := ([192,252,1614,1650,1748,1752,1764,1768,2614,2618,2716,2732,3102,3118,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2389 4 (fun x => (if x<2614 then (if x<1748 then (if x<1614 then (if x<252 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1764 then (if x<1752 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3102 then (if x<2716 then (if x<2618 then 2 else 3) else (if x<2732 then 2 else 3)) else (if x<3252 then (if x<3118 then 2 else 3) else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2390 : Finset ℕ := ([18,132,192,252,1594,1614,1650,1708,1748,1752,1764,1768,2614,2618,2638,2674,2716,2732,2772,2776,2788,2792,3102,3118,3158,3162,3178,3252,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2390 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2390 2674 4
  · have he : independentCachedBranchMembers2390.erase 2674=independentCachedBranchMembers2388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2388
  · have he : independentCachedBranchMembers2390.filter (independentCachedEdge 2674)=independentCachedBranchMembers2389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2389
def independentCachedBranchMembers2391 : Finset ℕ := ([192,1650,1708,1748,1752,2614,2618,2638,2716,2788,2792,3118,3158,3162,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2391 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2391 4 (fun x => (if x<2638 then (if x<1748 then (if x<1650 then 0 else (if x<1708 then 1 else 2)) else (if x<2614 then (if x<1752 then 0 else 1) else (if x<2618 then 1 else 0))) else (if x<3118 then (if x<2788 then (if x<2716 then 3 else 1) else (if x<2792 then 2 else 3)) else (if x<3162 then (if x<3158 then 0 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2392 : Finset ℕ := ([1748,1752,2638,2716,3118,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2392 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2392 3 (fun x => (if x<2716 then (if x<1752 then 0 else (if x<2638 then 1 else 2)) else (if x<3118 then 0 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2393 : Finset ℕ := ([18,192,1650,1708,1748,1752,2614,2618,2638,2716,2788,2792,3118,3158,3162,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2393 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2393 18 3
  · have he : independentCachedBranchMembers2393.erase 18=independentCachedBranchMembers2391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2391
  · have he : independentCachedBranchMembers2393.filter (independentCachedEdge 18)=independentCachedBranchMembers2392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2392
def independentCachedBranchMembers2394 : Finset ℕ := ([18,132,192,252,1594,1614,1650,1692,1708,1748,1752,1764,1768,2614,2618,2638,2674,2716,2732,2772,2776,2788,2792,3102,3118,3158,3162,3178,3252,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2394 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2394 1692 4
  · have he : independentCachedBranchMembers2394.erase 1692=independentCachedBranchMembers2390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2390
  · have he : independentCachedBranchMembers2394.filter (independentCachedEdge 1692)=independentCachedBranchMembers2393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2393
def independentCachedBranchMembers2395 : Finset ℕ := ([252,1594,1650,1752,1768,2614,2638,2716,2732,2772,2788,3162,3178,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2395 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2395 4 (fun x => (if x<2716 then (if x<1752 then (if x<1594 then 0 else (if x<1650 then 1 else 2)) else (if x<2614 then (if x<1768 then 0 else 1) else (if x<2638 then 1 else 3))) else (if x<3162 then (if x<2772 then (if x<2732 then 0 else 2) else (if x<2788 then 3 else 1)) else (if x<3256 then (if x<3178 then 2 else 3) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2396 : Finset ℕ := ([1752,1768,2614,2638,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2396 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2396 3 (fun x => (if x<2638 then (if x<1768 then 0 else (if x<2614 then 1 else 0)) else (if x<3256 then 2 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2397 : Finset ℕ := ([132,252,1594,1650,1752,1768,2614,2638,2716,2732,2772,2788,3162,3178,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2397 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2397 132 3
  · have he : independentCachedBranchMembers2397.erase 132=independentCachedBranchMembers2395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2395
  · have he : independentCachedBranchMembers2397.filter (independentCachedEdge 132)=independentCachedBranchMembers2396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2396
def independentCachedBranchMembers2398 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,2614,2618,2638,2674,2716,2732,2772,2776,2788,2792,3102,3118,3158,3162,3178,3252,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2398 1590 4
  · have he : independentCachedBranchMembers2398.erase 1590=independentCachedBranchMembers2394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2394
  · have he : independentCachedBranchMembers2398.filter (independentCachedEdge 1590)=independentCachedBranchMembers2397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2397
def independentCachedBranchMembers2399 : Finset ℕ := ([18,132,192,252,1582,1590,1594,1614,1622,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2614,2618,2638,2646,2650,2662,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3150,3158,3162,3178,3186,3228,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2399 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2399 3150 5
  · have he : independentCachedBranchMembers2399.erase 3150=independentCachedBranchMembers2383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2383
  · have he : independentCachedBranchMembers2399.filter (independentCachedEdge 3150)=independentCachedBranchMembers2398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2398
def independentCachedBranchMembers2400 : Finset ℕ := ([12,18,48,72,130,132,192,222,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2400 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2400 130 6
  · have he : independentCachedBranchMembers2400.erase 130=independentCachedBranchMembers2256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2256
  · have he : independentCachedBranchMembers2400.filter (independentCachedEdge 130)=independentCachedBranchMembers2399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2399
def independentCachedBranchMembers2401 : Finset ℕ := ([18,192,1594,1596,1614,1686,1714,1738,1764,1768,2614,2618,2668,2714,2740,2758,2764,2786,2792,3102,3126,3178,3250,3256,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2401 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2401 6 (fun x => (if x<2714 then (if x<1714 then (if x<1596 then (if x<192 then 0 else (if x<1594 then 0 else 0)) else (if x<1614 then 1 else (if x<1686 then 1 else 1))) else (if x<1768 then (if x<1738 then 2 else (if x<1764 then 2 else 1)) else (if x<2618 then (if x<2614 then 0 else 0) else (if x<2668 then 3 else 1)))) else (if x<3126 then (if x<2764 then (if x<2740 then 2 else (if x<2758 then 1 else 1)) else (if x<2792 then (if x<2786 then 2 else 2) else (if x<3102 then 3 else 0))) else (if x<3256 then (if x<3178 then 3 else (if x<3250 then 3 else 4)) else (if x<3276 then (if x<3274 then 3 else 4) else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2402 : Finset ℕ := ([192,1594,1596,1764,2618,2714,2758,2786,3102,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2402 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2402 5 (fun x => (if x<2714 then (if x<1596 then (if x<1594 then 0 else 0) else (if x<1764 then 1 else (if x<2618 then 1 else 1))) else (if x<3102 then (if x<2758 then 2 else (if x<2786 then 0 else 1)) else (if x<3256 then 1 else (if x<3300 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2403 : Finset ℕ := ([18,72,192,1594,1596,1614,1686,1714,1738,1764,1768,2614,2618,2668,2714,2740,2758,2764,2786,2792,3102,3126,3178,3250,3256,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2403 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2403 72 5
  · have he : independentCachedBranchMembers2403.erase 72=independentCachedBranchMembers2401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2401
  · have he : independentCachedBranchMembers2403.filter (independentCachedEdge 72)=independentCachedBranchMembers2402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2402
def independentCachedBranchMembers2404 : Finset ℕ := ([18,1686,1764,1768,2668,2714,2786,2792,3102,3178,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2404 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2404 5 (fun x => (if x<2714 then (if x<1764 then (if x<1686 then 0 else 0) else (if x<1768 then 0 else (if x<2668 then 1 else 0))) else (if x<3102 then (if x<2786 then 2 else (if x<2792 then 1 else 2)) else (if x<3178 then 1 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2405 : Finset ℕ := ([18,48,72,192,1594,1596,1614,1686,1714,1738,1764,1768,2614,2618,2668,2714,2740,2758,2764,2786,2792,3102,3126,3178,3250,3256,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2405 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2405 48 5
  · have he : independentCachedBranchMembers2405.erase 48=independentCachedBranchMembers2403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2403
  · have he : independentCachedBranchMembers2405.filter (independentCachedEdge 48)=independentCachedBranchMembers2404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2404
def independentCachedBranchMembers2406 : Finset ℕ := ([18,72,1714,1768,2614,2668,2714,2740,2758,2792,3256,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2406 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2406 5 (fun x => (if x<2740 then (if x<1768 then (if x<72 then 0 else (if x<1714 then 0 else 0)) else (if x<2668 then (if x<2614 then 0 else 0) else (if x<2714 then 0 else 1))) else (if x<3256 then (if x<2758 then 1 else (if x<2792 then 1 else 1)) else (if x<3276 then (if x<3274 then 1 else 1) else (if x<3300 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2407 : Finset ℕ := ([18,48,72,192,1594,1596,1614,1686,1714,1738,1764,1768,2614,2618,2668,2714,2740,2758,2764,2786,2792,3102,3126,3178,3250,3256,3270,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2407 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2407 3270 5
  · have he : independentCachedBranchMembers2407.erase 3270=independentCachedBranchMembers2405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2405
  · have he : independentCachedBranchMembers2407.filter (independentCachedEdge 3270)=independentCachedBranchMembers2406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2406
def independentCachedBranchMembers2408 : Finset ℕ := ([48,192,1594,1738,2614,2618,2668,2740,2758,2786,3178,3250,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2408 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2408 5 (fun x => (if x<2740 then (if x<1738 then (if x<192 then 0 else (if x<1594 then 0 else 0)) else (if x<2618 then (if x<2614 then 0 else 0) else (if x<2668 then 1 else 1))) else (if x<3178 then (if x<2758 then 1 else (if x<2786 then 0 else 1)) else (if x<3276 then (if x<3250 then 1 else 1) else (if x<3300 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2409 : Finset ℕ := ([18,48,72,192,1594,1596,1614,1686,1714,1738,1764,1768,2614,2618,2668,2714,2740,2758,2764,2786,2792,3102,3126,3178,3180,3250,3256,3270,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2409 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2409 3180 5
  · have he : independentCachedBranchMembers2409.erase 3180=independentCachedBranchMembers2407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2407
  · have he : independentCachedBranchMembers2409.filter (independentCachedEdge 3180)=independentCachedBranchMembers2408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2408
def independentCachedBranchMembers2410 : Finset ℕ := ([18,192,1594,1596,1614,1686,1764,1768,2668,2740,2758,2764,3126,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2410 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2410 5 (fun x => (if x<1768 then (if x<1596 then (if x<192 then 0 else (if x<1594 then 0 else 0)) else (if x<1686 then (if x<1614 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<2758 then (if x<2668 then 0 else (if x<2740 then 1 else 1)) else (if x<3126 then (if x<2764 then 1 else 0) else (if x<3300 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2411 : Finset ℕ := ([18,48,72,192,1594,1596,1614,1686,1714,1738,1764,1768,2614,2618,2638,2668,2714,2740,2758,2764,2786,2792,3102,3126,3178,3180,3250,3256,3270,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2411 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2411 2638 5
  · have he : independentCachedBranchMembers2411.erase 2638=independentCachedBranchMembers2409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2409
  · have he : independentCachedBranchMembers2411.filter (independentCachedEdge 2638)=independentCachedBranchMembers2410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2410
def independentCachedBranchMembers2412 : Finset ℕ := ([1594,1614,1714,1738,1764,1768,2714,2740,2764,2786,3102,3178,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2412 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2412 5 (fun x => (if x<2740 then (if x<1738 then (if x<1614 then 0 else (if x<1714 then 0 else 1)) else (if x<1768 then (if x<1764 then 1 else 1) else (if x<2714 then 0 else 1))) else (if x<3102 then (if x<2764 then 1 else (if x<2786 then 0 else 1)) else (if x<3256 then (if x<3178 then 2 else 2) else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2413 : Finset ℕ := ([18,48,72,192,1594,1596,1614,1686,1714,1738,1740,1764,1768,2614,2618,2638,2668,2714,2740,2758,2764,2786,2792,3102,3126,3178,3180,3250,3256,3270,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2413 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2413 1740 5
  · have he : independentCachedBranchMembers2413.erase 1740=independentCachedBranchMembers2411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2411
  · have he : independentCachedBranchMembers2413.filter (independentCachedEdge 1740)=independentCachedBranchMembers2412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2412
def independentCachedBranchMembers2414 : Finset ℕ := ([18,192,1594,1740,1768,2618,2668,2714,2740,2758,2764,2786,2792,3126,3178,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2414 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2414 5 (fun x => (if x<2758 then (if x<1768 then (if x<1594 then (if x<192 then 0 else 0) else (if x<1740 then 0 else 1)) else (if x<2668 then (if x<2618 then 0 else 1) else (if x<2714 then 1 else (if x<2740 then 2 else 2)))) else (if x<3178 then (if x<2786 then (if x<2764 then 2 else 0) else (if x<2792 then 3 else (if x<3126 then 2 else 0))) else (if x<3256 then (if x<3250 then 3 else 1) else (if x<3274 then 2 else (if x<3300 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2415 : Finset ℕ := ([18,48,72,192,1594,1596,1614,1686,1714,1738,1740,1764,1768,2614,2618,2638,2668,2714,2740,2758,2764,2786,2792,3102,3126,3178,3180,3250,3252,3256,3270,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2415 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2415 3252 5
  · have he : independentCachedBranchMembers2415.erase 3252=independentCachedBranchMembers2413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2413
  · have he : independentCachedBranchMembers2415.filter (independentCachedEdge 3252)=independentCachedBranchMembers2414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2414
def independentCachedBranchMembers2416 : Finset ℕ := ([48,192,1594,1596,1614,1686,1738,1740,1764,2614,2668,2714,2740,2758,2792,3256,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2416 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2416 5 (fun x => (if x<2614 then (if x<1614 then (if x<1594 then (if x<192 then 0 else 0) else (if x<1596 then 0 else 1)) else (if x<1738 then (if x<1686 then 1 else 1) else (if x<1740 then 0 else (if x<1764 then 2 else 1)))) else (if x<2792 then (if x<2714 then (if x<2668 then 0 else 1) else (if x<2740 then 3 else (if x<2758 then 1 else 0))) else (if x<3274 then (if x<3256 then 2 else 3) else (if x<3276 then 2 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2417 : Finset ℕ := ([18,48,72,192,1594,1596,1614,1686,1714,1738,1740,1764,1768,2614,2618,2638,2668,2710,2714,2740,2758,2764,2786,2792,3102,3126,3178,3180,3250,3252,3256,3270,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2417 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2417 2710 5
  · have he : independentCachedBranchMembers2417.erase 2710=independentCachedBranchMembers2415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2415
  · have he : independentCachedBranchMembers2417.filter (independentCachedEdge 2710)=independentCachedBranchMembers2416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2416
def independentCachedBranchMembers2418 : Finset ℕ := ([18,72,1596,1614,1686,1714,1740,1764,1768,2614,2618,2668,2740,2758,2786,3178,3250,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2418 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2418 5 (fun x => (if x<2614 then (if x<1686 then (if x<1596 then (if x<72 then 0 else 0) else (if x<1614 then 1 else 1)) else (if x<1740 then (if x<1714 then 0 else 2) else (if x<1764 then 0 else (if x<1768 then 1 else 2)))) else (if x<2786 then (if x<2668 then (if x<2618 then 0 else 3) else (if x<2740 then 0 else (if x<2758 then 1 else 1))) else (if x<3250 then (if x<3178 then 2 else 3) else (if x<3276 then 0 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2419 : Finset ℕ := ([18,48,72,192,1594,1596,1614,1686,1714,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2740,2758,2764,2786,2792,3102,3126,3178,3180,3250,3252,3256,3270,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2419 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2419 2620 5
  · have he : independentCachedBranchMembers2419.erase 2620=independentCachedBranchMembers2417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2417
  · have he : independentCachedBranchMembers2419.filter (independentCachedEdge 2620)=independentCachedBranchMembers2418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2418
def independentCachedBranchMembers2420 : Finset ℕ := ([18,48,72,192,1596,1686,1740,2614,2618,2638,2668,2758,2792,3126,3180,3250,3270,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2420 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2420 5 (fun x => (if x<2638 then (if x<1596 then (if x<72 then (if x<48 then 0 else 1) else (if x<192 then 0 else 1)) else (if x<1740 then (if x<1686 then 1 else 0) else (if x<2614 then 0 else (if x<2618 then 0 else 1)))) else (if x<3180 then (if x<2758 then (if x<2668 then 2 else 0) else (if x<2792 then 3 else (if x<3126 then 2 else 1))) else (if x<3270 then (if x<3250 then 2 else 0) else (if x<3274 then 1 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2421 : Finset ℕ := ([18,48,72,192,1594,1596,1614,1686,1692,1714,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2740,2758,2764,2786,2792,3102,3126,3178,3180,3250,3252,3256,3270,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2421 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2421 1692 5
  · have he : independentCachedBranchMembers2421.erase 1692=independentCachedBranchMembers2419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2419
  · have he : independentCachedBranchMembers2421.filter (independentCachedEdge 1692)=independentCachedBranchMembers2420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2420
def independentCachedBranchMembers2422 : Finset ℕ := ([1594,1596,1686,1714,1738,1740,1768,2614,2638,2668,2714,2758,2786,3126,3178,3180,3256,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2422 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2422 5 (fun x => (if x<2668 then (if x<1738 then (if x<1686 then (if x<1596 then 0 else 1) else (if x<1714 then 0 else 1)) else (if x<1768 then (if x<1740 then 0 else 2) else (if x<2614 then 1 else (if x<2638 then 0 else 2)))) else (if x<3178 then (if x<2758 then (if x<2714 then 1 else 0) else (if x<2786 then 0 else (if x<3126 then 1 else 3))) else (if x<3256 then (if x<3180 then 3 else 2) else (if x<3270 then 3 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2423 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1686,1692,1714,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2740,2758,2764,2786,2792,3102,3126,3178,3180,3250,3252,3256,3270,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2423 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2423 1590 5
  · have he : independentCachedBranchMembers2423.erase 1590=independentCachedBranchMembers2421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2421
  · have he : independentCachedBranchMembers2423.filter (independentCachedEdge 1590)=independentCachedBranchMembers2422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2422
def independentCachedBranchMembers2424 : Finset ℕ := ([48,1594,1596,1614,1692,1714,1768,2618,2620,2638,2714,2740,2758,2792,3102,3126,3178,3180,3256,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2424 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2424 5 (fun x => (if x<2740 then (if x<1714 then (if x<1596 then (if x<1594 then 0 else 0) else (if x<1614 then 1 else (if x<1692 then 0 else 2))) else (if x<2620 then (if x<1768 then 1 else (if x<2618 then 1 else 3)) else (if x<2638 then 2 else (if x<2714 then 3 else 2)))) else (if x<3178 then (if x<2792 then (if x<2758 then 4 else 0) else (if x<3102 then 3 else (if x<3126 then 2 else 1))) else (if x<3274 then (if x<3180 then 3 else (if x<3256 then 1 else 0)) else (if x<3276 then 4 else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2425 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1686,1692,1714,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2740,2758,2764,2786,2792,3102,3126,3178,3180,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2425 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2425 3304 5
  · have he : independentCachedBranchMembers2425.erase 3304=independentCachedBranchMembers2423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2423
  · have he : independentCachedBranchMembers2425.filter (independentCachedEdge 3304)=independentCachedBranchMembers2424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2424
def independentCachedBranchMembers2426 : Finset ℕ := ([18,72,1596,1614,1686,1714,1740,1764,1768,2620,2638,2710,2714,2764,2792,3102,3126,3180,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2426 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2426 5 (fun x => (if x<2710 then (if x<1714 then (if x<1596 then (if x<72 then 0 else 0) else (if x<1614 then 1 else (if x<1686 then 1 else 0))) else (if x<1768 then (if x<1740 then 2 else (if x<1764 then 0 else 1)) else (if x<2620 then 2 else (if x<2638 then 3 else 3)))) else (if x<3126 then (if x<2764 then (if x<2714 then 2 else 3) else (if x<2792 then 2 else (if x<3102 then 0 else 1))) else (if x<3256 then (if x<3180 then 0 else (if x<3252 then 0 else 1)) else (if x<3270 then 3 else (if x<3274 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2427 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1686,1692,1714,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2740,2758,2764,2786,2792,3102,3126,3132,3178,3180,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2427 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2427 3132 5
  · have he : independentCachedBranchMembers2427.erase 3132=independentCachedBranchMembers2425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2425
  · have he : independentCachedBranchMembers2427.filter (independentCachedEdge 3132)=independentCachedBranchMembers2426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2426
def independentCachedBranchMembers2428 : Finset ℕ := ([18,72,192,1594,1596,1614,1692,1714,1768,2614,2668,2710,2764,2786,3102,3126,3178,3180,3256,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2428 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2428 5 (fun x => (if x<2710 then (if x<1614 then (if x<192 then (if x<72 then 0 else 0) else (if x<1594 then 1 else (if x<1596 then 1 else 2))) else (if x<1768 then (if x<1692 then 2 else (if x<1714 then 3 else 0)) else (if x<2614 then 0 else (if x<2668 then 0 else 0)))) else (if x<3178 then (if x<2786 then (if x<2764 then 3 else 1) else (if x<3102 then 3 else (if x<3126 then 2 else 1))) else (if x<3274 then (if x<3180 then 3 else (if x<3256 then 2 else 2)) else (if x<3276 then 2 else (if x<3300 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2429 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1686,1692,1714,1720,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2740,2758,2764,2786,2792,3102,3126,3132,3178,3180,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2429 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2429 1720 5
  · have he : independentCachedBranchMembers2429.erase 1720=independentCachedBranchMembers2427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2427
  · have he : independentCachedBranchMembers2429.filter (independentCachedEdge 1720)=independentCachedBranchMembers2428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2428
def independentCachedBranchMembers2430 : Finset ℕ := ([48,192,1596,1614,1686,1714,1740,1764,1768,2614,2618,2668,2740,2758,2786,3102,3126,3180,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2430 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2430 5 (fun x => (if x<2618 then (if x<1714 then (if x<1596 then (if x<192 then 0 else 0) else (if x<1614 then 0 else (if x<1686 then 1 else 1))) else (if x<1764 then (if x<1740 then 2 else 0) else (if x<1768 then 1 else (if x<2614 then 2 else 0)))) else (if x<3102 then (if x<2740 then (if x<2668 then 3 else 1) else (if x<2758 then 1 else (if x<2786 then 0 else 2))) else (if x<3256 then (if x<3126 then 3 else (if x<3180 then 4 else 4)) else (if x<3270 then 3 else (if x<3274 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2431 : Finset ℕ := ([192,1740,1768,2618,2668,2740,2758,2786,3126,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2431 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2431 4 (fun x => (if x<2740 then (if x<1768 then (if x<1740 then 0 else 0) else (if x<2618 then 1 else (if x<2668 then 0 else 1))) else (if x<3126 then (if x<2758 then 2 else (if x<2786 then 2 else 1)) else (if x<3256 then 0 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
