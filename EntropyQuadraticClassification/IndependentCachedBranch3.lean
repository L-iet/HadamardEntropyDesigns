/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch2
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers384 : Finset ℕ := ([132,252,1594,1652,1686,1740,2652,2716,2730,2758,2788,2800,3126,3150,3180,3192,3214,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers384 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers384 5 (fun x => (if x<2800 then (if x<1740 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1686 then 1 else 1))) else (if x<2730 then (if x<2652 then 0 else (if x<2716 then 2 else 0)) else (if x<2758 then 3 else (if x<2788 then 2 else 0)))) else (if x<3214 then (if x<3150 then (if x<3126 then 2 else 1) else (if x<3180 then 2 else (if x<3192 then 4 else 1))) else (if x<3256 then (if x<3226 then 3 else (if x<3244 then 1 else 0)) else (if x<3284 then 3 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers385 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1626,1652,1678,1686,1720,1740,2620,2652,2662,2674,2716,2730,2738,2758,2762,2788,2792,2800,3126,3130,3150,3158,3180,3188,3192,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers385 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers385 1590 5
  · have he : independentCachedBranchMembers385.erase 1590=independentCachedBranchMembers383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound383
  · have he : independentCachedBranchMembers385.filter (independentCachedEdge 1590)=independentCachedBranchMembers384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound384
def independentCachedBranchMembers386 : Finset ℕ := ([132,252,1626,1652,1686,1720,1740,2652,2674,2716,2738,2758,2762,2788,2792,3126,3130,3150,3180,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers386 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers386 5 (fun x => (if x<2758 then (if x<1720 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1686 then 1 else 1))) else (if x<2674 then (if x<1740 then 1 else (if x<2652 then 0 else 2)) else (if x<2716 then 2 else (if x<2738 then 0 else 3)))) else (if x<3150 then (if x<2792 then (if x<2762 then 2 else (if x<2788 then 3 else 0)) else (if x<3126 then 2 else (if x<3130 then 3 else 4))) else (if x<3244 then (if x<3180 then 3 else (if x<3214 then 4 else 4)) else (if x<3284 then 0 else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers387 : Finset ℕ := ([1652,1720,2674,2716,2758,2788,3130,3214,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers387 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers387 4 (fun x => (if x<2788 then (if x<2674 then (if x<1720 then 0 else 0) else (if x<2716 then 1 else (if x<2758 then 2 else 1))) else (if x<3214 then (if x<3130 then 2 else 1) else (if x<3244 then 1 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers388 : Finset ℕ := ([72,132,252,1626,1652,1686,1720,1740,2652,2674,2716,2738,2758,2762,2788,2792,3126,3130,3150,3180,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers388 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers388 72 4
  · have he : independentCachedBranchMembers388.erase 72=independentCachedBranchMembers386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound386
  · have he : independentCachedBranchMembers388.filter (independentCachedEdge 72)=independentCachedBranchMembers387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound387
def independentCachedBranchMembers389 : Finset ℕ := ([1626,1686,2652,2716,2788,2792,3180,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers389 4 (fun x => (if x<2792 then (if x<2652 then (if x<1686 then 0 else 0) else (if x<2716 then 1 else (if x<2788 then 2 else 1))) else (if x<3244 then (if x<3180 then 2 else 1) else (if x<3284 then 2 else (if x<3288 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers390 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1720,1740,2652,2674,2716,2738,2758,2762,2788,2792,3126,3130,3150,3180,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers390 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers390 48 4
  · have he : independentCachedBranchMembers390.erase 48=independentCachedBranchMembers388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound388
  · have he : independentCachedBranchMembers390.filter (independentCachedEdge 48)=independentCachedBranchMembers389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound389
def independentCachedBranchMembers391 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1626,1652,1678,1686,1720,1740,2620,2652,2662,2674,2716,2730,2738,2758,2762,2788,2792,2800,3118,3126,3130,3150,3158,3180,3188,3192,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers391 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers391 3118 5
  · have he : independentCachedBranchMembers391.erase 3118=independentCachedBranchMembers385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound385
  · have he : independentCachedBranchMembers391.filter (independentCachedEdge 3118)=independentCachedBranchMembers390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound390
def independentCachedBranchMembers392 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers392 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers392 2786 6
  · have he : independentCachedBranchMembers392.erase 2786=independentCachedBranchMembers370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound370
  · have he : independentCachedBranchMembers392.filter (independentCachedEdge 2786)=independentCachedBranchMembers391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound391
def independentCachedBranchMembers393 : Finset ℕ := ([72,132,1642,1702,1740,2618,2650,2668,2702,2710,2716,2730,2738,2762,2776,2788,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers393 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers393 6 (fun x => (if x<2776 then (if x<2668 then (if x<1702 then (if x<132 then 0 else (if x<1642 then 0 else 0)) else (if x<2618 then (if x<1740 then 0 else 0) else (if x<2650 then 1 else 2))) else (if x<2716 then (if x<2702 then 1 else (if x<2710 then 1 else 2)) else (if x<2738 then (if x<2730 then 3 else 2) else (if x<2762 then 3 else 3)))) else (if x<3192 then (if x<3150 then (if x<2788 then 1 else (if x<3126 then 3 else 4)) else (if x<3178 then (if x<3164 then 4 else 5) else (if x<3186 then 2 else 5))) else (if x<3252 then (if x<3238 then (if x<3226 then 1 else 1) else (if x<3244 then 2 else 4)) else (if x<3284 then (if x<3270 then 3 else 5) else (if x<3304 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers394 : Finset ℕ := ([72,132,1740,2668,2716,2776,2788,3164,3192,3244,3252,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers394 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers394 5 (fun x => (if x<2788 then (if x<2668 then (if x<132 then 0 else (if x<1740 then 0 else 0)) else (if x<2716 then 1 else (if x<2776 then 1 else 2))) else (if x<3244 then (if x<3164 then 2 else (if x<3192 then 1 else 3)) else (if x<3284 then (if x<3252 then 1 else 3) else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers395 : Finset ℕ := ([72,132,1642,1702,1740,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers395 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers395 2662 5
  · have he : independentCachedBranchMembers395.erase 2662=independentCachedBranchMembers393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound393
  · have he : independentCachedBranchMembers395.filter (independentCachedEdge 2662)=independentCachedBranchMembers394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound394
def independentCachedBranchMembers396 : Finset ℕ := ([72,132,1740,2618,2650,2668,2702,2710,2776,3164,3178,3186,3238,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers396 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers396 5 (fun x => (if x<2710 then (if x<2618 then (if x<132 then 0 else (if x<1740 then 0 else 0)) else (if x<2668 then (if x<2650 then 1 else 2) else (if x<2702 then 1 else 1))) else (if x<3186 then (if x<3164 then (if x<2776 then 2 else 1) else (if x<3178 then 3 else 2)) else (if x<3270 then (if x<3238 then 3 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers397 : Finset ℕ := ([72,132,1642,1702,1740,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers397 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers397 3298 5
  · have he : independentCachedBranchMembers397.erase 3298=independentCachedBranchMembers395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound395
  · have he : independentCachedBranchMembers397.filter (independentCachedEdge 3298)=independentCachedBranchMembers396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound396
def independentCachedBranchMembers398 : Finset ℕ := ([1642,1702,1740,2650,2662,2710,2730,3126,3150,3164,3186,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers398 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers398 5 (fun x => (if x<3126 then (if x<2650 then (if x<1702 then 0 else (if x<1740 then 0 else 0)) else (if x<2710 then (if x<2662 then 1 else 1) else (if x<2730 then 1 else 1))) else (if x<3244 then (if x<3164 then (if x<3150 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3284 then (if x<3270 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers399 : Finset ℕ := ([72,132,1642,1702,1740,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers399 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers399 3276 5
  · have he : independentCachedBranchMembers399.erase 3276=independentCachedBranchMembers397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound397
  · have he : independentCachedBranchMembers399.filter (independentCachedEdge 3276)=independentCachedBranchMembers398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound398
def independentCachedBranchMembers400 : Finset ℕ := ([72,132,1740,2650,2710,2716,2738,2762,2788,3126,3150,3178,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers400 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers400 5 (fun x => (if x<2762 then (if x<2650 then (if x<132 then 0 else (if x<1740 then 0 else 0)) else (if x<2716 then (if x<2710 then 1 else 1) else (if x<2738 then 2 else 2))) else (if x<3178 then (if x<3126 then (if x<2788 then 2 else 2) else (if x<3150 then 3 else 3)) else (if x<3244 then (if x<3238 then 1 else 1) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers401 : Finset ℕ := ([72,132,1642,1702,1740,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers401 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers401 3118 5
  · have he : independentCachedBranchMembers401.erase 3118=independentCachedBranchMembers399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound399
  · have he : independentCachedBranchMembers401.filter (independentCachedEdge 3118)=independentCachedBranchMembers400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound400
def independentCachedBranchMembers402 : Finset ℕ := ([72,132,2618,2650,2662,2668,2710,2716,2730,2762,3126,3164,3178,3226,3238,3244,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers402 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers402 5 (fun x => (if x<2762 then (if x<2662 then (if x<2618 then (if x<132 then 0 else 0) else (if x<2650 then 1 else 0)) else (if x<2710 then (if x<2668 then 1 else 2) else (if x<2716 then 0 else (if x<2730 then 2 else 2)))) else (if x<3226 then (if x<3164 then (if x<3126 then 1 else 1) else (if x<3178 then 2 else 0)) else (if x<3244 then (if x<3238 then 1 else 0) else (if x<3270 then 2 else (if x<3276 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers403 : Finset ℕ := ([72,132,1642,1702,1740,1776,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers403 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers403 1776 5
  · have he : independentCachedBranchMembers403.erase 1776=independentCachedBranchMembers401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound401
  · have he : independentCachedBranchMembers403.filter (independentCachedEdge 1776)=independentCachedBranchMembers402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound402
def independentCachedBranchMembers404 : Finset ℕ := ([72,132,2650,2662,2702,2710,2730,2738,2776,2788,3150,3178,3186,3226,3238,3276,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers404 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers404 5 (fun x => (if x<2788 then (if x<2702 then (if x<2650 then (if x<132 then 0 else 0) else (if x<2662 then 0 else 1)) else (if x<2730 then (if x<2710 then 1 else 0) else (if x<2738 then 2 else (if x<2776 then 1 else 2)))) else (if x<3226 then (if x<3178 then (if x<3150 then 2 else 1) else (if x<3186 then 0 else 1)) else (if x<3276 then (if x<3238 then 1 else 0) else (if x<3284 then 3 else (if x<3304 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers405 : Finset ℕ := ([72,132,1596,1642,1702,1740,1776,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers405 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers405 1596 5
  · have he : independentCachedBranchMembers405.erase 1596=independentCachedBranchMembers403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound403
  · have he : independentCachedBranchMembers405.filter (independentCachedEdge 1596)=independentCachedBranchMembers404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound404
def independentCachedBranchMembers406 : Finset ℕ := ([1642,1702,2618,2650,2662,2702,2710,2730,2738,2762,3118,3126,3150,3178,3186,3226,3238,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers406 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers406 5 (fun x => (if x<2762 then (if x<2662 then (if x<2618 then (if x<1702 then 0 else 0) else (if x<2650 then 1 else 0)) else (if x<2710 then (if x<2702 then 0 else 1) else (if x<2730 then 0 else (if x<2738 then 0 else 2)))) else (if x<3186 then (if x<3126 then (if x<3118 then 2 else 1) else (if x<3150 then 2 else (if x<3178 then 2 else 3))) else (if x<3238 then (if x<3226 then 1 else 1) else (if x<3270 then 3 else (if x<3298 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers407 : Finset ℕ := ([72,132,252,1596,1642,1702,1740,1776,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers407 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers407 252 5
  · have he : independentCachedBranchMembers407.erase 252=independentCachedBranchMembers405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound405
  · have he : independentCachedBranchMembers407.filter (independentCachedEdge 252)=independentCachedBranchMembers406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound406
def independentCachedBranchMembers408 : Finset ℕ := ([132,1642,1740,1776,2618,2650,2662,2702,2716,2738,3118,3150,3164,3186,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers408 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers408 5 (fun x => (if x<3118 then (if x<2650 then (if x<1740 then (if x<1642 then 0 else 0) else (if x<1776 then 0 else (if x<2618 then 1 else 0))) else (if x<2702 then (if x<2662 then 2 else 2) else (if x<2716 then 1 else (if x<2738 then 0 else 1)))) else (if x<3238 then (if x<3164 then (if x<3150 then 3 else 1) else (if x<3186 then 3 else (if x<3226 then 0 else 2))) else (if x<3270 then (if x<3252 then 2 else 3) else (if x<3284 then 3 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers409 : Finset ℕ := ([72,132,252,1596,1642,1702,1740,1768,1776,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers409 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers409 1768 5
  · have he : independentCachedBranchMembers409.erase 1768=independentCachedBranchMembers407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound407
  · have he : independentCachedBranchMembers409.filter (independentCachedEdge 1768)=independentCachedBranchMembers408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound408
def independentCachedBranchMembers410 : Finset ℕ := ([132,1596,1702,1740,2618,2662,2702,2710,2762,2788,3118,3126,3164,3178,3186,3226,3244,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers410 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers410 5 (fun x => (if x<3118 then (if x<2662 then (if x<1702 then (if x<1596 then 0 else 1) else (if x<1740 then 0 else (if x<2618 then 0 else 1))) else (if x<2710 then (if x<2702 then 2 else 0) else (if x<2762 then 2 else (if x<2788 then 1 else 0)))) else (if x<3226 then (if x<3164 then (if x<3126 then 3 else 1) else (if x<3178 then 3 else (if x<3186 then 2 else 3))) else (if x<3252 then (if x<3244 then 2 else 0) else (if x<3270 then 3 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers411 : Finset ℕ := ([72,132,252,1596,1628,1642,1702,1740,1768,1776,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers411 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers411 1628 5
  · have he : independentCachedBranchMembers411.erase 1628=independentCachedBranchMembers409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound409
  · have he : independentCachedBranchMembers411.filter (independentCachedEdge 1628)=independentCachedBranchMembers410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound410
def independentCachedBranchMembers412 : Finset ℕ := ([1628,1642,1702,1768,2650,2662,2668,2710,2716,2730,2776,2788,3118,3164,3178,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers412 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers412 5 (fun x => (if x<2776 then (if x<2662 then (if x<1702 then (if x<1642 then 0 else 0) else (if x<1768 then 1 else (if x<2650 then 1 else 0))) else (if x<2710 then (if x<2668 then 2 else 0) else (if x<2716 then 1 else (if x<2730 then 0 else 0)))) else (if x<3226 then (if x<3118 then (if x<2788 then 1 else 1) else (if x<3164 then 2 else (if x<3178 then 3 else 3))) else (if x<3284 then (if x<3238 then 2 else (if x<3244 then 4 else 3)) else (if x<3298 then 4 else (if x<3304 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers413 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1702,1740,1768,1776,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers413 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers413 48 5
  · have he : independentCachedBranchMembers413.erase 48=independentCachedBranchMembers411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound411
  · have he : independentCachedBranchMembers413.filter (independentCachedEdge 48)=independentCachedBranchMembers412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound412
def independentCachedBranchMembers414 : Finset ℕ := ([132,252,1628,1642,1740,1776,2618,2710,2716,2730,2776,2788,3126,3150,3186,3192,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers414 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers414 5 (fun x => (if x<2788 then (if x<1776 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1642 then 1 else (if x<1740 then 1 else 0))) else (if x<2716 then (if x<2618 then 1 else (if x<2710 then 2 else 2)) else (if x<2730 then 0 else (if x<2776 then 3 else 2)))) else (if x<3226 then (if x<3150 then (if x<3126 then 0 else 2) else (if x<3186 then 1 else (if x<3192 then 4 else 1))) else (if x<3284 then (if x<3238 then 2 else (if x<3244 then 3 else 0)) else (if x<3298 then 0 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers415 : Finset ℕ := ([48,72,132,252,1596,1614,1628,1642,1702,1740,1768,1776,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers415 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers415 1614 5
  · have he : independentCachedBranchMembers415.erase 1614=independentCachedBranchMembers413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound413
  · have he : independentCachedBranchMembers415.filter (independentCachedEdge 1614)=independentCachedBranchMembers414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound414
def independentCachedBranchMembers416 : Finset ℕ := ([132,252,1596,1702,1740,1768,2650,2668,2702,2716,2730,2788,3126,3150,3164,3178,3192,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers416 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers416 5 (fun x => (if x<2788 then (if x<1768 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1702 then 1 else (if x<1740 then 1 else 0))) else (if x<2702 then (if x<2650 then 1 else (if x<2668 then 2 else 2)) else (if x<2716 then 2 else (if x<2730 then 0 else 3)))) else (if x<3192 then (if x<3150 then (if x<3126 then 0 else 1) else (if x<3164 then 2 else (if x<3178 then 3 else 3))) else (if x<3270 then (if x<3226 then 1 else (if x<3244 then 2 else 0)) else (if x<3284 then 4 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers417 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1628,1642,1702,1740,1768,1776,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers417 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers417 1590 5
  · have he : independentCachedBranchMembers417.erase 1590=independentCachedBranchMembers415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound415
  · have he : independentCachedBranchMembers417.filter (independentCachedEdge 1590)=independentCachedBranchMembers416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound416
def independentCachedBranchMembers418 : Finset ℕ := ([132,252,1596,1642,1702,1740,1776,2618,2668,2702,2716,2738,2762,2776,2788,3126,3150,3164,3186,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers418 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers418 5 (fun x => (if x<2738 then (if x<1740 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1642 then 1 else (if x<1702 then 1 else 1))) else (if x<2668 then (if x<1776 then 0 else (if x<2618 then 1 else 2)) else (if x<2702 then 2 else (if x<2716 then 2 else 0)))) else (if x<3164 then (if x<2788 then (if x<2762 then 3 else (if x<2776 then 3 else 2)) else (if x<3126 then 0 else (if x<3150 then 3 else 3))) else (if x<3270 then (if x<3186 then 4 else (if x<3244 then 4 else 0)) else (if x<3284 then 4 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers419 : Finset ℕ := ([1596,1776,2618,2702,2716,2788,3186,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers419 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers419 4 (fun x => (if x<2788 then (if x<2618 then (if x<1776 then 0 else 0) else (if x<2702 then 1 else (if x<2716 then 1 else 2))) else (if x<3244 then (if x<3186 then 2 else 1) else (if x<3270 then 2 else (if x<3284 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers420 : Finset ℕ := ([72,132,252,1596,1642,1702,1740,1776,2618,2668,2702,2716,2738,2762,2776,2788,3126,3150,3164,3186,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers420 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers420 72 4
  · have he : independentCachedBranchMembers420.erase 72=independentCachedBranchMembers418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound418
  · have he : independentCachedBranchMembers420.filter (independentCachedEdge 72)=independentCachedBranchMembers419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound419
def independentCachedBranchMembers421 : Finset ℕ := ([1642,1702,2668,2716,2776,2788,3164,3244,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers421 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers421 4 (fun x => (if x<2788 then (if x<2668 then (if x<1702 then 0 else 0) else (if x<2716 then 1 else (if x<2776 then 1 else 2))) else (if x<3244 then (if x<3164 then 2 else 1) else (if x<3284 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers422 : Finset ℕ := ([48,72,132,252,1596,1642,1702,1740,1776,2618,2668,2702,2716,2738,2762,2776,2788,3126,3150,3164,3186,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers422 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers422 48 4
  · have he : independentCachedBranchMembers422.erase 48=independentCachedBranchMembers420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound420
  · have he : independentCachedBranchMembers422.filter (independentCachedEdge 48)=independentCachedBranchMembers421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound421
def independentCachedBranchMembers423 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1628,1642,1702,1740,1768,1776,2618,2650,2662,2668,2702,2710,2716,2730,2738,2762,2776,2788,3118,3126,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers423 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers423 3158 5
  · have he : independentCachedBranchMembers423.erase 3158=independentCachedBranchMembers417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound417
  · have he : independentCachedBranchMembers423.filter (independentCachedEdge 3158)=independentCachedBranchMembers422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound422
def independentCachedBranchMembers424 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers424 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers424 2714 6
  · have he : independentCachedBranchMembers424.erase 2714=independentCachedBranchMembers392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound392
  · have he : independentCachedBranchMembers424.filter (independentCachedEdge 2714)=independentCachedBranchMembers423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound423
def independentCachedBranchMembers425 : Finset ℕ := ([72,132,1642,1702,1740,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers425 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers425 6 (fun x => (if x<2792 then (if x<2652 then (if x<1740 then (if x<1642 then (if x<132 then 0 else 0) else (if x<1702 then 0 else 0)) else (if x<2638 then (if x<2614 then 0 else 1) else (if x<2650 then 1 else 2))) else (if x<2730 then (if x<2674 then (if x<2662 then 3 else 2) else (if x<2710 then 3 else 2)) else (if x<2758 then (if x<2732 then 1 else 4) else (if x<2772 then 3 else 4)))) else (if x<3228 then (if x<3178 then (if x<3130 then (if x<3118 then 3 else 1) else (if x<3158 then 5 else 1)) else (if x<3192 then (if x<3180 then 2 else 5) else (if x<3214 then 3 else 5))) else (if x<3274 then (if x<3250 then (if x<3238 then 4 else 2) else (if x<3252 then 1 else 5)) else (if x<3288 then (if x<3276 then 1 else 3) else (if x<3298 then 5 else (if x<3300 then 3 else 4)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers426 : Finset ℕ := ([72,132,2614,2650,2652,2662,2710,2730,2732,2758,3130,3158,3178,3180,3228,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers426 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers426 5 (fun x => (if x<2758 then (if x<2652 then (if x<2614 then (if x<132 then 0 else 0) else (if x<2650 then 1 else 0)) else (if x<2710 then (if x<2662 then 1 else 2) else (if x<2730 then 0 else (if x<2732 then 2 else 1)))) else (if x<3180 then (if x<3158 then (if x<3130 then 1 else 3) else (if x<3178 then 1 else 0)) else (if x<3238 then (if x<3228 then 3 else 3) else (if x<3274 then 0 else (if x<3276 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers427 : Finset ℕ := ([72,132,1642,1702,1740,1776,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers427 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers427 1776 5
  · have he : independentCachedBranchMembers427.erase 1776=independentCachedBranchMembers425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound425
  · have he : independentCachedBranchMembers427.filter (independentCachedEdge 1776)=independentCachedBranchMembers426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound426
def independentCachedBranchMembers428 : Finset ℕ := ([72,132,2638,2650,2662,2674,2710,2730,2772,2792,3158,3178,3214,3238,3250,3276,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers428 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers428 5 (fun x => (if x<2792 then (if x<2662 then (if x<2638 then (if x<132 then 0 else 0) else (if x<2650 then 1 else 0)) else (if x<2710 then (if x<2674 then 2 else 1) else (if x<2730 then 0 else (if x<2772 then 1 else 2)))) else (if x<3238 then (if x<3178 then (if x<3158 then 2 else 1) else (if x<3214 then 0 else 1)) else (if x<3276 then (if x<3250 then 0 else 1) else (if x<3288 then 3 else (if x<3300 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers429 : Finset ℕ := ([72,132,1596,1642,1702,1740,1776,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers429 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers429 1596 5
  · have he : independentCachedBranchMembers429.erase 1596=independentCachedBranchMembers427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound427
  · have he : independentCachedBranchMembers429.filter (independentCachedEdge 1596)=independentCachedBranchMembers428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound428
def independentCachedBranchMembers430 : Finset ℕ := ([1642,1702,2614,2638,2650,2662,2674,2710,2730,2758,3118,3130,3158,3178,3214,3238,3250,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers430 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers430 5 (fun x => (if x<2758 then (if x<2650 then (if x<2614 then (if x<1702 then 0 else 0) else (if x<2638 then 1 else 1)) else (if x<2674 then (if x<2662 then 0 else 0) else (if x<2710 then 2 else (if x<2730 then 0 else 0)))) else (if x<3214 then (if x<3130 then (if x<3118 then 2 else 1) else (if x<3158 then 2 else (if x<3178 then 1 else 3))) else (if x<3250 then (if x<3238 then 2 else 3) else (if x<3274 then 1 else (if x<3298 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers431 : Finset ℕ := ([72,132,252,1596,1642,1702,1740,1776,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers431 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers431 252 5
  · have he : independentCachedBranchMembers431.erase 252=independentCachedBranchMembers429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound429
  · have he : independentCachedBranchMembers431.filter (independentCachedEdge 252)=independentCachedBranchMembers430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound430
def independentCachedBranchMembers432 : Finset ℕ := ([72,1702,1740,1776,2614,2638,2652,2674,2710,2730,3118,3158,3178,3192,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers432 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers432 5 (fun x => (if x<3118 then (if x<2638 then (if x<1740 then (if x<1702 then 0 else 0) else (if x<1776 then 0 else (if x<2614 then 1 else 0))) else (if x<2674 then (if x<2652 then 1 else 0) else (if x<2710 then 1 else (if x<2730 then 2 else 2)))) else (if x<3228 then (if x<3178 then (if x<3158 then 3 else 2) else (if x<3192 then 2 else (if x<3214 then 3 else 1))) else (if x<3274 then (if x<3250 then 3 else 0) else (if x<3288 then 3 else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers433 : Finset ℕ := ([72,132,252,1596,1642,1702,1740,1764,1776,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers433 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers433 1764 5
  · have he : independentCachedBranchMembers433.erase 1764=independentCachedBranchMembers431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound431
  · have he : independentCachedBranchMembers433.filter (independentCachedEdge 1764)=independentCachedBranchMembers432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound432
def independentCachedBranchMembers434 : Finset ℕ := ([72,1596,1642,1740,2614,2638,2650,2730,2758,2792,3118,3130,3158,3180,3192,3228,3238,3250,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers434 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers434 5 (fun x => (if x<3118 then (if x<2638 then (if x<1642 then (if x<1596 then 0 else 1) else (if x<1740 then 0 else (if x<2614 then 0 else 1))) else (if x<2730 then (if x<2650 then 0 else 2) else (if x<2758 then 2 else (if x<2792 then 1 else 0)))) else (if x<3228 then (if x<3158 then (if x<3130 then 3 else 1) else (if x<3180 then 2 else (if x<3192 then 0 else 3))) else (if x<3250 then (if x<3238 then 3 else 2) else (if x<3274 then 3 else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers435 : Finset ℕ := ([72,132,252,1596,1642,1692,1702,1740,1764,1776,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers435 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers435 1692 5
  · have he : independentCachedBranchMembers435.erase 1692=independentCachedBranchMembers433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound433
  · have he : independentCachedBranchMembers435.filter (independentCachedEdge 1692)=independentCachedBranchMembers434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound434
def independentCachedBranchMembers436 : Finset ℕ := ([1642,1692,1702,1764,2650,2652,2662,2710,2730,2732,2772,2792,3118,3158,3178,3180,3228,3238,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers436 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers436 5 (fun x => (if x<2772 then (if x<2652 then (if x<1702 then (if x<1692 then 0 else 1) else (if x<1764 then 0 else (if x<2650 then 1 else 0))) else (if x<2710 then (if x<2662 then 2 else 0) else (if x<2730 then 0 else (if x<2732 then 0 else 1)))) else (if x<3180 then (if x<3118 then (if x<2792 then 1 else 2) else (if x<3158 then 3 else (if x<3178 then 2 else 4))) else (if x<3288 then (if x<3228 then 2 else (if x<3238 then 3 else 4)) else (if x<3298 then 2 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers437 : Finset ℕ := ([48,72,132,252,1596,1642,1692,1702,1740,1764,1776,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers437 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers437 48 5
  · have he : independentCachedBranchMembers437.erase 48=independentCachedBranchMembers435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound435
  · have he : independentCachedBranchMembers437.filter (independentCachedEdge 48)=independentCachedBranchMembers436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound436
def independentCachedBranchMembers438 : Finset ℕ := ([72,252,1692,1702,1740,1776,2614,2650,2652,2662,2772,2792,3130,3158,3178,3180,3214,3250,3252,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers438 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers438 5 (fun x => (if x<2792 then (if x<1776 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1702 then 1 else (if x<1740 then 1 else 0))) else (if x<2652 then (if x<2614 then 1 else (if x<2650 then 2 else 2)) else (if x<2662 then 0 else (if x<2772 then 3 else 2)))) else (if x<3214 then (if x<3158 then (if x<3130 then 0 else 2) else (if x<3178 then 2 else (if x<3180 then 3 else 0))) else (if x<3288 then (if x<3250 then 1 else (if x<3252 then 4 else 1)) else (if x<3298 then 0 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers439 : Finset ℕ := ([48,72,132,252,1596,1642,1678,1692,1702,1740,1764,1776,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers439 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers439 1678 5
  · have he : independentCachedBranchMembers439.erase 1678=independentCachedBranchMembers437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound437
  · have he : independentCachedBranchMembers439.filter (independentCachedEdge 1678)=independentCachedBranchMembers438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound438
def independentCachedBranchMembers440 : Finset ℕ := ([72,252,1596,1642,1740,1764,2638,2652,2662,2710,2732,2792,3130,3158,3180,3214,3228,3238,3252,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers440 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers440 5 (fun x => (if x<2792 then (if x<1764 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1642 then 1 else (if x<1740 then 1 else 0))) else (if x<2662 then (if x<2638 then 1 else (if x<2652 then 2 else 0)) else (if x<2710 then 3 else (if x<2732 then 2 else 2)))) else (if x<3228 then (if x<3158 then (if x<3130 then 0 else 1) else (if x<3180 then 2 else (if x<3214 then 0 else 2))) else (if x<3274 then (if x<3238 then 3 else (if x<3252 then 3 else 1)) else (if x<3288 then 4 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers441 : Finset ℕ := ([48,72,132,252,1594,1596,1642,1678,1692,1702,1740,1764,1776,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers441 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers441 1594 5
  · have he : independentCachedBranchMembers441.erase 1594=independentCachedBranchMembers439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound439
  · have he : independentCachedBranchMembers441.filter (independentCachedEdge 1594)=independentCachedBranchMembers440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound440
def independentCachedBranchMembers442 : Finset ℕ := ([132,252,1596,1642,1702,1740,1776,2614,2638,2652,2674,2732,2758,2772,2792,3130,3180,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers442 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers442 5 (fun x => (if x<2732 then (if x<1740 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1642 then 1 else (if x<1702 then 1 else 1))) else (if x<2638 then (if x<1776 then 0 else (if x<2614 then 1 else 2)) else (if x<2652 then 2 else (if x<2674 then 3 else 3)))) else (if x<3214 then (if x<2792 then (if x<2758 then 0 else (if x<2772 then 3 else 0)) else (if x<3130 then 3 else (if x<3180 then 4 else 4))) else (if x<3274 then (if x<3228 then 4 else (if x<3250 then 0 else 2)) else (if x<3288 then 2 else (if x<3300 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers443 : Finset ℕ := ([1596,1776,2674,2732,2758,2772,3130,3214,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers443 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers443 4 (fun x => (if x<2772 then (if x<2674 then (if x<1776 then 0 else 0) else (if x<2732 then 1 else (if x<2758 then 2 else 1))) else (if x<3214 then (if x<3130 then 2 else 1) else (if x<3228 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers444 : Finset ℕ := ([72,132,252,1596,1642,1702,1740,1776,2614,2638,2652,2674,2732,2758,2772,2792,3130,3180,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers444 72 4
  · have he : independentCachedBranchMembers444.erase 72=independentCachedBranchMembers442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound442
  · have he : independentCachedBranchMembers444.filter (independentCachedEdge 72)=independentCachedBranchMembers443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound443
def independentCachedBranchMembers445 : Finset ℕ := ([1642,1702,2652,2732,2772,2792,3180,3228,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers445 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers445 4 (fun x => (if x<2792 then (if x<2652 then (if x<1702 then 0 else 0) else (if x<2732 then 1 else (if x<2772 then 1 else 2))) else (if x<3228 then (if x<3180 then 2 else 1) else (if x<3288 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers446 : Finset ℕ := ([48,72,132,252,1596,1642,1702,1740,1776,2614,2638,2652,2674,2732,2758,2772,2792,3130,3180,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers446 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers446 48 4
  · have he : independentCachedBranchMembers446.erase 48=independentCachedBranchMembers444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound444
  · have he : independentCachedBranchMembers446.filter (independentCachedEdge 48)=independentCachedBranchMembers445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound445
def independentCachedBranchMembers447 : Finset ℕ := ([48,72,132,252,1594,1596,1642,1678,1692,1702,1740,1764,1776,2614,2638,2650,2652,2662,2674,2710,2730,2732,2758,2772,2792,3118,3130,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers447 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers447 3226 5
  · have he : independentCachedBranchMembers447.erase 3226=independentCachedBranchMembers441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound441
  · have he : independentCachedBranchMembers447.filter (independentCachedEdge 3226)=independentCachedBranchMembers446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound446
def independentCachedBranchMembers448 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers448 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers448 2646 6
  · have he : independentCachedBranchMembers448.erase 2646=independentCachedBranchMembers424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound424
  · have he : independentCachedBranchMembers448.filter (independentCachedEdge 2646)=independentCachedBranchMembers447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound447
def independentCachedBranchMembers449 : Finset ℕ := ([48,252,1652,1720,1740,2614,2618,2620,2638,2668,2702,2730,2732,2772,2776,2800,3118,3164,3186,3188,3192,3228,3250,3252,3256,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers449 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers449 6 (fun x => (if x<2776 then (if x<2620 then (if x<1720 then (if x<252 then 0 else (if x<1652 then 0 else 0)) else (if x<2614 then (if x<1740 then 0 else 0) else (if x<2618 then 1 else 2))) else (if x<2702 then (if x<2638 then 3 else (if x<2668 then 1 else 2)) else (if x<2732 then (if x<2730 then 2 else 1) else (if x<2772 then 4 else 3)))) else (if x<3228 then (if x<3164 then (if x<2800 then 2 else (if x<3118 then 4 else 1)) else (if x<3188 then (if x<3186 then 3 else 4) else (if x<3192 then 5 else 2))) else (if x<3270 then (if x<3252 then (if x<3250 then 5 else 1) else (if x<3256 then 3 else 4)) else (if x<3300 then (if x<3274 then 3 else 1) else (if x<3304 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers450 : Finset ℕ := ([48,252,1740,2614,2638,2668,2776,3164,3192,3250,3252,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers450 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers450 5 (fun x => (if x<2776 then (if x<2614 then (if x<252 then 0 else (if x<1740 then 0 else 0)) else (if x<2638 then 1 else (if x<2668 then 1 else 2))) else (if x<3250 then (if x<3164 then 2 else (if x<3192 then 2 else 3)) else (if x<3274 then (if x<3252 then 1 else 3) else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers451 : Finset ℕ := ([48,252,1652,1720,1740,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3164,3186,3188,3192,3228,3250,3252,3256,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers451 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers451 2662 5
  · have he : independentCachedBranchMembers451.erase 2662=independentCachedBranchMembers449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound449
  · have he : independentCachedBranchMembers451.filter (independentCachedEdge 2662)=independentCachedBranchMembers450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound450
def independentCachedBranchMembers452 : Finset ℕ := ([1652,1720,1740,2620,2662,2730,2800,3164,3186,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers452 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers452 5 (fun x => (if x<3164 then (if x<2620 then (if x<1720 then 0 else (if x<1740 then 0 else 0)) else (if x<2730 then (if x<2662 then 1 else 1) else (if x<2800 then 1 else 1))) else (if x<3270 then (if x<3228 then (if x<3186 then 2 else 2) else (if x<3250 then 3 else 3)) else (if x<3300 then (if x<3274 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers453 : Finset ℕ := ([48,252,1652,1720,1740,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3164,3186,3188,3192,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers453 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers453 3276 5
  · have he : independentCachedBranchMembers453.erase 3276=independentCachedBranchMembers451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound451
  · have he : independentCachedBranchMembers453.filter (independentCachedEdge 3276)=independentCachedBranchMembers452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound452
def independentCachedBranchMembers454 : Finset ℕ := ([48,252,1740,2614,2620,2638,2732,2772,2800,3188,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers454 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers454 5 (fun x => (if x<2772 then (if x<2614 then (if x<252 then 0 else (if x<1740 then 0 else 0)) else (if x<2638 then (if x<2620 then 1 else 2) else (if x<2732 then 1 else 1))) else (if x<3250 then (if x<3188 then (if x<2800 then 1 else 2) else (if x<3228 then 2 else 3)) else (if x<3274 then (if x<3256 then 3 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers455 : Finset ℕ := ([48,252,1652,1720,1740,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers455 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers455 3226 5
  · have he : independentCachedBranchMembers455.erase 3226=independentCachedBranchMembers453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound453
  · have he : independentCachedBranchMembers455.filter (independentCachedEdge 3226)=independentCachedBranchMembers454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound454
def independentCachedBranchMembers456 : Finset ℕ := ([48,252,1740,2618,2620,2668,2702,2776,2800,3164,3186,3188,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers456 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers456 5 (fun x => (if x<2776 then (if x<2618 then (if x<252 then 0 else (if x<1740 then 0 else 0)) else (if x<2668 then (if x<2620 then 1 else 2) else (if x<2702 then 1 else 1))) else (if x<3188 then (if x<3164 then (if x<2800 then 1 else 2) else (if x<3186 then 3 else 3)) else (if x<3270 then (if x<3256 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers457 : Finset ℕ := ([48,252,1652,1720,1740,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers457 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers457 3158 5
  · have he : independentCachedBranchMembers457.erase 3158=independentCachedBranchMembers455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound455
  · have he : independentCachedBranchMembers457.filter (independentCachedEdge 3158)=independentCachedBranchMembers456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound456
def independentCachedBranchMembers458 : Finset ℕ := ([48,252,2618,2620,2638,2662,2730,2732,2776,2800,3118,3164,3186,3188,3256,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers458 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers458 5 (fun x => (if x<2800 then (if x<2638 then (if x<2618 then (if x<252 then 0 else 0) else (if x<2620 then 1 else 0)) else (if x<2730 then (if x<2662 then 1 else 2) else (if x<2732 then 2 else (if x<2776 then 1 else 1)))) else (if x<3188 then (if x<3164 then (if x<3118 then 0 else 1) else (if x<3186 then 3 else 3)) else (if x<3274 then (if x<3256 then 0 else 0) else (if x<3276 then 3 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers459 : Finset ℕ := ([48,252,1652,1686,1720,1740,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers459 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers459 1686 5
  · have he : independentCachedBranchMembers459.erase 1686=independentCachedBranchMembers457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound457
  · have he : independentCachedBranchMembers459.filter (independentCachedEdge 1686)=independentCachedBranchMembers458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound458
def independentCachedBranchMembers460 : Finset ℕ := ([48,252,2614,2620,2662,2668,2702,2730,2772,2800,3118,3188,3228,3250,3256,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers460 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers460 5 (fun x => (if x<2800 then (if x<2662 then (if x<2614 then (if x<252 then 0 else 0) else (if x<2620 then 1 else 0)) else (if x<2702 then (if x<2668 then 2 else 1) else (if x<2730 then 1 else (if x<2772 then 2 else 1)))) else (if x<3250 then (if x<3188 then (if x<3118 then 0 else 1) else (if x<3228 then 0 else 3)) else (if x<3270 then (if x<3256 then 3 else 0) else (if x<3276 then 3 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers461 : Finset ℕ := ([48,252,1626,1652,1686,1720,1740,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers461 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers461 1626 5
  · have he : independentCachedBranchMembers461.erase 1626=independentCachedBranchMembers459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound459
  · have he : independentCachedBranchMembers461.filter (independentCachedEdge 1626)=independentCachedBranchMembers460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound460
def independentCachedBranchMembers462 : Finset ℕ := ([1652,1720,2614,2620,2638,2662,2668,2730,2776,2800,3118,3158,3164,3188,3226,3250,3256,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers462 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers462 5 (fun x => (if x<2800 then (if x<2638 then (if x<2614 then (if x<1720 then 0 else 0) else (if x<2620 then 1 else 0)) else (if x<2668 then (if x<2662 then 1 else 0) else (if x<2730 then 2 else (if x<2776 then 0 else 2)))) else (if x<3226 then (if x<3158 then (if x<3118 then 0 else 1) else (if x<3164 then 1 else (if x<3188 then 2 else 3))) else (if x<3256 then (if x<3250 then 2 else 1) else (if x<3274 then 3 else (if x<3304 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers463 : Finset ℕ := ([48,132,252,1626,1652,1686,1720,1740,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers463 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers463 132 5
  · have he : independentCachedBranchMembers463.erase 132=independentCachedBranchMembers461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound461
  · have he : independentCachedBranchMembers463.filter (independentCachedEdge 132)=independentCachedBranchMembers462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound462
def independentCachedBranchMembers464 : Finset ℕ := ([1652,1720,2618,2620,2662,2702,2730,2732,2772,2800,3118,3158,3186,3188,3226,3228,3256,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers464 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers464 5 (fun x => (if x<2800 then (if x<2662 then (if x<2618 then (if x<1720 then 0 else 0) else (if x<2620 then 1 else 0)) else (if x<2730 then (if x<2702 then 0 else 1) else (if x<2732 then 0 else (if x<2772 then 2 else 2)))) else (if x<3226 then (if x<3158 then (if x<3118 then 0 else 1) else (if x<3186 then 2 else (if x<3188 then 1 else 3))) else (if x<3256 then (if x<3228 then 1 else 2) else (if x<3270 then 3 else (if x<3300 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers465 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1720,1740,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers465 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers465 72 5
  · have he : independentCachedBranchMembers465.erase 72=independentCachedBranchMembers463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound463
  · have he : independentCachedBranchMembers465.filter (independentCachedEdge 72)=independentCachedBranchMembers464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound464
def independentCachedBranchMembers466 : Finset ℕ := ([48,132,1686,1720,1740,2618,2620,2638,2662,2702,2772,3118,3164,3186,3188,3226,3228,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers466 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers466 5 (fun x => (if x<2772 then (if x<2618 then (if x<1686 then (if x<132 then 0 else 0) else (if x<1720 then 1 else (if x<1740 then 1 else 0))) else (if x<2638 then (if x<2620 then 0 else 2) else (if x<2662 then 2 else (if x<2702 then 3 else 0)))) else (if x<3226 then (if x<3164 then (if x<3118 then 2 else 2) else (if x<3186 then 2 else (if x<3188 then 0 else 3))) else (if x<3252 then (if x<3228 then 1 else (if x<3250 then 3 else 4)) else (if x<3270 then 1 else (if x<3304 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers467 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1720,1740,1768,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers467 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers467 1768 5
  · have he : independentCachedBranchMembers467.erase 1768=independentCachedBranchMembers465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound465
  · have he : independentCachedBranchMembers467.filter (independentCachedEdge 1768)=independentCachedBranchMembers466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound466
def independentCachedBranchMembers468 : Finset ℕ := ([48,72,1686,1720,1740,2614,2618,2638,2668,2730,2800,3118,3158,3188,3192,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers468 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers468 5 (fun x => (if x<2800 then (if x<2614 then (if x<1686 then (if x<72 then 0 else 0) else (if x<1720 then 1 else (if x<1740 then 1 else 0))) else (if x<2638 then (if x<2618 then 0 else 2) else (if x<2668 then 0 else (if x<2730 then 2 else 3)))) else (if x<3228 then (if x<3158 then (if x<3118 then 2 else 2) else (if x<3188 then 1 else (if x<3192 then 3 else 1))) else (if x<3274 then (if x<3250 then 1 else (if x<3270 then 0 else 4)) else (if x<3300 then 0 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers469 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1692,1720,1740,1768,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers469 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers469 1692 5
  · have he : independentCachedBranchMembers469.erase 1692=independentCachedBranchMembers467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound467
  · have he : independentCachedBranchMembers469.filter (independentCachedEdge 1692)=independentCachedBranchMembers468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound468
def independentCachedBranchMembers470 : Finset ℕ := ([48,72,1626,1652,1740,1768,2614,2620,2638,2702,2730,2776,3118,3158,3164,3186,3192,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers470 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers470 5 (fun x => (if x<2776 then (if x<1768 then (if x<1626 then (if x<72 then 0 else 0) else (if x<1652 then 1 else (if x<1740 then 1 else 0))) else (if x<2638 then (if x<2614 then 1 else (if x<2620 then 0 else 2)) else (if x<2702 then 0 else (if x<2730 then 2 else 3)))) else (if x<3192 then (if x<3158 then (if x<3118 then 2 else 2) else (if x<3164 then 1 else (if x<3186 then 3 else 4))) else (if x<3256 then (if x<3228 then 1 else (if x<3250 then 2 else 0)) else (if x<3274 then 3 else (if x<3300 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers471 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1692,1720,1740,1764,1768,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers471 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers471 1764 5
  · have he : independentCachedBranchMembers471.erase 1764=independentCachedBranchMembers469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound469
  · have he : independentCachedBranchMembers471.filter (independentCachedEdge 1764)=independentCachedBranchMembers470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound470
def independentCachedBranchMembers472 : Finset ℕ := ([48,132,1626,1652,1692,1740,2614,2618,2662,2702,2732,2800,3118,3164,3186,3226,3252,3256,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers472 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers472 5 (fun x => (if x<2800 then (if x<1740 then (if x<1626 then (if x<132 then 0 else 0) else (if x<1652 then 1 else (if x<1692 then 1 else 1))) else (if x<2662 then (if x<2614 then 0 else (if x<2618 then 2 else 0)) else (if x<2702 then 3 else (if x<2732 then 0 else 2)))) else (if x<3252 then (if x<3164 then (if x<3118 then 2 else 2) else (if x<3186 then 1 else (if x<3226 then 0 else 1))) else (if x<3274 then (if x<3256 then 1 else (if x<3270 then 3 else 0)) else (if x<3300 then 4 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers473 : Finset ℕ := ([48,72,132,252,1626,1628,1652,1686,1692,1720,1740,1764,1768,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers473 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers473 1628 5
  · have he : independentCachedBranchMembers473.erase 1628=independentCachedBranchMembers471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound471
  · have he : independentCachedBranchMembers473.filter (independentCachedEdge 1628)=independentCachedBranchMembers472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound472
def independentCachedBranchMembers474 : Finset ℕ := ([132,252,1626,1652,1686,1720,1740,2614,2618,2638,2668,2702,2732,2772,2776,3164,3186,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers474 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers474 5 (fun x => (if x<2702 then (if x<1720 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1686 then 1 else 1))) else (if x<2618 then (if x<1740 then 1 else (if x<2614 then 0 else 2)) else (if x<2638 then 3 else (if x<2668 then 2 else 3)))) else (if x<3228 then (if x<2776 then (if x<2732 then 3 else (if x<2772 then 0 else 0)) else (if x<3164 then 3 else (if x<3186 then 4 else 4))) else (if x<3274 then (if x<3250 then 0 else (if x<3270 then 2 else 4)) else (if x<3300 then 2 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers475 : Finset ℕ := ([1652,1720,2618,2702,2732,2772,3186,3228,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers475 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers475 4 (fun x => (if x<2772 then (if x<2618 then (if x<1720 then 0 else 0) else (if x<2702 then 1 else (if x<2732 then 1 else 2))) else (if x<3228 then (if x<3186 then 2 else 1) else (if x<3270 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers476 : Finset ℕ := ([72,132,252,1626,1652,1686,1720,1740,2614,2618,2638,2668,2702,2732,2772,2776,3164,3186,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers476 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers476 72 4
  · have he : independentCachedBranchMembers476.erase 72=independentCachedBranchMembers474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound474
  · have he : independentCachedBranchMembers476.filter (independentCachedEdge 72)=independentCachedBranchMembers475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound475
def independentCachedBranchMembers477 : Finset ℕ := ([1626,1686,2668,2732,2772,2776,3164,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers477 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers477 4 (fun x => (if x<2776 then (if x<2668 then (if x<1686 then 0 else 0) else (if x<2732 then 1 else (if x<2772 then 2 else 1))) else (if x<3228 then (if x<3164 then 2 else 1) else (if x<3300 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers478 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1720,1740,2614,2618,2638,2668,2702,2732,2772,2776,3164,3186,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers478 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers478 48 4
  · have he : independentCachedBranchMembers478.erase 48=independentCachedBranchMembers476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound476
  · have he : independentCachedBranchMembers478.filter (independentCachedEdge 48)=independentCachedBranchMembers477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound477
def independentCachedBranchMembers479 : Finset ℕ := ([48,72,132,252,1626,1628,1652,1686,1692,1720,1740,1764,1768,2614,2618,2620,2638,2662,2668,2702,2730,2732,2772,2776,2800,3118,3158,3164,3186,3188,3192,3226,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers479 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers479 3298 5
  · have he : independentCachedBranchMembers479.erase 3298=independentCachedBranchMembers473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound473
  · have he : independentCachedBranchMembers479.filter (independentCachedEdge 3298)=independentCachedBranchMembers478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound478
def independentCachedBranchMembers480 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers480 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers480 2606 6
  · have he : independentCachedBranchMembers480.erase 2606=independentCachedBranchMembers448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound448
  · have he : independentCachedBranchMembers480.filter (independentCachedEdge 2606)=independentCachedBranchMembers479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound479
def independentCachedBranchMembers481 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2662,2680,2730,2740,2764,3180,3186,3244,3250,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers481 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers481 6 (fun x => (if x<1746 then (if x<1628 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1594 then (if x<1590 then 0 else 1) else (if x<1614 then 2 else 1))) else (if x<1692 then (if x<1652 then (if x<1642 then 2 else 3) else (if x<1678 then 3 else 2)) else (if x<1720 then (if x<1702 then 1 else 3) else (if x<1740 then 3 else 0)))) else (if x<3180 then (if x<2680 then (if x<1768 then (if x<1764 then 1 else 1) else (if x<2662 then 2 else 3)) else (if x<2740 then (if x<2730 then 2 else 2) else (if x<2764 then 3 else 2))) else (if x<3270 then (if x<3244 then (if x<3186 then 4 else 4) else (if x<3250 then 5 else 5)) else (if x<3284 then (if x<3274 then 4 else 5) else (if x<3288 then 5 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers482 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1652,1678,1720,1740,2680,2740,2764,3186,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers482 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers482 5 (fun x => (if x<1720 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1614 then (if x<1594 then 1 else 2) else (if x<1652 then 1 else (if x<1678 then 2 else 3)))) else (if x<2764 then (if x<2680 then (if x<1740 then 3 else 0) else (if x<2740 then 2 else 1)) else (if x<3250 then (if x<3186 then 1 else 2) else (if x<3270 then 1 else (if x<3274 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers483 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2662,2680,2730,2740,2764,3180,3186,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers483 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers483 3298 5
  · have he : independentCachedBranchMembers483.erase 3298=independentCachedBranchMembers481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound481
  · have he : independentCachedBranchMembers483.filter (independentCachedEdge 3298)=independentCachedBranchMembers482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound482
def independentCachedBranchMembers484 : Finset ℕ := ([48,72,132,252,1590,1614,1628,1642,1702,1740,1768,2680,2740,2764,3180,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers484 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers484 5 (fun x => (if x<1740 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1628 then (if x<1614 then 1 else 1) else (if x<1642 then 2 else (if x<1702 then 2 else 3)))) else (if x<2764 then (if x<2680 then (if x<1768 then 0 else 3) else (if x<2740 then 2 else 1)) else (if x<3250 then (if x<3180 then 1 else 2) else (if x<3274 then 1 else (if x<3288 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers485 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2662,2680,2730,2740,2764,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers485 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers485 3226 5
  · have he : independentCachedBranchMembers485.erase 3226=independentCachedBranchMembers483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound483
  · have he : independentCachedBranchMembers485.filter (independentCachedEdge 3226)=independentCachedBranchMembers484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound484
def independentCachedBranchMembers486 : Finset ℕ := ([48,72,132,252,1594,1642,1678,1692,1702,1740,1764,2680,2740,2764,3186,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers486 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers486 5 (fun x => (if x<1740 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1642 then 1 else 2) else (if x<1692 then 1 else (if x<1702 then 3 else 2)))) else (if x<2764 then (if x<2680 then (if x<1764 then 0 else 3) else (if x<2740 then 1 else 2)) else (if x<3244 then (if x<3186 then 1 else 1) else (if x<3270 then 3 else (if x<3284 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers487 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2662,2680,2730,2740,2764,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers487 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers487 3158 5
  · have he : independentCachedBranchMembers487.erase 3158=independentCachedBranchMembers485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound485
  · have he : independentCachedBranchMembers487.filter (independentCachedEdge 3158)=independentCachedBranchMembers486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound486
def independentCachedBranchMembers488 : Finset ℕ := ([72,132,252,1628,1692,1720,1740,1764,1768,2680,2740,2764,3180,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers488 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers488 5 (fun x => (if x<1768 then (if x<1692 then (if x<252 then (if x<132 then 0 else 0) else (if x<1628 then 0 else 1)) else (if x<1740 then (if x<1720 then 2 else 1) else (if x<1764 then 0 else 1))) else (if x<3180 then (if x<2740 then (if x<2680 then 2 else 3) else (if x<2764 then 3 else 2)) else (if x<3284 then (if x<3244 then 4 else 2) else (if x<3288 then 4 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers489 : Finset ℕ := ([72,132,1628,1764,2764,3244,3288] : List ℕ).toFinset
theorem independentCachedBranchBound489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers489 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers489 4 (fun x => (if x<1764 then (if x<132 then 0 else (if x<1628 then 0 else 1)) else (if x<3244 then (if x<2764 then 1 else 0) else (if x<3288 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers490 : Finset ℕ := ([72,132,252,1628,1652,1692,1720,1740,1764,1768,2680,2740,2764,3180,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers490 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers490 1652 4
  · have he : independentCachedBranchMembers490.erase 1652=independentCachedBranchMembers488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound488
  · have he : independentCachedBranchMembers490.filter (independentCachedEdge 1652)=independentCachedBranchMembers489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound489
def independentCachedBranchMembers491 : Finset ℕ := ([1628,1692,1764,1768,3180,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers491 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers491 4 (fun x => (if x<3180 then (if x<1764 then (if x<1692 then 0 else 1) else (if x<1768 then 0 else 1)) else (if x<3284 then (if x<3244 then 0 else 1) else (if x<3288 then 0 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers492 : Finset ℕ := ([48,72,132,252,1628,1652,1692,1720,1740,1764,1768,2680,2740,2764,3180,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers492 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers492 48 4
  · have he : independentCachedBranchMembers492.erase 48=independentCachedBranchMembers490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound490
  · have he : independentCachedBranchMembers492.filter (independentCachedEdge 48)=independentCachedBranchMembers491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound491
def independentCachedBranchMembers493 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2662,2680,2730,2740,2764,3118,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers493 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers493 3118 5
  · have he : independentCachedBranchMembers493.erase 3118=independentCachedBranchMembers487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound487
  · have he : independentCachedBranchMembers493.filter (independentCachedEdge 3118)=independentCachedBranchMembers492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound492
def independentCachedBranchMembers494 : Finset ℕ := ([48,132,1594,1614,1628,1652,1678,1692,1702,1746,1768,2680,2730,2764,3118,3186,3226,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers494 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers494 5 (fun x => (if x<1768 then (if x<1652 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1614 then 0 else (if x<1628 then 1 else 2))) else (if x<1692 then (if x<1678 then 1 else 0) else (if x<1702 then 1 else (if x<1746 then 1 else 1)))) else (if x<3186 then (if x<2730 then (if x<2680 then 1 else 0) else (if x<2764 then 2 else (if x<3118 then 0 else 3))) else (if x<3250 then (if x<3226 then 0 else 3) else (if x<3270 then 2 else (if x<3284 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers495 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2662,2680,2730,2740,2764,2792,3118,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers495 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers495 2792 5
  · have he : independentCachedBranchMembers495.erase 2792=independentCachedBranchMembers493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound493
  · have he : independentCachedBranchMembers495.filter (independentCachedEdge 2792)=independentCachedBranchMembers494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound494
def independentCachedBranchMembers496 : Finset ℕ := ([72,252,1590,1594,1628,1642,1678,1720,1746,1764,1768,2680,2730,2764,3158,3180,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers496 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers496 5 (fun x => (if x<1768 then (if x<1642 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1594 then 1 else (if x<1628 then 2 else 0))) else (if x<1720 then (if x<1678 then 1 else 1) else (if x<1746 then 1 else (if x<1764 then 1 else 1)))) else (if x<3180 then (if x<2730 then (if x<2680 then 0 else 0) else (if x<2764 then 2 else (if x<3158 then 0 else 3))) else (if x<3284 then (if x<3250 then 0 else 2) else (if x<3288 then 2 else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers497 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2662,2680,2702,2730,2740,2764,2792,3118,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers497 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers497 2702 5
  · have he : independentCachedBranchMembers497.erase 2702=independentCachedBranchMembers495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound495
  · have he : independentCachedBranchMembers497.filter (independentCachedEdge 2702)=independentCachedBranchMembers496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound496
def independentCachedBranchMembers498 : Finset ℕ := ([48,132,1590,1594,1628,1642,1678,1720,1746,1764,1768,2680,2730,2764,3118,3186,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers498 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers498 5 (fun x => (if x<1768 then (if x<1642 then (if x<1590 then (if x<132 then 0 else 0) else (if x<1594 then 1 else (if x<1628 then 0 else 1))) else (if x<1720 then (if x<1678 then 1 else 0) else (if x<1746 then 1 else (if x<1764 then 1 else 1)))) else (if x<3186 then (if x<2730 then (if x<2680 then 2 else 0) else (if x<2764 then 2 else (if x<3118 then 0 else 3))) else (if x<3244 then (if x<3226 then 0 else 3) else (if x<3270 then 2 else (if x<3274 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers499 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2652,2662,2680,2702,2730,2740,2764,2792,3118,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers499 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers499 2652 5
  · have he : independentCachedBranchMembers499.erase 2652=independentCachedBranchMembers497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound497
  · have he : independentCachedBranchMembers499.filter (independentCachedEdge 2652)=independentCachedBranchMembers498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound498
def independentCachedBranchMembers500 : Finset ℕ := ([72,252,1594,1614,1628,1652,1678,1692,1702,1746,1768,2680,2730,2764,3158,3180,3244,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers500 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers500 5 (fun x => (if x<1768 then (if x<1652 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1614 then 1 else (if x<1628 then 1 else 0))) else (if x<1692 then (if x<1678 then 1 else 2) else (if x<1702 then 1 else (if x<1746 then 1 else 1)))) else (if x<3180 then (if x<2730 then (if x<2680 then 0 else 0) else (if x<2764 then 2 else (if x<3158 then 0 else 3))) else (if x<3274 then (if x<3244 then 0 else 2) else (if x<3288 then 2 else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers501 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2680,2702,2730,2740,2764,2792,3118,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers501 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers501 2618 5
  · have he : independentCachedBranchMembers501.erase 2618=independentCachedBranchMembers499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound499
  · have he : independentCachedBranchMembers501.filter (independentCachedEdge 2618)=independentCachedBranchMembers500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound500
def independentCachedBranchMembers502 : Finset ℕ := ([48,72,1590,1614,1628,1642,1678,1692,1720,1746,1764,2618,2662,2740,2764,2792,3118,3158,3186,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers502 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers502 5 (fun x => (if x<2618 then (if x<1642 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else (if x<1628 then 0 else 1))) else (if x<1720 then (if x<1678 then 1 else (if x<1692 then 1 else 2)) else (if x<1746 then 1 else (if x<1764 then 1 else 1)))) else (if x<3118 then (if x<2740 then (if x<2662 then 3 else 2) else (if x<2764 then 0 else (if x<2792 then 0 else 3))) else (if x<3250 then (if x<3158 then 4 else (if x<3186 then 4 else 2)) else (if x<3274 then 0 else (if x<3288 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers503 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2680,2702,2730,2740,2764,2788,2792,3118,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers503 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers503 2788 5
  · have he : independentCachedBranchMembers503.erase 2788=independentCachedBranchMembers501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound501
  · have he : independentCachedBranchMembers503.filter (independentCachedEdge 2788)=independentCachedBranchMembers502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound502
def independentCachedBranchMembers504 : Finset ℕ := ([48,72,1590,1594,1614,1652,1692,1702,1746,1764,1768,2652,2662,2702,2740,2764,3118,3158,3180,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers504 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers504 5 (fun x => (if x<2652 then (if x<1652 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1594 then 0 else (if x<1614 then 1 else 0))) else (if x<1746 then (if x<1692 then 1 else (if x<1702 then 1 else 1)) else (if x<1764 then 1 else (if x<1768 then 2 else 1)))) else (if x<3118 then (if x<2702 then (if x<2662 then 3 else 2) else (if x<2740 then 3 else (if x<2764 then 0 else 0))) else (if x<3250 then (if x<3158 then 4 else (if x<3180 then 4 else 2)) else (if x<3270 then 0 else (if x<3274 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers505 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2680,2702,2716,2730,2740,2764,2788,2792,3118,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers505 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers505 2716 5
  · have he : independentCachedBranchMembers505.erase 2716=independentCachedBranchMembers503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound503
  · have he : independentCachedBranchMembers505.filter (independentCachedEdge 2716)=independentCachedBranchMembers504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound504
def independentCachedBranchMembers506 : Finset ℕ := ([132,252,1594,1614,1652,1692,1702,1746,1764,1768,2652,2662,2702,2740,2764,3186,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers506 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers506 5 (fun x => (if x<2652 then (if x<1692 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1614 then 1 else (if x<1652 then 1 else 1))) else (if x<1746 then (if x<1702 then 0 else 1) else (if x<1764 then 1 else (if x<1768 then 0 else 1)))) else (if x<3186 then (if x<2702 then (if x<2662 then 2 else 2) else (if x<2740 then 2 else (if x<2764 then 0 else 0))) else (if x<3284 then (if x<3226 then 3 else (if x<3244 then 3 else 0)) else (if x<3288 then 0 else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers507 : Finset ℕ := ([132,252,1594,1652,1702,1768,2652,2702,3226,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers507 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers507 4 (fun x => (if x<2652 then (if x<1652 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1702 then 1 else (if x<1768 then 1 else 1))) else (if x<3244 then (if x<2702 then 2 else (if x<3226 then 2 else 3)) else (if x<3284 then 0 else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers508 : Finset ℕ := ([132,252,1590,1594,1614,1652,1692,1702,1746,1764,1768,2652,2662,2702,2740,2764,3186,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers508 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers508 1590 4
  · have he : independentCachedBranchMembers508.erase 1590=independentCachedBranchMembers506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound506
  · have he : independentCachedBranchMembers508.filter (independentCachedEdge 1590)=independentCachedBranchMembers507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound507
def independentCachedBranchMembers509 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2618,2638,2652,2662,2680,2702,2716,2730,2740,2764,2788,2792,3118,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers509 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers509 2638 5
  · have he : independentCachedBranchMembers509.erase 2638=independentCachedBranchMembers505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound505
  · have he : independentCachedBranchMembers509.filter (independentCachedEdge 2638)=independentCachedBranchMembers508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound508
def independentCachedBranchMembers510 : Finset ℕ := ([132,252,1590,1628,1642,1678,1692,1720,1746,1764,2618,2662,2740,2764,2792,3180,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers510 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers510 5 (fun x => (if x<2618 then (if x<1678 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1628 then 1 else (if x<1642 then 1 else 1))) else (if x<1720 then (if x<1692 then 1 else 0) else (if x<1746 then 1 else (if x<1764 then 1 else 0)))) else (if x<3180 then (if x<2740 then (if x<2662 then 2 else 2) else (if x<2764 then 0 else (if x<2792 then 0 else 2))) else (if x<3270 then (if x<3226 then 3 else (if x<3244 then 4 else 0)) else (if x<3284 then 3 else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers511 : Finset ℕ := ([132,252,1628,1642,1678,1720,2618,2792,3226,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers511 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers511 4 (fun x => (if x<2618 then (if x<1642 then (if x<252 then 0 else (if x<1628 then 0 else 1)) else (if x<1678 then 1 else (if x<1720 then 1 else 1))) else (if x<3244 then (if x<2792 then 2 else (if x<3226 then 2 else 3)) else (if x<3284 then 0 else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
