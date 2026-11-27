/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch3
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers512 : Finset ℕ := ([132,252,1590,1614,1628,1642,1678,1692,1720,1746,1764,2618,2662,2740,2764,2792,3180,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers512 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers512 1614 4
  · have he : independentCachedBranchMembers512.erase 1614=independentCachedBranchMembers510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound510
  · have he : independentCachedBranchMembers512.filter (independentCachedEdge 1614)=independentCachedBranchMembers511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound511
def independentCachedBranchMembers513 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2614,2618,2638,2652,2662,2680,2702,2716,2730,2740,2764,2788,2792,3118,3158,3180,3186,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers513 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers513 2614 5
  · have he : independentCachedBranchMembers513.erase 2614=independentCachedBranchMembers509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound509
  · have he : independentCachedBranchMembers513.filter (independentCachedEdge 2614)=independentCachedBranchMembers512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound512
def independentCachedBranchMembers514 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers514 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers514 3282 6
  · have he : independentCachedBranchMembers514.erase 3282=independentCachedBranchMembers480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound480
  · have he : independentCachedBranchMembers514.filter (independentCachedEdge 3282)=independentCachedBranchMembers513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound513
def independentCachedBranchMembers515 : Finset ℕ := ([1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2620,2650,2662,2668,2674,2702,2738,2772,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers515 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers515 6 (fun x => (if x<2738 then (if x<1764 then (if x<1686 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1740 then (if x<1692 then 0 else 2) else (if x<1746 then 1 else 1))) else (if x<2662 then (if x<2620 then (if x<1776 then 2 else 0) else (if x<2650 then 3 else 3)) else (if x<2674 then (if x<2668 then 2 else 1) else (if x<2702 then 1 else 3)))) else (if x<3192 then (if x<3126 then (if x<2792 then (if x<2772 then 0 else 0) else (if x<3102 then 3 else 3)) else (if x<3180 then (if x<3150 then 4 else 4) else (if x<3186 then 5 else 5))) else (if x<3256 then (if x<3238 then (if x<3226 then 3 else 2) else (if x<3244 then 5 else 3)) else (if x<3284 then (if x<3274 then 5 else 3) else (if x<3298 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers516 : Finset ℕ := ([1594,1652,1686,1740,2620,2662,2674,2738,2792,3126,3150,3180,3192,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers516 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers516 5 (fun x => (if x<3126 then (if x<2620 then (if x<1686 then (if x<1652 then 0 else 0) else (if x<1740 then 0 else 1)) else (if x<2674 then (if x<2662 then 2 else 2) else (if x<2738 then 1 else (if x<2792 then 2 else 1)))) else (if x<3226 then (if x<3180 then (if x<3150 then 0 else 3) else (if x<3192 then 2 else 0)) else (if x<3256 then (if x<3244 then 0 else 1) else (if x<3284 then 2 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers517 : Finset ℕ := ([1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2620,2650,2662,2668,2674,2702,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers517 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers517 2786 5
  · have he : independentCachedBranchMembers517.erase 2786=independentCachedBranchMembers515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound515
  · have he : independentCachedBranchMembers517.filter (independentCachedEdge 2786)=independentCachedBranchMembers516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound516
def independentCachedBranchMembers518 : Finset ℕ := ([1628,1642,1740,1776,2650,2662,2668,2702,2738,3126,3150,3186,3192,3226,3238,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers518 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers518 5 (fun x => (if x<3126 then (if x<2650 then (if x<1740 then (if x<1642 then 0 else 0) else (if x<1776 then 1 else 0)) else (if x<2668 then (if x<2662 then 2 else 2) else (if x<2702 then 1 else (if x<2738 then 1 else 2)))) else (if x<3226 then (if x<3186 then (if x<3150 then 3 else 0) else (if x<3192 then 2 else 0)) else (if x<3244 then (if x<3238 then 2 else 2) else (if x<3284 then 1 else (if x<3298 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers519 : Finset ℕ := ([1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2620,2650,2662,2668,2674,2702,2714,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers519 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers519 2714 5
  · have he : independentCachedBranchMembers519.erase 2714=independentCachedBranchMembers517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound517
  · have he : independentCachedBranchMembers519.filter (independentCachedEdge 2714)=independentCachedBranchMembers518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound518
def independentCachedBranchMembers520 : Finset ℕ := ([1642,1652,1692,1764,2620,2650,2662,2702,2738,2772,2792,3126,3150,3180,3186,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers520 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers520 5 (fun x => (if x<2772 then (if x<2620 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1764 then 1 else 1)) else (if x<2662 then (if x<2650 then 2 else 2) else (if x<2702 then 0 else (if x<2738 then 2 else 2)))) else (if x<3186 then (if x<3126 then (if x<2792 then 0 else 2) else (if x<3150 then 3 else (if x<3180 then 3 else 4))) else (if x<3238 then (if x<3226 then 4 else 1) else (if x<3256 then 4 else (if x<3298 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers521 : Finset ℕ := ([1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2620,2650,2662,2668,2674,2702,2714,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3250,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers521 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers521 3250 5
  · have he : independentCachedBranchMembers521.erase 3250=independentCachedBranchMembers519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound519
  · have he : independentCachedBranchMembers521.filter (independentCachedEdge 3250)=independentCachedBranchMembers520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound520
def independentCachedBranchMembers522 : Finset ℕ := ([1692,1740,1746,1764,2620,2650,2668,2674,2702,2792,3102,3126,3150,3192,3226,3244,3250,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers522 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers522 5 (fun x => (if x<3102 then (if x<2650 then (if x<1746 then (if x<1740 then 0 else 1) else (if x<1764 then 0 else (if x<2620 then 0 else 2))) else (if x<2674 then (if x<2668 then 2 else 1) else (if x<2702 then 1 else (if x<2792 then 2 else 2)))) else (if x<3244 then (if x<3150 then (if x<3126 then 2 else 3) else (if x<3192 then 3 else (if x<3226 then 2 else 0))) else (if x<3274 then (if x<3250 then 0 else 1) else (if x<3284 then 2 else (if x<3298 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers523 : Finset ℕ := ([1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2620,2650,2662,2668,2674,2680,2702,2714,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3250,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers523 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers523 2680 5
  · have he : independentCachedBranchMembers523.erase 2680=independentCachedBranchMembers521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound521
  · have he : independentCachedBranchMembers523.filter (independentCachedEdge 2680)=independentCachedBranchMembers522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound522
def independentCachedBranchMembers524 : Finset ℕ := ([1594,1652,1686,1692,1746,1764,2650,2662,2668,2702,2738,3126,3150,3186,3192,3226,3238,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers524 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers524 5 (fun x => (if x<2738 then (if x<1764 then (if x<1686 then (if x<1652 then 0 else 0) else (if x<1692 then 0 else (if x<1746 then 1 else 1))) else (if x<2662 then (if x<2650 then 1 else 2) else (if x<2668 then 2 else (if x<2702 then 3 else 2)))) else (if x<3226 then (if x<3150 then (if x<3126 then 2 else 0) else (if x<3186 then 2 else (if x<3192 then 2 else 0))) else (if x<3244 then (if x<3238 then 0 else 2) else (if x<3284 then 1 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers525 : Finset ℕ := ([1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2620,2638,2650,2662,2668,2674,2680,2702,2714,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3250,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers525 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers525 2638 5
  · have he : independentCachedBranchMembers525.erase 2638=independentCachedBranchMembers523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound523
  · have he : independentCachedBranchMembers525.filter (independentCachedEdge 2638)=independentCachedBranchMembers524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound524
def independentCachedBranchMembers526 : Finset ℕ := ([1628,1642,1692,1746,1764,1776,2620,2662,2674,2738,2792,3126,3150,3180,3192,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers526 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers526 5 (fun x => (if x<2792 then (if x<1776 then (if x<1692 then (if x<1642 then 0 else 0) else (if x<1746 then 1 else (if x<1764 then 0 else 0))) else (if x<2662 then (if x<2620 then 1 else 2) else (if x<2674 then 2 else (if x<2738 then 1 else 2)))) else (if x<3226 then (if x<3150 then (if x<3126 then 2 else 2) else (if x<3180 then 3 else (if x<3192 then 0 else 3))) else (if x<3256 then (if x<3244 then 3 else 3) else (if x<3284 then 2 else (if x<3298 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers527 : Finset ℕ := ([1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2614,2620,2638,2650,2662,2668,2674,2680,2702,2714,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3250,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers527 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers527 2614 5
  · have he : independentCachedBranchMembers527.erase 2614=independentCachedBranchMembers525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound525
  · have he : independentCachedBranchMembers527.filter (independentCachedEdge 2614)=independentCachedBranchMembers526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound526
def independentCachedBranchMembers528 : Finset ℕ := ([1594,1652,1692,1746,1764,1776,2620,2662,2674,2702,2714,2772,2786,3102,3186,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers528 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers528 5 (fun x => (if x<2714 then (if x<1776 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1746 then 0 else (if x<1764 then 0 else 1))) else (if x<2662 then (if x<2620 then 2 else 0) else (if x<2674 then 1 else (if x<2702 then 0 else 2)))) else (if x<3226 then (if x<2786 then (if x<2772 then 0 else 0) else (if x<3102 then 2 else (if x<3186 then 2 else 2))) else (if x<3256 then (if x<3244 then 1 else 3) else (if x<3284 then 4 else (if x<3298 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers529 : Finset ℕ := ([72,1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2614,2620,2638,2650,2662,2668,2674,2680,2702,2714,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3250,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers529 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers529 72 5
  · have he : independentCachedBranchMembers529.erase 72=independentCachedBranchMembers527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound527
  · have he : independentCachedBranchMembers529.filter (independentCachedEdge 72)=independentCachedBranchMembers528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound528
def independentCachedBranchMembers530 : Finset ℕ := ([1628,1642,1686,1692,1746,1764,2650,2662,2668,2714,2772,2786,2792,3102,3180,3226,3238,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers530 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers530 5 (fun x => (if x<2772 then (if x<1764 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1692 then 1 else (if x<1746 then 2 else 0))) else (if x<2662 then (if x<2650 then 0 else 0) else (if x<2668 then 2 else (if x<2714 then 0 else 1)))) else (if x<3226 then (if x<2792 then (if x<2786 then 0 else 0) else (if x<3102 then 1 else (if x<3180 then 1 else 1))) else (if x<3244 then (if x<3238 then 2 else 3) else (if x<3284 then 4 else (if x<3298 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers531 : Finset ℕ := ([48,72,1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2614,2620,2638,2650,2662,2668,2674,2680,2702,2714,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3250,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers531 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers531 48 5
  · have he : independentCachedBranchMembers531.erase 48=independentCachedBranchMembers529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound529
  · have he : independentCachedBranchMembers531.filter (independentCachedEdge 48)=independentCachedBranchMembers530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound530
def independentCachedBranchMembers532 : Finset ℕ := ([48,1594,1628,1652,1692,1746,2620,2638,2650,2662,2674,2702,2714,2738,2772,2792,3102,3126,3180,3192,3244,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers532 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers532 5 (fun x => (if x<2714 then (if x<2620 then (if x<1652 then (if x<1594 then 0 else (if x<1628 then 0 else 1)) else (if x<1692 then 0 else (if x<1746 then 2 else 1))) else (if x<2662 then (if x<2638 then 0 else (if x<2650 then 3 else 1)) else (if x<2674 then 2 else (if x<2702 then 0 else 2)))) else (if x<3180 then (if x<2792 then (if x<2738 then 3 else (if x<2772 then 1 else 1)) else (if x<3102 then 3 else (if x<3126 then 3 else 0))) else (if x<3256 then (if x<3192 then 3 else (if x<3244 then 0 else 4)) else (if x<3274 then 3 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers533 : Finset ℕ := ([48,72,1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2614,2620,2638,2650,2662,2668,2674,2680,2702,2714,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers533 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers533 3304 5
  · have he : independentCachedBranchMembers533.erase 3304=independentCachedBranchMembers531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound531
  · have he : independentCachedBranchMembers533.filter (independentCachedEdge 3304)=independentCachedBranchMembers532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound532
def independentCachedBranchMembers534 : Finset ℕ := ([72,1594,1628,1642,1746,1764,2614,2620,2650,2662,2668,2702,2738,2772,2786,2792,3102,3150,3186,3192,3226,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers534 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers534 5 (fun x => (if x<2738 then (if x<2614 then (if x<1642 then (if x<1594 then 0 else (if x<1628 then 1 else 0)) else (if x<1746 then 0 else (if x<1764 then 1 else 2))) else (if x<2662 then (if x<2620 then 3 else (if x<2650 then 1 else 0)) else (if x<2668 then 2 else (if x<2702 then 0 else 3)))) else (if x<3186 then (if x<2792 then (if x<2772 then 1 else (if x<2786 then 1 else 3)) else (if x<3102 then 2 else (if x<3150 then 3 else 0))) else (if x<3238 then (if x<3192 then 3 else (if x<3226 then 0 else 4)) else (if x<3244 then 3 else (if x<3274 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers535 : Finset ℕ := ([48,72,1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2614,2620,2638,2650,2662,2668,2674,2680,2702,2714,2738,2772,2786,2792,3102,3126,3150,3180,3186,3192,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers535 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers535 3214 5
  · have he : independentCachedBranchMembers535.erase 3214=independentCachedBranchMembers533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound533
  · have he : independentCachedBranchMembers535.filter (independentCachedEdge 3214)=independentCachedBranchMembers534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound534
def independentCachedBranchMembers536 : Finset ℕ := ([1594,1628,1686,1692,1764,1776,2614,2620,2638,2650,2702,2714,2786,2792,3102,3180,3186,3192,3238,3244,3250,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers536 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers536 5 (fun x => (if x<2786 then (if x<2614 then (if x<1692 then (if x<1628 then 0 else (if x<1686 then 0 else 0)) else (if x<1764 then 1 else (if x<1776 then 1 else 0))) else (if x<2650 then (if x<2620 then 2 else (if x<2638 then 3 else 2)) else (if x<2702 then 3 else (if x<2714 then 3 else 1)))) else (if x<3238 then (if x<3180 then (if x<2792 then 1 else (if x<3102 then 3 else 0)) else (if x<3186 then 4 else (if x<3192 then 4 else 0))) else (if x<3256 then (if x<3244 then 4 else (if x<3250 then 3 else 0)) else (if x<3274 then 4 else (if x<3284 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers537 : Finset ℕ := ([48,72,1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2614,2620,2638,2650,2662,2668,2674,2680,2702,2714,2738,2762,2772,2786,2792,3102,3126,3150,3180,3186,3192,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers537 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers537 2762 5
  · have he : independentCachedBranchMembers537.erase 2762=independentCachedBranchMembers535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound535
  · have he : independentCachedBranchMembers537.filter (independentCachedEdge 2762)=independentCachedBranchMembers536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound536
def independentCachedBranchMembers538 : Finset ℕ := ([48,72,1594,1628,1642,1652,1686,1776,2620,2650,2668,2674,2702,2792,3102,3126,3150,3192,3226,3244,3250,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers538 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers538 5 (fun x => (if x<2702 then (if x<1686 then (if x<1628 then (if x<72 then 0 else (if x<1594 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 2 else 2))) else (if x<2650 then (if x<1776 then 1 else (if x<2620 then 1 else 3)) else (if x<2668 then 3 else (if x<2674 then 2 else 2)))) else (if x<3226 then (if x<3126 then (if x<2792 then 3 else (if x<3102 then 3 else 1)) else (if x<3150 then 0 else (if x<3192 then 0 else 0))) else (if x<3274 then (if x<3244 then 4 else (if x<3250 then 3 else 1)) else (if x<3284 then 3 else (if x<3298 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers539 : Finset ℕ := ([48,72,1594,1628,1642,1652,1686,1692,1740,1746,1764,1776,2614,2620,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2762,2772,2786,2792,3102,3126,3150,3180,3186,3192,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers539 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers539 2732 5
  · have he : independentCachedBranchMembers539.erase 2732=independentCachedBranchMembers537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound537
  · have he : independentCachedBranchMembers539.filter (independentCachedEdge 2732)=independentCachedBranchMembers538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound538
def independentCachedBranchMembers540 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1748,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers540 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers540 1748 6
  · have he : independentCachedBranchMembers540.erase 1748=independentCachedBranchMembers514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound514
  · have he : independentCachedBranchMembers540.filter (independentCachedEdge 1748)=independentCachedBranchMembers539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound539
def independentCachedBranchMembers541 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2710,2732,2762,2800,3102,3118,3158,3180,3186,3192,3228,3238,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers541 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers541 6 (fun x => (if x<2710 then (if x<1746 then (if x<1642 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1626 then 0 else 1)) else (if x<1678 then (if x<1652 then 2 else 2) else (if x<1740 then 1 else 2))) else (if x<2646 then (if x<2606 then (if x<1768 then 0 else 1) else (if x<2618 then 0 else 3)) else (if x<2662 then (if x<2652 then 0 else 3) else (if x<2668 then 3 else (if x<2674 then 2 else 2))))) else (if x<3186 then (if x<3102 then (if x<2762 then (if x<2732 then 3 else 1) else (if x<2800 then 0 else 3)) else (if x<3158 then (if x<3118 then 4 else 5) else (if x<3180 then 5 else 4))) else (if x<3250 then (if x<3228 then (if x<3192 then 4 else 5) else (if x<3238 then 5 else 4)) else (if x<3274 then (if x<3256 then 5 else 4) else (if x<3284 then 4 else (if x<3300 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers542 : Finset ℕ := ([1590,1614,1642,1652,2618,2652,2662,2710,2732,2762,2800,3118,3158,3180,3186,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers542 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers542 5 (fun x => (if x<2762 then (if x<2618 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<2662 then (if x<2652 then 2 else 2) else (if x<2710 then 0 else (if x<2732 then 2 else 2)))) else (if x<3186 then (if x<3118 then (if x<2800 then 0 else 2) else (if x<3158 then 3 else (if x<3180 then 3 else 1))) else (if x<3238 then (if x<3228 then 1 else 3) else (if x<3256 then 4 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers543 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2710,2732,2762,2800,3102,3118,3158,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers543 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers543 3244 5
  · have he : independentCachedBranchMembers543.erase 3244=independentCachedBranchMembers541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound541
  · have he : independentCachedBranchMembers543.filter (independentCachedEdge 3244)=independentCachedBranchMembers542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound542
def independentCachedBranchMembers544 : Finset ℕ := ([1590,1596,1614,1642,1678,1746,2618,2662,2668,2732,2800,3118,3158,3186,3192,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers544 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers544 5 (fun x => (if x<2800 then (if x<1746 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1642 then 0 else (if x<1678 then 1 else 1))) else (if x<2662 then (if x<2618 then 0 else 2) else (if x<2668 then 2 else (if x<2732 then 3 else 2)))) else (if x<3228 then (if x<3158 then (if x<3118 then 2 else 0) else (if x<3186 then 0 else (if x<3192 then 2 else 1))) else (if x<3256 then (if x<3250 then 1 else 0) else (if x<3274 then 2 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers545 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2710,2732,2762,2788,2800,3102,3118,3158,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers545 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers545 2788 5
  · have he : independentCachedBranchMembers545.erase 2788=independentCachedBranchMembers543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound543
  · have he : independentCachedBranchMembers545.filter (independentCachedEdge 2788)=independentCachedBranchMembers544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound544
def independentCachedBranchMembers546 : Finset ℕ := ([1590,1614,1626,1652,1746,1768,2652,2662,2674,2710,2732,3118,3158,3180,3192,3228,3238,3250,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers546 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers546 5 (fun x => (if x<2732 then (if x<1768 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else (if x<1746 then 1 else 0))) else (if x<2662 then (if x<2652 then 1 else 2) else (if x<2674 then 2 else (if x<2710 then 3 else 2)))) else (if x<3228 then (if x<3158 then (if x<3118 then 2 else 0) else (if x<3180 then 0 else (if x<3192 then 2 else 1))) else (if x<3250 then (if x<3238 then 2 else 2) else (if x<3274 then 0 else (if x<3300 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers547 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2710,2716,2732,2762,2788,2800,3102,3118,3158,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers547 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers547 2716 5
  · have he : independentCachedBranchMembers547.erase 2716=independentCachedBranchMembers545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound545
  · have he : independentCachedBranchMembers547.filter (independentCachedEdge 2716)=independentCachedBranchMembers546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound546
def independentCachedBranchMembers548 : Finset ℕ := ([1590,1614,1740,1746,2618,2652,2668,2674,2710,2800,3102,3118,3158,3192,3228,3244,3250,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers548 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers548 5 (fun x => (if x<3102 then (if x<2652 then (if x<1740 then (if x<1614 then 0 else 0) else (if x<1746 then 1 else (if x<2618 then 0 else 1))) else (if x<2674 then (if x<2668 then 1 else 2) else (if x<2710 then 2 else (if x<2800 then 3 else 3)))) else (if x<3244 then (if x<3158 then (if x<3118 then 3 else 0) else (if x<3192 then 0 else (if x<3228 then 2 else 4))) else (if x<3274 then (if x<3250 then 2 else 0) else (if x<3284 then 0 else (if x<3300 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers549 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2680,2710,2716,2732,2762,2788,2800,3102,3118,3158,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers549 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers549 2680 5
  · have he : independentCachedBranchMembers549.erase 2680=independentCachedBranchMembers547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound547
  · have he : independentCachedBranchMembers549.filter (independentCachedEdge 2680)=independentCachedBranchMembers548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound548
def independentCachedBranchMembers550 : Finset ℕ := ([1590,1614,1626,1642,1678,1746,2606,2618,2646,2662,2674,2710,2762,3102,3118,3158,3186,3238,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers550 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers550 5 (fun x => (if x<2674 then (if x<1746 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1642 then 1 else (if x<1678 then 2 else 1))) else (if x<2618 then (if x<2606 then 0 else 0) else (if x<2646 then 2 else (if x<2662 then 0 else 2)))) else (if x<3158 then (if x<2762 then (if x<2710 then 1 else 2) else (if x<3102 then 0 else (if x<3118 then 3 else 4))) else (if x<3238 then (if x<3186 then 4 else 3) else (if x<3250 then 3 else (if x<3274 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers551 : Finset ℕ := ([252,1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2680,2710,2716,2732,2762,2788,2800,3102,3118,3158,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers551 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers551 252 5
  · have he : independentCachedBranchMembers551.erase 252=independentCachedBranchMembers549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound549
  · have he : independentCachedBranchMembers551.filter (independentCachedEdge 252)=independentCachedBranchMembers550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound550
def independentCachedBranchMembers552 : Finset ℕ := ([1590,1596,1614,1652,1746,1768,2606,2646,2652,2662,2668,2762,2800,3102,3118,3158,3180,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers552 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers552 5 (fun x => (if x<2668 then (if x<1768 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1652 then 0 else (if x<1746 then 2 else 0))) else (if x<2646 then (if x<2606 then 1 else 0) else (if x<2652 then 0 else (if x<2662 then 2 else 2)))) else (if x<3158 then (if x<2800 then (if x<2762 then 1 else 0) else (if x<3102 then 2 else (if x<3118 then 3 else 4))) else (if x<3250 then (if x<3180 then 4 else 3) else (if x<3256 then 4 else (if x<3274 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers553 : Finset ℕ := ([132,252,1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2680,2710,2716,2732,2762,2788,2800,3102,3118,3158,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers553 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers553 132 5
  · have he : independentCachedBranchMembers553.erase 132=independentCachedBranchMembers551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound551
  · have he : independentCachedBranchMembers553.filter (independentCachedEdge 132)=independentCachedBranchMembers552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound552
def independentCachedBranchMembers554 : Finset ℕ := ([1590,1642,1678,1746,1768,2606,2618,2652,2662,2674,2710,2732,2762,2788,2800,3102,3158,3180,3192,3228,3238,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers554 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers554 5 (fun x => (if x<2732 then (if x<2606 then (if x<1678 then (if x<1642 then 0 else 0) else (if x<1746 then 0 else (if x<1768 then 0 else 1))) else (if x<2662 then (if x<2618 then 0 else (if x<2652 then 2 else 2)) else (if x<2674 then 2 else (if x<2710 then 0 else 0)))) else (if x<3180 then (if x<2800 then (if x<2762 then 1 else (if x<2788 then 0 else 3)) else (if x<3102 then 1 else (if x<3158 then 3 else 4))) else (if x<3238 then (if x<3192 then 3 else (if x<3228 then 4 else 4)) else (if x<3250 then 3 else (if x<3284 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers555 : Finset ℕ := ([1590,1746,1768,2606,2652,2662,2762,2800,3102,3158,3180,3250] : List ℕ).toFinset
theorem independentCachedBranchBound555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers555 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers555 4 (fun x => (if x<2762 then (if x<2606 then (if x<1746 then 0 else (if x<1768 then 0 else 1)) else (if x<2652 then 0 else (if x<2662 then 2 else 2))) else (if x<3158 then (if x<2800 then 0 else (if x<3102 then 1 else 1)) else (if x<3180 then 2 else (if x<3250 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers556 : Finset ℕ := ([132,1590,1642,1678,1746,1768,2606,2618,2652,2662,2674,2710,2732,2762,2788,2800,3102,3158,3180,3192,3228,3238,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers556 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers556 132 4
  · have he : independentCachedBranchMembers556.erase 132=independentCachedBranchMembers554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound554
  · have he : independentCachedBranchMembers556.filter (independentCachedEdge 132)=independentCachedBranchMembers555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound555
def independentCachedBranchMembers557 : Finset ℕ := ([132,252,1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2680,2710,2716,2732,2762,2788,2800,3102,3118,3158,3164,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers557 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers557 3164 5
  · have he : independentCachedBranchMembers557.erase 3164=independentCachedBranchMembers553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound553
  · have he : independentCachedBranchMembers557.filter (independentCachedEdge 3164)=independentCachedBranchMembers556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound556
def independentCachedBranchMembers558 : Finset ℕ := ([1614,1652,1678,1746,1768,2618,2646,2652,2662,2668,2710,2716,2732,2762,2800,3102,3118,3186,3192,3250,3256,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers558 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers558 5 (fun x => (if x<2716 then (if x<2618 then (if x<1678 then (if x<1652 then 0 else 0) else (if x<1746 then 1 else (if x<1768 then 0 else 0))) else (if x<2662 then (if x<2646 then 2 else (if x<2652 then 0 else 2)) else (if x<2668 then 2 else (if x<2710 then 0 else 1)))) else (if x<3186 then (if x<2800 then (if x<2732 then 3 else (if x<2762 then 1 else 0)) else (if x<3102 then 0 else (if x<3118 then 3 else 4))) else (if x<3256 then (if x<3192 then 3 else (if x<3250 then 4 else 4)) else (if x<3284 then 3 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers559 : Finset ℕ := ([1614,1678,1746,2618,2646,2662,2710,2762,3102,3118,3186,3250] : List ℕ).toFinset
theorem independentCachedBranchBound559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers559 4 (fun x => (if x<2710 then (if x<2618 then (if x<1678 then 0 else (if x<1746 then 1 else 0)) else (if x<2646 then 2 else (if x<2662 then 0 else 2))) else (if x<3118 then (if x<2762 then 1 else (if x<3102 then 0 else 1)) else (if x<3186 then 2 else (if x<3250 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers560 : Finset ℕ := ([252,1614,1652,1678,1746,1768,2618,2646,2652,2662,2668,2710,2716,2732,2762,2800,3102,3118,3186,3192,3250,3256,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers560 252 4
  · have he : independentCachedBranchMembers560.erase 252=independentCachedBranchMembers558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound558
  · have he : independentCachedBranchMembers560.filter (independentCachedEdge 252)=independentCachedBranchMembers559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound559
def independentCachedBranchMembers561 : Finset ℕ := ([132,252,1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2680,2710,2716,2732,2762,2788,2800,3102,3118,3130,3158,3164,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers561 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers561 3130 5
  · have he : independentCachedBranchMembers561.erase 3130=independentCachedBranchMembers557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound557
  · have he : independentCachedBranchMembers561.filter (independentCachedEdge 3130)=independentCachedBranchMembers560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound560
def independentCachedBranchMembers562 : Finset ℕ := ([1590,1596,1614,1626,1678,1768,2606,2618,2646,2652,2710,2716,2788,2800,3102,3180,3186,3192,3238,3244,3250,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers562 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers562 5 (fun x => (if x<2788 then (if x<2606 then (if x<1626 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1678 then 1 else (if x<1768 then 1 else 1))) else (if x<2652 then (if x<2618 then 0 else (if x<2646 then 2 else 0)) else (if x<2710 then 2 else (if x<2716 then 2 else 3)))) else (if x<3238 then (if x<3180 then (if x<2800 then 3 else (if x<3102 then 2 else 0)) else (if x<3186 then 4 else (if x<3192 then 4 else 1))) else (if x<3256 then (if x<3244 then 4 else (if x<3250 then 1 else 2)) else (if x<3274 then 4 else (if x<3284 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers563 : Finset ℕ := ([132,252,1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2680,2710,2716,2732,2762,2772,2788,2800,3102,3118,3130,3158,3164,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers563 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers563 2772 5
  · have he : independentCachedBranchMembers563.erase 2772=independentCachedBranchMembers561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound561
  · have he : independentCachedBranchMembers563.filter (independentCachedEdge 2772)=independentCachedBranchMembers562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound562
def independentCachedBranchMembers564 : Finset ℕ := ([132,252,1596,1626,1642,1652,1678,1768,2618,2652,2668,2674,2710,2800,3102,3118,3158,3192,3228,3244,3250,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers564 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers564 5 (fun x => (if x<2710 then (if x<1678 then (if x<1626 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 2 else 2))) else (if x<2652 then (if x<1768 then 1 else (if x<2618 then 1 else 3)) else (if x<2668 then 3 else (if x<2674 then 2 else 2)))) else (if x<3228 then (if x<3118 then (if x<2800 then 3 else (if x<3102 then 3 else 1)) else (if x<3158 then 4 else (if x<3192 then 4 else 0))) else (if x<3274 then (if x<3244 then 0 else (if x<3250 then 1 else 3)) else (if x<3284 then 1 else (if x<3300 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers565 : Finset ℕ := ([132,252,1590,1596,1614,1626,1642,1652,1678,1740,1746,1768,2606,2618,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2762,2772,2788,2800,3102,3118,3130,3158,3164,3180,3186,3192,3228,3238,3244,3250,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers565 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers565 2738 5
  · have he : independentCachedBranchMembers565.erase 2738=independentCachedBranchMembers563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound563
  · have he : independentCachedBranchMembers565.filter (independentCachedEdge 2738)=independentCachedBranchMembers564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound564
def independentCachedBranchMembers566 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1738,1740,1746,1748,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers566 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers566 1738 6
  · have he : independentCachedBranchMembers566.erase 1738=independentCachedBranchMembers540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound540
  · have he : independentCachedBranchMembers566.filter (independentCachedEdge 1738)=independentCachedBranchMembers565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound565
def independentCachedBranchMembers567 : Finset ℕ := ([1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2702,2738,2758,2772,2776,2792,3102,3118,3158,3178,3188,3192,3228,3244,3250,3270,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers567 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers567 6 (fun x => (if x<2758 then (if x<1746 then (if x<1686 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1720 then (if x<1702 then 1 else 2) else (if x<1740 then 2 else 2))) else (if x<2646 then (if x<2606 then (if x<1776 then 0 else 1) else (if x<2620 then 0 else 3)) else (if x<2662 then (if x<2650 then 0 else 3) else (if x<2702 then 3 else (if x<2738 then 3 else 0))))) else (if x<3188 then (if x<3102 then (if x<2776 then (if x<2772 then 2 else 1) else (if x<2792 then 2 else 3)) else (if x<3158 then (if x<3118 then 4 else 5) else (if x<3178 then 5 else 4))) else (if x<3250 then (if x<3228 then (if x<3192 then 4 else 5) else (if x<3244 then 5 else 4)) else (if x<3274 then (if x<3270 then 4 else 4) else (if x<3288 then 5 else (if x<3300 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers568 : Finset ℕ := ([1590,1614,1702,1720,2620,2650,2662,2702,2738,2772,2792,3118,3158,3178,3188,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers568 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers568 5 (fun x => (if x<2772 then (if x<2620 then (if x<1702 then (if x<1614 then 0 else 0) else (if x<1720 then 1 else 1)) else (if x<2662 then (if x<2650 then 2 else 2) else (if x<2702 then 0 else (if x<2738 then 2 else 0)))) else (if x<3188 then (if x<3118 then (if x<2792 then 2 else 2) else (if x<3158 then 3 else (if x<3178 then 3 else 4))) else (if x<3270 then (if x<3228 then 4 else 3) else (if x<3288 then 1 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers569 : Finset ℕ := ([1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2702,2738,2758,2772,2776,2792,3102,3118,3158,3178,3188,3192,3228,3244,3250,3270,3274,3284,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers569 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers569 3284 5
  · have he : independentCachedBranchMembers569.erase 3284=independentCachedBranchMembers567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound567
  · have he : independentCachedBranchMembers569.filter (independentCachedEdge 3284)=independentCachedBranchMembers568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound568
def independentCachedBranchMembers570 : Finset ℕ := ([1590,1614,1628,1686,1720,1746,2650,2662,2758,2772,2792,3118,3158,3178,3192,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers570 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers570 5 (fun x => (if x<2792 then (if x<1746 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1686 then 1 else (if x<1720 then 1 else 1))) else (if x<2662 then (if x<2650 then 0 else 2) else (if x<2758 then 2 else (if x<2772 then 3 else 2)))) else (if x<3228 then (if x<3158 then (if x<3118 then 2 else 0) else (if x<3178 then 0 else (if x<3192 then 2 else 1))) else (if x<3274 then (if x<3250 then 1 else 0) else (if x<3288 then 0 else (if x<3300 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers571 : Finset ℕ := ([1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2702,2738,2758,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3228,3244,3250,3270,3274,3284,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers571 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers571 2788 5
  · have he : independentCachedBranchMembers571.erase 2788=independentCachedBranchMembers569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound569
  · have he : independentCachedBranchMembers571.filter (independentCachedEdge 2788)=independentCachedBranchMembers570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound570
def independentCachedBranchMembers572 : Finset ℕ := ([1590,1594,1614,1702,1746,1776,2620,2662,2702,2772,2776,3118,3158,3188,3192,3228,3250,3270,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers572 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers572 5 (fun x => (if x<2776 then (if x<1776 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1702 then 0 else (if x<1746 then 1 else 0))) else (if x<2662 then (if x<2620 then 1 else 2) else (if x<2702 then 2 else (if x<2772 then 2 else 2)))) else (if x<3228 then (if x<3158 then (if x<3118 then 3 else 0) else (if x<3188 then 0 else (if x<3192 then 2 else 1))) else (if x<3270 then (if x<3250 then 2 else 0) else (if x<3274 then 2 else (if x<3300 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers573 : Finset ℕ := ([1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2702,2716,2738,2758,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3228,3244,3250,3270,3274,3284,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers573 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers573 2716 5
  · have he : independentCachedBranchMembers573.erase 2716=independentCachedBranchMembers571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound571
  · have he : independentCachedBranchMembers573.filter (independentCachedEdge 2716)=independentCachedBranchMembers572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound572
def independentCachedBranchMembers574 : Finset ℕ := ([1590,1614,1740,1746,2620,2650,2702,2758,2776,2792,3102,3118,3158,3192,3228,3244,3250,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers574 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers574 5 (fun x => (if x<3102 then (if x<2650 then (if x<1740 then (if x<1614 then 0 else 0) else (if x<1746 then 1 else (if x<2620 then 0 else 2))) else (if x<2758 then (if x<2702 then 2 else 1) else (if x<2776 then 3 else (if x<2792 then 1 else 2)))) else (if x<3244 then (if x<3158 then (if x<3118 then 2 else 0) else (if x<3192 then 0 else (if x<3228 then 2 else 1))) else (if x<3274 then (if x<3250 then 2 else 0) else (if x<3284 then 0 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers575 : Finset ℕ := ([1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2680,2702,2716,2738,2758,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3228,3244,3250,3270,3274,3284,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers575 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers575 2680 5
  · have he : independentCachedBranchMembers575.erase 2680=independentCachedBranchMembers573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound573
  · have he : independentCachedBranchMembers575.filter (independentCachedEdge 2680)=independentCachedBranchMembers574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound574
def independentCachedBranchMembers576 : Finset ℕ := ([1590,1594,1614,1686,1702,1746,2606,2646,2650,2662,2702,2738,2758,3102,3118,3158,3178,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers576 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers576 5 (fun x => (if x<2702 then (if x<1746 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1686 then 0 else (if x<1702 then 1 else 2))) else (if x<2646 then (if x<2606 then 0 else 0) else (if x<2650 then 0 else (if x<2662 then 2 else 2)))) else (if x<3158 then (if x<2758 then (if x<2738 then 2 else 0) else (if x<3102 then 1 else (if x<3118 then 3 else 4))) else (if x<3250 then (if x<3178 then 4 else 3) else (if x<3270 then 3 else (if x<3274 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers577 : Finset ℕ := ([252,1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2680,2702,2716,2738,2758,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3228,3244,3250,3270,3274,3284,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers577 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers577 252 5
  · have he : independentCachedBranchMembers577.erase 252=independentCachedBranchMembers575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound575
  · have he : independentCachedBranchMembers577.filter (independentCachedEdge 252)=independentCachedBranchMembers576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound576
def independentCachedBranchMembers578 : Finset ℕ := ([1590,1628,1720,1746,1776,2620,2646,2662,2738,2776,2792,3102,3118,3158,3188,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers578 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers578 5 (fun x => (if x<2776 then (if x<1776 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2646 then (if x<2620 then 1 else 0) else (if x<2662 then 0 else (if x<2738 then 2 else 0)))) else (if x<3158 then (if x<3102 then (if x<2792 then 0 else 1) else (if x<3118 then 1 else 2)) else (if x<3250 then (if x<3188 then 2 else 3) else (if x<3274 then 3 else (if x<3288 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers579 : Finset ℕ := ([1628,1720,1776,2620,2776,2792,3188,3288] : List ℕ).toFinset
theorem independentCachedBranchBound579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers579 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers579 4 (fun x => (if x<2776 then (if x<1776 then (if x<1720 then 0 else 0) else (if x<2620 then 1 else 0)) else (if x<3188 then (if x<2792 then 0 else 1) else (if x<3288 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers580 : Finset ℕ := ([1590,1614,1628,1720,1746,1776,2620,2646,2662,2738,2776,2792,3102,3118,3158,3188,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers580 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers580 1614 4
  · have he : independentCachedBranchMembers580.erase 1614=independentCachedBranchMembers578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound578
  · have he : independentCachedBranchMembers580.filter (independentCachedEdge 1614)=independentCachedBranchMembers579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound579
def independentCachedBranchMembers581 : Finset ℕ := ([1628,1720,2620,2662,2776,3118,3158,3188,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers581 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers581 4 (fun x => (if x<3118 then (if x<2620 then (if x<1720 then 0 else 0) else (if x<2662 then 0 else (if x<2776 then 1 else 0))) else (if x<3188 then (if x<3158 then 1 else 1) else (if x<3250 then 2 else (if x<3274 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers582 : Finset ℕ := ([1590,1614,1628,1720,1746,1776,2606,2620,2646,2662,2738,2776,2792,3102,3118,3158,3188,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers582 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers582 2606 4
  · have he : independentCachedBranchMembers582.erase 2606=independentCachedBranchMembers580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound580
  · have he : independentCachedBranchMembers582.filter (independentCachedEdge 2606)=independentCachedBranchMembers581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound581
def independentCachedBranchMembers583 : Finset ℕ := ([132,252,1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2680,2702,2716,2738,2758,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3228,3244,3250,3270,3274,3284,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers583 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers583 132 5
  · have he : independentCachedBranchMembers583.erase 132=independentCachedBranchMembers577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound577
  · have he : independentCachedBranchMembers583.filter (independentCachedEdge 132)=independentCachedBranchMembers582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound582
def independentCachedBranchMembers584 : Finset ℕ := ([1594,1614,1628,1702,1746,2606,2620,2650,2662,2702,2716,2738,2758,2772,2792,3102,3158,3178,3192,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers584 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers584 5 (fun x => (if x<2738 then (if x<2606 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1702 then 1 else (if x<1746 then 0 else 0))) else (if x<2662 then (if x<2620 then 0 else (if x<2650 then 1 else 0)) else (if x<2702 then 2 else (if x<2716 then 2 else 3)))) else (if x<3178 then (if x<2792 then (if x<2758 then 0 else (if x<2772 then 0 else 1)) else (if x<3102 then 2 else (if x<3158 then 3 else 4))) else (if x<3274 then (if x<3192 then 3 else (if x<3244 then 4 else 3)) else (if x<3288 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers585 : Finset ℕ := ([1614,1628,1746,2606,2620,2662,2738,2792,3102,3158,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers585 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers585 4 (fun x => (if x<2738 then (if x<2606 then (if x<1628 then 0 else (if x<1746 then 1 else 0)) else (if x<2620 then 0 else (if x<2662 then 1 else 2))) else (if x<3158 then (if x<2792 then 0 else (if x<3102 then 2 else 1)) else (if x<3274 then 2 else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers586 : Finset ℕ := ([132,1594,1614,1628,1702,1746,2606,2620,2650,2662,2702,2716,2738,2758,2772,2792,3102,3158,3178,3192,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers586 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers586 132 4
  · have he : independentCachedBranchMembers586.erase 132=independentCachedBranchMembers584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound584
  · have he : independentCachedBranchMembers586.filter (independentCachedEdge 132)=independentCachedBranchMembers585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound585
def independentCachedBranchMembers587 : Finset ℕ := ([132,252,1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2680,2702,2716,2738,2758,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers587 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers587 3304 5
  · have he : independentCachedBranchMembers587.erase 3304=independentCachedBranchMembers583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound583
  · have he : independentCachedBranchMembers587.filter (independentCachedEdge 3304)=independentCachedBranchMembers586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound586
def independentCachedBranchMembers588 : Finset ℕ := ([1590,1594,1628,1720,1746,2620,2646,2650,2662,2702,2738,2772,2776,2788,2792,3102,3118,3188,3192,3228,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers588 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers588 5 (fun x => (if x<2772 then (if x<2620 then (if x<1628 then (if x<1594 then 0 else 1) else (if x<1720 then 0 else (if x<1746 then 0 else 0))) else (if x<2662 then (if x<2646 then 0 else (if x<2650 then 0 else 1)) else (if x<2702 then 2 else (if x<2738 then 2 else 0)))) else (if x<3188 then (if x<2792 then (if x<2776 then 1 else (if x<2788 then 0 else 3)) else (if x<3102 then 2 else (if x<3118 then 3 else 4))) else (if x<3244 then (if x<3192 then 3 else (if x<3228 then 4 else 4)) else (if x<3270 then 3 else (if x<3274 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers589 : Finset ℕ := ([1590,1594,1746,2646,2650,2662,2702,2738,3102,3118,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers589 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers589 4 (fun x => (if x<2702 then (if x<2646 then (if x<1594 then 0 else (if x<1746 then 1 else 0)) else (if x<2650 then 0 else (if x<2662 then 1 else 2))) else (if x<3118 then (if x<2738 then 2 else (if x<3102 then 0 else 1)) else (if x<3270 then 2 else (if x<3274 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers590 : Finset ℕ := ([252,1590,1594,1628,1720,1746,2620,2646,2650,2662,2702,2738,2772,2776,2788,2792,3102,3118,3188,3192,3228,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers590 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers590 252 4
  · have he : independentCachedBranchMembers590.erase 252=independentCachedBranchMembers588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound588
  · have he : independentCachedBranchMembers590.filter (independentCachedEdge 252)=independentCachedBranchMembers589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound589
def independentCachedBranchMembers591 : Finset ℕ := ([132,252,1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2680,2702,2716,2738,2758,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers591 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers591 3214 5
  · have he : independentCachedBranchMembers591.erase 3214=independentCachedBranchMembers587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound587
  · have he : independentCachedBranchMembers591.filter (independentCachedEdge 3214)=independentCachedBranchMembers590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound590
def independentCachedBranchMembers592 : Finset ℕ := ([132,252,1594,1628,1686,1702,1720,1776,2620,2650,2702,2758,2776,2792,3102,3118,3158,3192,3228,3244,3250,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers592 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers592 5 (fun x => (if x<2776 then (if x<1720 then (if x<1628 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1686 then 1 else (if x<1702 then 1 else 2))) else (if x<2650 then (if x<1776 then 2 else (if x<2620 then 1 else 3)) else (if x<2702 then 3 else (if x<2758 then 3 else 2)))) else (if x<3228 then (if x<3118 then (if x<2792 then 2 else (if x<3102 then 3 else 1)) else (if x<3158 then 4 else (if x<3192 then 4 else 0))) else (if x<3274 then (if x<3244 then 0 else (if x<3250 then 3 else 1)) else (if x<3284 then 3 else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers593 : Finset ℕ := ([132,252,1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2680,2702,2716,2738,2758,2762,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers593 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers593 2762 5
  · have he : independentCachedBranchMembers593.erase 2762=independentCachedBranchMembers591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound591
  · have he : independentCachedBranchMembers593.filter (independentCachedEdge 2762)=independentCachedBranchMembers592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound592
def independentCachedBranchMembers594 : Finset ℕ := ([1590,1594,1614,1628,1686,1776,2606,2620,2646,2650,2702,2716,2788,2792,3102,3178,3188,3192,3244,3250,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers594 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers594 5 (fun x => (if x<2788 then (if x<2606 then (if x<1628 then (if x<1594 then 0 else (if x<1614 then 1 else 0)) else (if x<1686 then 1 else (if x<1776 then 1 else 1))) else (if x<2650 then (if x<2620 then 0 else (if x<2646 then 2 else 0)) else (if x<2702 then 2 else (if x<2716 then 2 else 3)))) else (if x<3244 then (if x<3178 then (if x<2792 then 3 else (if x<3102 then 2 else 0)) else (if x<3188 then 4 else (if x<3192 then 4 else 1))) else (if x<3274 then (if x<3250 then 2 else (if x<3270 then 1 else 4)) else (if x<3284 then 2 else (if x<3288 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers595 : Finset ℕ := ([132,252,1590,1594,1614,1628,1686,1702,1720,1740,1746,1776,2606,2620,2646,2650,2662,2680,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers595 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers595 2732 5
  · have he : independentCachedBranchMembers595.erase 2732=independentCachedBranchMembers593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound593
  · have he : independentCachedBranchMembers595.filter (independentCachedEdge 2732)=independentCachedBranchMembers594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound594
def independentCachedBranchMembers596 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1714,1720,1738,1740,1746,1748,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers596 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers596 1714 6
  · have he : independentCachedBranchMembers596.erase 1714=independentCachedBranchMembers566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound566
  · have he : independentCachedBranchMembers596.filter (independentCachedEdge 1714)=independentCachedBranchMembers595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound595
def independentCachedBranchMembers597 : Finset ℕ := ([1596,1626,1678,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2732,2762,2800,3102,3126,3150,3192,3226,3244,3270,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers597 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers597 6 (fun x => (if x<2732 then (if x<1746 then (if x<1702 then (if x<1626 then 0 else (if x<1678 then 0 else 0)) else (if x<1720 then 1 else (if x<1740 then 1 else 1))) else (if x<2618 then (if x<1764 then 1 else (if x<1768 then 2 else 0)) else (if x<2662 then (if x<2652 then 2 else 3) else (if x<2710 then 2 else 3)))) else (if x<3192 then (if x<3102 then (if x<2762 then 0 else (if x<2800 then 0 else 2)) else (if x<3126 then 3 else (if x<3150 then 4 else 4))) else (if x<3270 then (if x<3226 then 3 else (if x<3244 then 4 else 1)) else (if x<3288 then (if x<3284 then 1 else 3) else (if x<3298 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers598 : Finset ℕ := ([1596,1678,1720,1740,2618,2762,2800,3126,3150,3192,3270] : List ℕ).toFinset
theorem independentCachedBranchBound598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers598 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers598 5 (fun x => (if x<2762 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<1740 then 1 else (if x<2618 then 1 else 1))) else (if x<3150 then (if x<2800 then 0 else (if x<3126 then 2 else 3)) else (if x<3192 then 2 else (if x<3270 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers599 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2732,2762,2800,3102,3126,3150,3192,3226,3244,3270,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers599 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers599 1692 5
  · have he : independentCachedBranchMembers599.erase 1692=independentCachedBranchMembers597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound597
  · have he : independentCachedBranchMembers599.filter (independentCachedEdge 1692)=independentCachedBranchMembers598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound598
def independentCachedBranchMembers600 : Finset ℕ := ([1596,1626,1678,1692,1764,1768,2662,2732,2762,3126,3150,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers600 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers600 5 (fun x => (if x<2662 then (if x<1692 then (if x<1626 then 0 else (if x<1678 then 0 else 0)) else (if x<1764 then 1 else (if x<1768 then 1 else 0))) else (if x<3126 then (if x<2732 then 1 else (if x<2762 then 0 else 0)) else (if x<3226 then (if x<3150 then 2 else 2) else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers601 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2732,2762,2800,3102,3126,3150,3192,3226,3244,3250,3270,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers601 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers601 3250 5
  · have he : independentCachedBranchMembers601.erase 3250=independentCachedBranchMembers599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound599
  · have he : independentCachedBranchMembers601.filter (independentCachedEdge 3250)=independentCachedBranchMembers600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound600
def independentCachedBranchMembers602 : Finset ℕ := ([1626,1692,1702,1720,1740,1746,1768,2618,2710,2732,3126,3192,3226,3284] : List ℕ).toFinset
theorem independentCachedBranchBound602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers602 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers602 5 (fun x => (if x<2618 then (if x<1720 then (if x<1692 then 0 else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3126 then (if x<2710 then 2 else (if x<2732 then 2 else 0)) else (if x<3226 then (if x<3192 then 2 else 2) else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers603 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2732,2762,2800,3102,3126,3150,3188,3192,3226,3244,3250,3270,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers603 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers603 3188 5
  · have he : independentCachedBranchMembers603.erase 3188=independentCachedBranchMembers601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound601
  · have he : independentCachedBranchMembers603.filter (independentCachedEdge 3188)=independentCachedBranchMembers602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound602
def independentCachedBranchMembers604 : Finset ℕ := ([1596,1678,1702,1720,1740,1746,1764,2652,2732,2800,3150,3192,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers604 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers604 5 (fun x => (if x<2652 then (if x<1720 then (if x<1678 then 0 else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3150 then (if x<2732 then 2 else (if x<2800 then 0 else 2)) else (if x<3284 then (if x<3192 then 2 else 2) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers605 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2732,2762,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers605 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers605 3178 5
  · have he : independentCachedBranchMembers605.erase 3178=independentCachedBranchMembers603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound603
  · have he : independentCachedBranchMembers605.filter (independentCachedEdge 3178)=independentCachedBranchMembers604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound604
def independentCachedBranchMembers606 : Finset ℕ := ([1596,1678,1764,2652,2662,2762,2800,3102,3150,3178,3188,3244,3250,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers606 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers606 5 (fun x => (if x<3150 then (if x<2662 then (if x<1764 then (if x<1678 then 0 else 0) else (if x<2652 then 0 else 1)) else (if x<2800 then (if x<2762 then 1 else 1) else (if x<3102 then 1 else 0))) else (if x<3250 then (if x<3188 then (if x<3178 then 1 else 2) else (if x<3244 then 0 else 0)) else (if x<3288 then (if x<3270 then 2 else 0) else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers607 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2732,2762,2776,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers607 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers607 2776 5
  · have he : independentCachedBranchMembers607.erase 2776=independentCachedBranchMembers605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound605
  · have he : independentCachedBranchMembers607.filter (independentCachedEdge 2776)=independentCachedBranchMembers606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound606
def independentCachedBranchMembers608 : Finset ℕ := ([1626,1692,1768,2618,2662,2710,2762,3102,3126,3178,3188,3226,3244,3250,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers608 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers608 5 (fun x => (if x<3126 then (if x<2662 then (if x<1768 then (if x<1692 then 0 else 0) else (if x<2618 then 0 else 1)) else (if x<2762 then (if x<2710 then 1 else 1) else (if x<3102 then 1 else 0))) else (if x<3244 then (if x<3188 then (if x<3178 then 1 else 0) else (if x<3226 then 2 else 1)) else (if x<3270 then (if x<3250 then 0 else 2) else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers609 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2732,2758,2762,2776,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers609 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers609 2758 5
  · have he : independentCachedBranchMembers609.erase 2758=independentCachedBranchMembers607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound607
  · have he : independentCachedBranchMembers609.filter (independentCachedEdge 2758)=independentCachedBranchMembers608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound608
def independentCachedBranchMembers610 : Finset ℕ := ([1626,1678,1720,1740,2652,2662,2758,2762,2800,3126,3150,3188,3192,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers610 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers610 5 (fun x => (if x<3126 then (if x<2652 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<1740 then 0 else 1)) else (if x<2758 then (if x<2662 then 1 else 2) else (if x<2762 then 1 else (if x<2800 then 2 else 2)))) else (if x<3226 then (if x<3188 then (if x<3150 then 3 else 0) else (if x<3192 then 2 else 0)) else (if x<3284 then (if x<3244 then 0 else 0) else (if x<3288 then 1 else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers611 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2732,2758,2762,2776,2786,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers611 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers611 2786 5
  · have he : independentCachedBranchMembers611.erase 2786=independentCachedBranchMembers609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound609
  · have he : independentCachedBranchMembers611.filter (independentCachedEdge 2786)=independentCachedBranchMembers610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound610
def independentCachedBranchMembers612 : Finset ℕ := ([1596,1702,1740,1768,2618,2662,2710,2762,2776,3126,3150,3178,3192,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers612 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers612 5 (fun x => (if x<3126 then (if x<2618 then (if x<1740 then (if x<1702 then 0 else 0) else (if x<1768 then 0 else 1)) else (if x<2710 then (if x<2662 then 2 else 2) else (if x<2762 then 1 else (if x<2776 then 1 else 3)))) else (if x<3226 then (if x<3178 then (if x<3150 then 0 else 4) else (if x<3192 then 1 else 3)) else (if x<3270 then (if x<3244 then 2 else 0) else (if x<3284 then 0 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers613 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2714,2732,2758,2762,2776,2786,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers613 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers613 2714 5
  · have he : independentCachedBranchMembers613.erase 2714=independentCachedBranchMembers611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound611
  · have he : independentCachedBranchMembers613.filter (independentCachedEdge 2714)=independentCachedBranchMembers612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound612
def independentCachedBranchMembers614 : Finset ℕ := ([1692,1702,1720,1764,2618,2652,2662,2710,2732,2762,2800,3126,3150,3178,3188,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers614 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers614 5 (fun x => (if x<2762 then (if x<2618 then (if x<1720 then (if x<1702 then 0 else 0) else (if x<1764 then 1 else 1)) else (if x<2662 then (if x<2652 then 1 else 0) else (if x<2710 then 0 else (if x<2732 then 0 else 0)))) else (if x<3188 then (if x<3126 then (if x<2800 then 2 else 1) else (if x<3150 then 2 else (if x<3178 then 2 else 3))) else (if x<3270 then (if x<3226 then 3 else 2) else (if x<3288 then 3 else (if x<3298 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers615 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2710,2714,2732,2758,2762,2776,2786,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers615 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers615 3274 5
  · have he : independentCachedBranchMembers615.erase 3274=independentCachedBranchMembers613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound613
  · have he : independentCachedBranchMembers615.filter (independentCachedEdge 3274)=independentCachedBranchMembers614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound614
def independentCachedBranchMembers616 : Finset ℕ := ([1692,1740,1746,1764,2618,2652,2710,2758,2776,2800,3102,3126,3150,3192,3226,3244,3250,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers616 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers616 5 (fun x => (if x<3102 then (if x<2652 then (if x<1746 then (if x<1740 then 0 else 1) else (if x<1764 then 0 else (if x<2618 then 0 else 1))) else (if x<2758 then (if x<2710 then 1 else 2) else (if x<2776 then 3 else (if x<2800 then 2 else 3)))) else (if x<3244 then (if x<3150 then (if x<3126 then 4 else 2) else (if x<3192 then 3 else (if x<3226 then 2 else 0))) else (if x<3274 then (if x<3250 then 0 else 1) else (if x<3284 then 4 else (if x<3298 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers617 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2652,2662,2680,2710,2714,2732,2758,2762,2776,2786,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers617 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers617 2680 5
  · have he : independentCachedBranchMembers617.erase 2680=independentCachedBranchMembers615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound615
  · have he : independentCachedBranchMembers617.filter (independentCachedEdge 2680)=independentCachedBranchMembers616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound616
def independentCachedBranchMembers618 : Finset ℕ := ([1596,1692,1702,1746,1764,1768,2652,2662,2758,2762,2800,3126,3150,3188,3192,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers618 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers618 5 (fun x => (if x<2800 then (if x<1768 then (if x<1702 then (if x<1692 then 0 else 1) else (if x<1746 then 0 else (if x<1764 then 1 else 1))) else (if x<2662 then (if x<2652 then 0 else 2) else (if x<2758 then 2 else (if x<2762 then 3 else 2)))) else (if x<3226 then (if x<3150 then (if x<3126 then 2 else 0) else (if x<3188 then 2 else (if x<3192 then 2 else 0))) else (if x<3284 then (if x<3244 then 1 else 0) else (if x<3288 then 1 else (if x<3298 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers619 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2618,2638,2652,2662,2680,2710,2714,2732,2758,2762,2776,2786,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers619 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers619 2638 5
  · have he : independentCachedBranchMembers619.erase 2638=independentCachedBranchMembers617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound617
  · have he : independentCachedBranchMembers619.filter (independentCachedEdge 2638)=independentCachedBranchMembers618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound618
def independentCachedBranchMembers620 : Finset ℕ := ([1626,1678,1692,1720,1746,1764,2618,2662,2710,2762,2776,3126,3150,3178,3192,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers620 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers620 5 (fun x => (if x<2776 then (if x<1764 then (if x<1692 then (if x<1678 then 0 else 0) else (if x<1720 then 1 else (if x<1746 then 0 else 1))) else (if x<2662 then (if x<2618 then 1 else 2) else (if x<2710 then 2 else (if x<2762 then 2 else 2)))) else (if x<3226 then (if x<3150 then (if x<3126 then 3 else 2) else (if x<3178 then 0 else (if x<3192 then 2 else 0))) else (if x<3270 then (if x<3244 then 0 else 0) else (if x<3284 then 2 else (if x<3298 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers621 : Finset ℕ := ([1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2614,2618,2638,2652,2662,2680,2710,2714,2732,2758,2762,2776,2786,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers621 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers621 2614 5
  · have he : independentCachedBranchMembers621.erase 2614=independentCachedBranchMembers619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound619
  · have he : independentCachedBranchMembers621.filter (independentCachedEdge 2614)=independentCachedBranchMembers620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound620
def independentCachedBranchMembers622 : Finset ℕ := ([1596,1678,1692,1720,1746,1764,2618,2662,2714,2732,2758,2786,2800,3102,3188,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers622 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers622 5 (fun x => (if x<2758 then (if x<1764 then (if x<1692 then (if x<1678 then 0 else 0) else (if x<1720 then 1 else (if x<1746 then 2 else 1))) else (if x<2662 then (if x<2618 then 0 else 2) else (if x<2714 then 2 else (if x<2732 then 1 else 0)))) else (if x<3226 then (if x<2800 then (if x<2786 then 0 else 1) else (if x<3102 then 2 else (if x<3188 then 3 else 3))) else (if x<3270 then (if x<3244 then 4 else 3) else (if x<3284 then 3 else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers623 : Finset ℕ := ([72,1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2614,2618,2638,2652,2662,2680,2710,2714,2732,2758,2762,2776,2786,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers623 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers623 72 5
  · have he : independentCachedBranchMembers623.erase 72=independentCachedBranchMembers621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound621
  · have he : independentCachedBranchMembers623.filter (independentCachedEdge 72)=independentCachedBranchMembers622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound622
def independentCachedBranchMembers624 : Finset ℕ := ([1626,1692,1702,1746,1764,1768,2652,2662,2710,2732,2776,2786,3102,3178,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers624 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers624 5 (fun x => (if x<2732 then (if x<1764 then (if x<1702 then (if x<1692 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2652 then (if x<1768 then 2 else 0) else (if x<2662 then 3 else (if x<2710 then 2 else 1)))) else (if x<3226 then (if x<2786 then (if x<2776 then 0 else 0) else (if x<3102 then 1 else (if x<3178 then 3 else 4))) else (if x<3284 then (if x<3244 then 2 else 4) else (if x<3288 then 3 else (if x<3298 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers625 : Finset ℕ := ([1702,1768,2662,2710,2776,3178,3226,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers625 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers625 4 (fun x => (if x<3178 then (if x<2662 then (if x<1768 then 0 else 0) else (if x<2710 then 1 else (if x<2776 then 0 else 0))) else (if x<3244 then (if x<3226 then 1 else 1) else (if x<3284 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers626 : Finset ℕ := ([1626,1692,1702,1746,1764,1768,2652,2662,2710,2714,2732,2776,2786,3102,3178,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers626 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers626 2714 4
  · have he : independentCachedBranchMembers626.erase 2714=independentCachedBranchMembers624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound624
  · have he : independentCachedBranchMembers626.filter (independentCachedEdge 2714)=independentCachedBranchMembers625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound625
def independentCachedBranchMembers627 : Finset ℕ := ([48,72,1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2614,2618,2638,2652,2662,2680,2710,2714,2732,2758,2762,2776,2786,2800,3102,3126,3150,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers627 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers627 48 5
  · have he : independentCachedBranchMembers627.erase 48=independentCachedBranchMembers623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound623
  · have he : independentCachedBranchMembers627.filter (independentCachedEdge 48)=independentCachedBranchMembers626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound626
def independentCachedBranchMembers628 : Finset ℕ := ([1678,1720,1746,1764,1768,2614,2618,2652,2662,2710,2714,2732,2758,2762,2800,3102,3150,3188,3192,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers628 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers628 5 (fun x => (if x<2732 then (if x<2614 then (if x<1746 then (if x<1720 then 0 else 0) else (if x<1764 then 0 else (if x<1768 then 0 else 1))) else (if x<2662 then (if x<2618 then 1 else (if x<2652 then 2 else 2)) else (if x<2710 then 2 else (if x<2714 then 2 else 0)))) else (if x<3188 then (if x<2800 then (if x<2758 then 0 else (if x<2762 then 0 else 2)) else (if x<3102 then 0 else (if x<3150 then 1 else 3))) else (if x<3284 then (if x<3192 then 3 else (if x<3250 then 4 else 4)) else (if x<3288 then 4 else (if x<3298 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers629 : Finset ℕ := ([1746,1764,1768,2652,2662,2710,2714,2732,3102,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers629 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers629 4 (fun x => (if x<2714 then (if x<2652 then (if x<1764 then 0 else (if x<1768 then 0 else 1)) else (if x<2662 then 2 else (if x<2710 then 2 else 1))) else (if x<3284 then (if x<2732 then 0 else (if x<3102 then 0 else 1)) else (if x<3288 then 3 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers630 : Finset ℕ := ([48,1678,1720,1746,1764,1768,2614,2618,2652,2662,2710,2714,2732,2758,2762,2800,3102,3150,3188,3192,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers630 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers630 48 4
  · have he : independentCachedBranchMembers630.erase 48=independentCachedBranchMembers628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound628
  · have he : independentCachedBranchMembers630.filter (independentCachedEdge 48)=independentCachedBranchMembers629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound629
def independentCachedBranchMembers631 : Finset ℕ := ([48,72,1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2614,2618,2638,2652,2662,2680,2710,2714,2732,2758,2762,2776,2786,2800,3102,3126,3150,3164,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers631 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers631 3164 5
  · have he : independentCachedBranchMembers631.erase 3164=independentCachedBranchMembers627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound627
  · have he : independentCachedBranchMembers631.filter (independentCachedEdge 3164)=independentCachedBranchMembers630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound630
def independentCachedBranchMembers632 : Finset ℕ := ([72,1678,1692,1702,1746,1768,2618,2638,2652,2662,2710,2732,2762,2776,2786,2800,3102,3126,3178,3192,3226,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers632 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers632 5 (fun x => (if x<2762 then (if x<2618 then (if x<1702 then (if x<1678 then 0 else (if x<1692 then 1 else 2)) else (if x<1746 then 0 else (if x<1768 then 1 else 0))) else (if x<2662 then (if x<2638 then 3 else (if x<2652 then 3 else 2)) else (if x<2710 then 2 else (if x<2732 then 0 else 1)))) else (if x<3178 then (if x<2800 then (if x<2776 then 1 else (if x<2786 then 0 else 3)) else (if x<3102 then 1 else (if x<3126 then 3 else 0))) else (if x<3250 then (if x<3192 then 3 else (if x<3226 then 0 else 4)) else (if x<3270 then 3 else (if x<3284 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers633 : Finset ℕ := ([48,72,1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2614,2618,2638,2652,2662,2680,2710,2714,2732,2758,2762,2776,2786,2800,3102,3126,3130,3150,3164,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers633 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers633 3130 5
  · have he : independentCachedBranchMembers633.erase 3130=independentCachedBranchMembers631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound631
  · have he : independentCachedBranchMembers633.filter (independentCachedEdge 3130)=independentCachedBranchMembers632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound632
def independentCachedBranchMembers634 : Finset ℕ := ([48,72,1596,1626,1678,1702,1720,1768,2618,2652,2710,2758,2776,2800,3102,3126,3150,3192,3226,3244,3250,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers634 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers634 5 (fun x => (if x<2776 then (if x<1720 then (if x<1626 then (if x<72 then 0 else (if x<1596 then 0 else 1)) else (if x<1678 then 1 else (if x<1702 then 1 else 2))) else (if x<2652 then (if x<1768 then 2 else (if x<2618 then 1 else 3)) else (if x<2710 then 3 else (if x<2758 then 3 else 2)))) else (if x<3226 then (if x<3126 then (if x<2800 then 2 else (if x<3102 then 3 else 1)) else (if x<3150 then 0 else (if x<3192 then 0 else 0))) else (if x<3274 then (if x<3244 then 4 else (if x<3250 then 1 else 3)) else (if x<3284 then 1 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers635 : Finset ℕ := ([48,72,1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2614,2618,2638,2652,2662,2680,2710,2714,2732,2758,2762,2772,2776,2786,2800,3102,3126,3130,3150,3164,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers635 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers635 2772 5
  · have he : independentCachedBranchMembers635.erase 2772=independentCachedBranchMembers633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound633
  · have he : independentCachedBranchMembers635.filter (independentCachedEdge 2772)=independentCachedBranchMembers634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound634
def independentCachedBranchMembers636 : Finset ℕ := ([1596,1626,1678,1692,1764,1768,2614,2618,2638,2652,2710,2714,2786,2800,3102,3178,3188,3192,3244,3250,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers636 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers636 5 (fun x => (if x<2786 then (if x<2614 then (if x<1692 then (if x<1626 then 0 else (if x<1678 then 0 else 0)) else (if x<1764 then 1 else (if x<1768 then 1 else 0))) else (if x<2652 then (if x<2618 then 2 else (if x<2638 then 3 else 2)) else (if x<2710 then 3 else (if x<2714 then 3 else 1)))) else (if x<3244 then (if x<3178 then (if x<2800 then 1 else (if x<3102 then 3 else 0)) else (if x<3188 then 4 else (if x<3192 then 4 else 0))) else (if x<3274 then (if x<3250 then 0 else (if x<3270 then 2 else 4)) else (if x<3284 then 0 else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers637 : Finset ℕ := ([48,72,1596,1626,1678,1692,1702,1720,1740,1746,1764,1768,2614,2618,2638,2652,2662,2680,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800,3102,3126,3130,3150,3164,3178,3188,3192,3226,3244,3250,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers637 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers637 2738 5
  · have he : independentCachedBranchMembers637.erase 2738=independentCachedBranchMembers635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound635
  · have he : independentCachedBranchMembers637.filter (independentCachedEdge 2738)=independentCachedBranchMembers636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound636
def independentCachedBranchMembers638 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1708,1714,1720,1738,1740,1746,1748,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers638 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers638 1708 6
  · have he : independentCachedBranchMembers638.erase 1708=independentCachedBranchMembers596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound596
  · have he : independentCachedBranchMembers638.filter (independentCachedEdge 1708)=independentCachedBranchMembers637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound637
def independentCachedBranchMembers639 : Finset ℕ := ([1590,1626,1628,1692,1702,1720,1738,1746,1748,1768,1776,2620,2638,2646,2674,2710,2730,2740,2776,2786,2788,3102,3130,3158,3178,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers639 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers639 6 (fun x => (if x<2730 then (if x<1748 then (if x<1702 then (if x<1628 then (if x<1626 then 0 else 0) else (if x<1692 then 1 else 0)) else (if x<1738 then (if x<1720 then 2 else 1) else (if x<1746 then 1 else 2))) else (if x<2638 then (if x<1776 then (if x<1768 then 3 else 2) else (if x<2620 then 0 else 1)) else (if x<2674 then (if x<2646 then 1 else 3) else (if x<2710 then 0 else 2)))) else (if x<3178 then (if x<2788 then (if x<2776 then (if x<2740 then 1 else 0) else (if x<2786 then 0 else 2)) else (if x<3130 then (if x<3102 then 3 else 4) else (if x<3158 then 5 else 5))) else (if x<3250 then (if x<3214 then (if x<3188 then 4 else 3) else (if x<3244 then 5 else 4)) else (if x<3270 then (if x<3252 then 4 else 5) else (if x<3288 then 3 else (if x<3298 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
