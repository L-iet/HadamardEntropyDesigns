/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch177
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8480 : Finset ℕ := ([18,40,72,130,252,1590,1622,1644,1650,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2732,2738,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8480 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8480 18 4
  · have he : independentCachedBranchMembers8480.erase 18=independentCachedBranchMembers8476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8476
  · have he : independentCachedBranchMembers8480.filter (independentCachedEdge 18)=independentCachedBranchMembers8479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8479
def independentCachedBranchMembers8481 : Finset ℕ := ([40,72,1590,1622,1702,1720,1734,1752,2662,2680,2710,2792,3174,3192,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8481 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8481 4 (fun x => (if x<2662 then (if x<1702 then (if x<1590 then (if x<72 then 0 else 1) else (if x<1622 then 1 else 0)) else (if x<1734 then (if x<1720 then 2 else 2) else (if x<1752 then 3 else 3))) else (if x<3174 then (if x<2710 then (if x<2680 then 2 else 2) else (if x<2792 then 0 else 1)) else (if x<3222 then (if x<3192 then 3 else 3) else (if x<3304 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8482 : Finset ℕ := ([12,18,40,72,130,252,1590,1622,1644,1650,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2732,2738,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8482 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8482 12 4
  · have he : independentCachedBranchMembers8482.erase 12=independentCachedBranchMembers8480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8480
  · have he : independentCachedBranchMembers8482.filter (independentCachedEdge 12)=independentCachedBranchMembers8481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8481
def independentCachedBranchMembers8483 : Finset ℕ := ([10,12,18,20,40,48,72,80,130,132,160,190,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2560,2590,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8483 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8483 10 5
  · have he : independentCachedBranchMembers8483.erase 10=independentCachedBranchMembers8457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8457
  · have he : independentCachedBranchMembers8483.filter (independentCachedEdge 10)=independentCachedBranchMembers8482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8482
def independentCachedBranchMembers8484 : Finset ℕ := ([10,12,18,20,34,36,40,48,66,68,72,80,130,132,136,144,160,190,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1638,1642,1644,1650,1652,1656,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8484 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8484 1638 6
  · have he : independentCachedBranchMembers8484.erase 1638=independentCachedBranchMembers8024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8024
  · have he : independentCachedBranchMembers8484.filter (independentCachedEdge 1638)=independentCachedBranchMembers8483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8483
def independentCachedBranchMembers8485 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2680,2732,2738,2762,2772,3102,3178,3180,3186,3188,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8485 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8485 6 (fun x => (if x<2732 then (if x<1690 then (if x<1626 then (if x<1596 then (if x<1594 then 0 else 1) else (if x<1614 then 2 else 0)) else (if x<1678 then (if x<1628 then 2 else 1) else (if x<1686 then 1 else 2))) else (if x<1768 then (if x<1762 then (if x<1692 then 0 else 3) else (if x<1764 then 0 else 3)) else (if x<2590 then (if x<1776 then 1 else 2) else (if x<2680 then 0 else 1)))) else (if x<3188 then (if x<3102 then (if x<2762 then (if x<2738 then 3 else 0) else (if x<2772 then 0 else 3)) else (if x<3180 then (if x<3178 then 2 else 4) else (if x<3186 then 5 else 5))) else (if x<3256 then (if x<3242 then (if x<3238 then 4 else 4) else (if x<3252 then 5 else 2)) else (if x<3276 then (if x<3270 then 4 else 5) else (if x<3282 then 3 else (if x<3288 then 2 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8486 : Finset ℕ := ([1590,1614,1626,1628,1686,1768,2680,2738,2762,3178,3180,3238,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8486 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8486 5 (fun x => (if x<2738 then (if x<1628 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<1768 then (if x<1686 then 2 else 1) else (if x<2680 then 2 else 1))) else (if x<3238 then (if x<3178 then (if x<2762 then 0 else 0) else (if x<3180 then 1 else 2)) else (if x<3276 then (if x<3252 then 1 else 0) else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8487 : Finset ℕ := ([1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2680,2732,2738,2762,2772,3102,3178,3180,3186,3188,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8487 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8487 1622 5
  · have he : independentCachedBranchMembers8487.erase 1622=independentCachedBranchMembers8485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8485
  · have he : independentCachedBranchMembers8487.filter (independentCachedEdge 1622)=independentCachedBranchMembers8486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8486
def independentCachedBranchMembers8488 : Finset ℕ := ([1590,1594,1596,1614,1678,1776,2680,2738,2762,3186,3188,3252,3256,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8488 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8488 5 (fun x => (if x<2738 then (if x<1614 then (if x<1594 then 0 else (if x<1596 then 1 else 2)) else (if x<1776 then (if x<1678 then 0 else 1) else (if x<2680 then 2 else 1))) else (if x<3252 then (if x<3186 then (if x<2762 then 0 else 0) else (if x<3188 then 1 else 2)) else (if x<3270 then (if x<3256 then 0 else 2) else (if x<3276 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8489 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2680,2732,2738,2762,2772,3102,3178,3180,3186,3188,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8489 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8489 1582 5
  · have he : independentCachedBranchMembers8489.erase 1582=independentCachedBranchMembers8487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8487
  · have he : independentCachedBranchMembers8489.filter (independentCachedEdge 1582)=independentCachedBranchMembers8488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8488
def independentCachedBranchMembers8490 : Finset ℕ := ([1594,1596,1614,1622,1678,1686,1762,1764,2680,2762,2772,3102,3178,3180,3186,3188,3242,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8490 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8490 5 (fun x => (if x<2772 then (if x<1686 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1622 then 0 else (if x<1678 then 1 else 1))) else (if x<1764 then (if x<1762 then 0 else 0) else (if x<2680 then 1 else (if x<2762 then 2 else 2)))) else (if x<3188 then (if x<3178 then (if x<3102 then 2 else 0) else (if x<3180 then 0 else (if x<3186 then 3 else 3))) else (if x<3252 then (if x<3242 then 1 else 3) else (if x<3270 then 3 else (if x<3288 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8491 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2680,2732,2738,2762,2772,2776,3102,3178,3180,3186,3188,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8491 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8491 2776 5
  · have he : independentCachedBranchMembers8491.erase 2776=independentCachedBranchMembers8489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8489
  · have he : independentCachedBranchMembers8491.filter (independentCachedEdge 2776)=independentCachedBranchMembers8490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8490
def independentCachedBranchMembers8492 : Finset ℕ := ([1582,1590,1626,1628,1690,1692,1768,1776,2680,2762,2772,3102,3178,3180,3186,3188,3242,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8492 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8492 5 (fun x => (if x<2772 then (if x<1692 then (if x<1626 then (if x<1590 then 0 else 1) else (if x<1628 then 0 else (if x<1690 then 1 else 1))) else (if x<1776 then (if x<1768 then 0 else 0) else (if x<2680 then 1 else (if x<2762 then 2 else 2)))) else (if x<3188 then (if x<3178 then (if x<3102 then 2 else 0) else (if x<3180 then 0 else (if x<3186 then 3 else 3))) else (if x<3252 then (if x<3242 then 1 else 3) else (if x<3270 then 3 else (if x<3288 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8493 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2680,2732,2738,2758,2762,2772,2776,3102,3178,3180,3186,3188,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8493 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8493 2758 5
  · have he : independentCachedBranchMembers8493.erase 2758=independentCachedBranchMembers8491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8491
  · have he : independentCachedBranchMembers8493.filter (independentCachedEdge 2758)=independentCachedBranchMembers8492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8492
def independentCachedBranchMembers8494 : Finset ℕ := ([1582,1596,1614,1628,1686,1690,1764,1768,2680,2732,2738,3102,3180,3186,3238,3242,3252,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8494 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8494 5 (fun x => (if x<2738 then (if x<1690 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1628 then 1 else (if x<1686 then 0 else 0))) else (if x<1768 then (if x<1764 then 1 else 0) else (if x<2680 then 1 else (if x<2732 then 2 else 2)))) else (if x<3242 then (if x<3180 then (if x<3102 then 2 else 0) else (if x<3186 then 0 else (if x<3238 then 2 else 0))) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3270 then 1 else (if x<3288 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8495 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2674,2680,2732,2738,2758,2762,2772,2776,3102,3178,3180,3186,3188,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8495 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8495 2674 5
  · have he : independentCachedBranchMembers8495.erase 2674=independentCachedBranchMembers8493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8493
  · have he : independentCachedBranchMembers8495.filter (independentCachedEdge 2674)=independentCachedBranchMembers8494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8494
def independentCachedBranchMembers8496 : Finset ℕ := ([1590,1594,1622,1626,1678,1692,1762,1776,2680,2732,2738,3102,3180,3186,3238,3242,3252,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8496 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8496 5 (fun x => (if x<2738 then (if x<1692 then (if x<1622 then (if x<1594 then 0 else 1) else (if x<1626 then 1 else (if x<1678 then 0 else 0))) else (if x<1776 then (if x<1762 then 1 else 0) else (if x<2680 then 1 else (if x<2732 then 2 else 2)))) else (if x<3242 then (if x<3180 then (if x<3102 then 2 else 0) else (if x<3186 then 2 else (if x<3238 then 0 else 0))) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3270 then 1 else (if x<3288 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8497 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2668,2674,2680,2732,2738,2758,2762,2772,2776,3102,3178,3180,3186,3188,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8497 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8497 2668 5
  · have he : independentCachedBranchMembers8497.erase 2668=independentCachedBranchMembers8495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8495
  · have he : independentCachedBranchMembers8497.filter (independentCachedEdge 2668)=independentCachedBranchMembers8496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8496
def independentCachedBranchMembers8498 : Finset ℕ := ([1582,1590,1614,1622,1690,1692,1762,1764,2590,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8498 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8498 5 (fun x => (if x<2738 then (if x<1692 then (if x<1614 then (if x<1590 then 0 else 1) else (if x<1622 then 1 else (if x<1690 then 0 else 0))) else (if x<2590 then (if x<1762 then 1 else (if x<1764 then 0 else 1)) else (if x<2680 then 0 else (if x<2732 then 2 else 2)))) else (if x<3186 then (if x<2772 then (if x<2762 then 2 else 2) else (if x<3178 then 2 else (if x<3180 then 3 else 4))) else (if x<3256 then (if x<3188 then 4 else (if x<3238 then 3 else 3)) else (if x<3270 then 3 else (if x<3288 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8499 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2668,2674,2680,2732,2738,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8499 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8499 3192 5
  · have he : independentCachedBranchMembers8499.erase 3192=independentCachedBranchMembers8497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8497
  · have he : independentCachedBranchMembers8499.filter (independentCachedEdge 3192)=independentCachedBranchMembers8498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8498
def independentCachedBranchMembers8500 : Finset ℕ := ([1582,1590,1626,1628,1678,1686,1762,1764,2680,2732,2738,2758,2776,3102,3178,3180,3186,3188,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8500 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8500 5 (fun x => (if x<2758 then (if x<1686 then (if x<1626 then (if x<1590 then 0 else 1) else (if x<1628 then 0 else (if x<1678 then 1 else 1))) else (if x<2680 then (if x<1762 then 0 else (if x<1764 then 0 else 1)) else (if x<2732 then 2 else (if x<2738 then 2 else 2)))) else (if x<3186 then (if x<3102 then (if x<2776 then 3 else 3) else (if x<3178 then 0 else (if x<3180 then 0 else 2))) else (if x<3256 then (if x<3188 then 2 else (if x<3238 then 1 else 0)) else (if x<3276 then 2 else (if x<3282 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8501 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2668,2674,2680,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8501 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8501 2744 5
  · have he : independentCachedBranchMembers8501.erase 2744=independentCachedBranchMembers8499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8499
  · have he : independentCachedBranchMembers8501.filter (independentCachedEdge 2744)=independentCachedBranchMembers8500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8500
def independentCachedBranchMembers8502 : Finset ℕ := ([1594,1596,1614,1622,1690,1692,1768,1776,2680,2732,2738,2758,2776,3102,3178,3180,3186,3188,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8502 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8502 5 (fun x => (if x<2758 then (if x<1692 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1622 then 0 else (if x<1690 then 1 else 1))) else (if x<2680 then (if x<1768 then 0 else (if x<1776 then 0 else 1)) else (if x<2732 then 2 else (if x<2738 then 2 else 2)))) else (if x<3186 then (if x<3102 then (if x<2776 then 3 else 3) else (if x<3178 then 0 else (if x<3180 then 0 else 2))) else (if x<3256 then (if x<3188 then 2 else (if x<3238 then 1 else 2)) else (if x<3276 then 0 else (if x<3282 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8503 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2668,2674,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8503 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8503 2726 5
  · have he : independentCachedBranchMembers8503.erase 2726=independentCachedBranchMembers8501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8501
  · have he : independentCachedBranchMembers8503.filter (independentCachedEdge 2726)=independentCachedBranchMembers8502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8502
def independentCachedBranchMembers8504 : Finset ℕ := ([1582,1594,1614,1626,1686,1692,1762,1768,2668,2674,2680,2762,2772,3102,3178,3188,3238,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8504 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8504 5 (fun x => (if x<2762 then (if x<1692 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1626 then 1 else (if x<1686 then 0 else 0))) else (if x<2668 then (if x<1762 then 1 else (if x<1768 then 0 else 1)) else (if x<2674 then 2 else (if x<2680 then 2 else 3)))) else (if x<3238 then (if x<3102 then (if x<2772 then 2 else 2) else (if x<3178 then 0 else (if x<3188 then 0 else 2))) else (if x<3276 then (if x<3256 then 0 else (if x<3270 then 1 else 3)) else (if x<3282 then 1 else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8505 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8505 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8505 2676 5
  · have he : independentCachedBranchMembers8505.erase 2676=independentCachedBranchMembers8503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8503
  · have he : independentCachedBranchMembers8505.filter (independentCachedEdge 2676)=independentCachedBranchMembers8504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8504
def independentCachedBranchMembers8506 : Finset ℕ := ([1590,1596,1622,1628,1678,1690,1764,1776,2668,2674,2680,2762,2772,3102,3178,3188,3238,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8506 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8506 5 (fun x => (if x<2762 then (if x<1690 then (if x<1622 then (if x<1596 then 0 else 1) else (if x<1628 then 1 else (if x<1678 then 0 else 0))) else (if x<2668 then (if x<1764 then 1 else (if x<1776 then 0 else 1)) else (if x<2674 then 2 else (if x<2680 then 2 else 3)))) else (if x<3238 then (if x<3102 then (if x<2772 then 2 else 2) else (if x<3178 then 0 else (if x<3188 then 2 else 0))) else (if x<3276 then (if x<3256 then 0 else (if x<3270 then 1 else 3)) else (if x<3282 then 0 else (if x<3288 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8507 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8507 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8507 2666 5
  · have he : independentCachedBranchMembers8507.erase 2666=independentCachedBranchMembers8505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8505
  · have he : independentCachedBranchMembers8507.filter (independentCachedEdge 2666)=independentCachedBranchMembers8506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8506
def independentCachedBranchMembers8508 : Finset ℕ := ([1590,1594,1614,1622,1626,1678,1686,1762,2590,2666,2674,2726,2738,2758,2762,3102,3178,3186,3238,3242,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8508 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8508 5 (fun x => (if x<2726 then (if x<1678 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1622 then 0 else (if x<1626 then 1 else 2))) else (if x<2590 then (if x<1686 then 1 else (if x<1762 then 2 else 0)) else (if x<2666 then 0 else (if x<2674 then 2 else 1)))) else (if x<3178 then (if x<2758 then (if x<2738 then 2 else 0) else (if x<2762 then 1 else (if x<3102 then 0 else 3))) else (if x<3242 then (if x<3186 then 3 else (if x<3238 then 4 else 3)) else (if x<3270 then 4 else (if x<3282 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8509 : Finset ℕ := ([1590,1594,1614,1678,2674,2738,2758,2762,3186,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8509 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8509 4 (fun x => (if x<2738 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1678 then 0 else (if x<2674 then 1 else 1))) else (if x<2762 then (if x<2758 then 0 else 1) else (if x<3186 then 0 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8510 : Finset ℕ := ([1582,1590,1594,1614,1622,1626,1678,1686,1762,2590,2666,2674,2726,2738,2758,2762,3102,3178,3186,3238,3242,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8510 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8510 1582 4
  · have he : independentCachedBranchMembers8510.erase 1582=independentCachedBranchMembers8508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8508
  · have he : independentCachedBranchMembers8510.filter (independentCachedEdge 1582)=independentCachedBranchMembers8509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8509
def independentCachedBranchMembers8511 : Finset ℕ := ([1594,1626,1678,1686,2666,2674,2726,2758,3178,3186,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8511 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8511 4 (fun x => (if x<2726 then (if x<1686 then (if x<1626 then 0 else (if x<1678 then 1 else 0)) else (if x<2666 then 1 else (if x<2674 then 1 else 0))) else (if x<3186 then (if x<2758 then 1 else (if x<3178 then 0 else 2)) else (if x<3238 then 3 else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
