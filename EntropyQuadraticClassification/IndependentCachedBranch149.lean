/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch148
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7552 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7552 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7552 3276 4
  · have he : independentCachedBranchMembers7552.erase 3276=independentCachedBranchMembers7550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7550
  · have he : independentCachedBranchMembers7552.filter (independentCachedEdge 3276)=independentCachedBranchMembers7551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7551
def independentCachedBranchMembers7553 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1768,2614,2652,2710,2786,3132,3158,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7553 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7553 4 (fun x => (if x<2614 then (if x<1596 then (if x<136 then (if x<66 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1692 then (if x<1622 then 0 else 0) else (if x<1768 then 1 else 1))) else (if x<3132 then (if x<2710 then (if x<2652 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3158 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7554 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2738,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7554 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7554 2738 4
  · have he : independentCachedBranchMembers7554.erase 2738=independentCachedBranchMembers7552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7552
  · have he : independentCachedBranchMembers7554.filter (independentCachedEdge 2738)=independentCachedBranchMembers7553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7553
def independentCachedBranchMembers7555 : Finset ℕ := ([40,252,1622,1692,1740,1746,2652,2710,2758,2776,3132,3180,3186,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7555 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7555 4 (fun x => (if x<2758 then (if x<1740 then (if x<1622 then (if x<252 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1746 then 2 else 2) else (if x<2710 then 1 else 1))) else (if x<3186 then (if x<3132 then (if x<2776 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7556 : Finset ℕ := ([40,66,136,252,1596,1622,1650,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2738,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7556 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7556 1650 4
  · have he : independentCachedBranchMembers7556.erase 1650=independentCachedBranchMembers7554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7554
  · have he : independentCachedBranchMembers7556.filter (independentCachedEdge 1650)=independentCachedBranchMembers7555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7555
def independentCachedBranchMembers7557 : Finset ℕ := ([66,136,1596,1740,1746,1768,2614,2758,2776,2786,3158,3180,3186,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7557 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7557 4 (fun x => (if x<2776 then (if x<1746 then (if x<1596 then (if x<136 then 0 else 0) else (if x<1740 then 1 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2758 then 1 else 1))) else (if x<3186 then (if x<3158 then (if x<2786 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3238 then (if x<3228 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7558 : Finset ℕ := ([40,66,136,252,1596,1622,1644,1650,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2738,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7558 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7558 1644 4
  · have he : independentCachedBranchMembers7558.erase 1644=independentCachedBranchMembers7556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7556
  · have he : independentCachedBranchMembers7558.filter (independentCachedEdge 1644)=independentCachedBranchMembers7557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7557
def independentCachedBranchMembers7559 : Finset ℕ := ([66,252,1596,1692,1702,1720,2652,2662,2680,2758,2776,2786,3132,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7559 4 (fun x => (if x<2680 then (if x<1702 then (if x<1596 then (if x<252 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<2652 then (if x<1720 then 2 else 2) else (if x<2662 then 1 else 2))) else (if x<3132 then (if x<2776 then (if x<2758 then 2 else 0) else (if x<2786 then 3 else 3)) else (if x<3238 then (if x<3228 then 1 else 3) else (if x<3256 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7560 : Finset ℕ := ([18,40,66,136,252,1596,1622,1644,1650,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2738,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7560 18 4
  · have he : independentCachedBranchMembers7560.erase 18=independentCachedBranchMembers7558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7558
  · have he : independentCachedBranchMembers7560.filter (independentCachedEdge 18)=independentCachedBranchMembers7559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7559
def independentCachedBranchMembers7561 : Finset ℕ := ([40,136,1622,1702,1720,1768,2614,2662,2680,2710,2758,2776,3158,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7561 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7561 4 (fun x => (if x<2680 then (if x<1720 then (if x<1622 then (if x<136 then 0 else 1) else (if x<1702 then 0 else 2)) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2662 then 2 else 1))) else (if x<3158 then (if x<2758 then (if x<2710 then 2 else 0) else (if x<2776 then 3 else 3)) else (if x<3256 then (if x<3238 then 1 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7562 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2738,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7562 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7562 12 4
  · have he : independentCachedBranchMembers7562.erase 12=independentCachedBranchMembers7560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7560
  · have he : independentCachedBranchMembers7562.filter (independentCachedEdge 12)=independentCachedBranchMembers7561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7561
def independentCachedBranchMembers7563 : Finset ℕ := ([12,18,34,40,66,72,130,136,246,252,1590,1596,1622,1628,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2726,2732,2738,2744,2758,2764,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7563 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7563 2726 5
  · have he : independentCachedBranchMembers7563.erase 2726=independentCachedBranchMembers7543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7543
  · have he : independentCachedBranchMembers7563.filter (independentCachedEdge 2726)=independentCachedBranchMembers7562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7562
def independentCachedBranchMembers7564 : Finset ℕ := ([10,12,18,20,34,36,40,48,66,68,72,80,130,132,136,144,160,190,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7564 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7564 10 6
  · have he : independentCachedBranchMembers7564.erase 10=independentCachedBranchMembers7314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7314
  · have he : independentCachedBranchMembers7564.filter (independentCachedEdge 10)=independentCachedBranchMembers7563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7563
def independentCachedBranchMembers7565 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2662,2680,2732,2738,2762,2772,3118,3126,3150,3158,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7565 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7565 6 (fun x => (if x<2732 then (if x<1702 then (if x<1650 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<1678 then (if x<1652 then 2 else 1) else (if x<1686 then 0 else 3))) else (if x<1768 then (if x<1734 then (if x<1720 then 1 else 1) else (if x<1752 then 2 else 2)) else (if x<2662 then (if x<1776 then 0 else 3) else (if x<2680 then 1 else 0)))) else (if x<3192 then (if x<3118 then (if x<2762 then (if x<2738 then 0 else 3) else (if x<2772 then 0 else 3)) else (if x<3150 then (if x<3126 then 4 else 5) else (if x<3158 then 5 else 4))) else (if x<3252 then (if x<3228 then (if x<3226 then 2 else 4) else (if x<3242 then 5 else 5)) else (if x<3282 then (if x<3276 then 3 else 2) else (if x<3298 then 2 else (if x<3300 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7566 : Finset ℕ := ([1596,1626,1644,1652,1702,1752,2662,2732,2762,3118,3126,3226,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7566 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7566 5 (fun x => (if x<2732 then (if x<1652 then (if x<1626 then 0 else (if x<1644 then 0 else 1)) else (if x<1752 then (if x<1702 then 2 else 1) else (if x<2662 then 2 else 1))) else (if x<3226 then (if x<3118 then (if x<2762 then 0 else 0) else (if x<3126 then 1 else 2)) else (if x<3282 then (if x<3252 then 2 else 0) else (if x<3300 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7567 : Finset ℕ := ([1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2662,2680,2732,2738,2762,2772,3118,3126,3150,3158,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7567 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7567 1628 5
  · have he : independentCachedBranchMembers7567.erase 1628=independentCachedBranchMembers7565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7565
  · have he : independentCachedBranchMembers7567.filter (independentCachedEdge 1628)=independentCachedBranchMembers7566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7566
def independentCachedBranchMembers7568 : Finset ℕ := ([1596,1626,1642,1650,1720,1734,2662,2732,2762,3150,3158,3228,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7568 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7568 5 (fun x => (if x<2732 then (if x<1650 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1734 then (if x<1720 then 2 else 1) else (if x<2662 then 2 else 1))) else (if x<3228 then (if x<3150 then (if x<2762 then 0 else 0) else (if x<3158 then 1 else 2)) else (if x<3282 then (if x<3252 then 1 else 0) else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7569 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2662,2680,2732,2738,2762,2772,3118,3126,3150,3158,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7569 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7569 1594 5
  · have he : independentCachedBranchMembers7569.erase 1594=independentCachedBranchMembers7567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7567
  · have he : independentCachedBranchMembers7569.filter (independentCachedEdge 1594)=independentCachedBranchMembers7568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7568
def independentCachedBranchMembers7570 : Finset ℕ := ([1596,1628,1642,1650,1678,1686,1720,1752,2662,2732,2772,3118,3126,3150,3158,3192,3228,3242,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7570 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7570 5 (fun x => (if x<2772 then (if x<1686 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1650 then 0 else (if x<1678 then 1 else 0))) else (if x<1752 then (if x<1720 then 1 else 1) else (if x<2662 then 0 else (if x<2732 then 2 else 2)))) else (if x<3192 then (if x<3126 then (if x<3118 then 2 else 0) else (if x<3150 then 3 else (if x<3158 then 3 else 1))) else (if x<3242 then (if x<3228 then 0 else 0) else (if x<3282 then 3 else (if x<3300 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7571 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2662,2680,2732,2738,2762,2772,2788,3118,3126,3150,3158,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7571 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7571 2788 5
  · have he : independentCachedBranchMembers7571.erase 2788=independentCachedBranchMembers7569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7569
  · have he : independentCachedBranchMembers7571.filter (independentCachedEdge 2788)=independentCachedBranchMembers7570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7570
def independentCachedBranchMembers7572 : Finset ℕ := ([1594,1626,1644,1652,1702,1734,1768,1776,2662,2732,2772,3118,3126,3150,3158,3192,3228,3242,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7572 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7572 5 (fun x => (if x<2772 then (if x<1734 then (if x<1644 then (if x<1626 then 0 else 1) else (if x<1652 then 0 else (if x<1702 then 1 else 0))) else (if x<1776 then (if x<1768 then 1 else 1) else (if x<2662 then 0 else (if x<2732 then 2 else 2)))) else (if x<3192 then (if x<3126 then (if x<3118 then 2 else 0) else (if x<3150 then 3 else (if x<3158 then 3 else 1))) else (if x<3242 then (if x<3228 then 0 else 2) else (if x<3282 then 3 else (if x<3300 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7573 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2662,2680,2716,2732,2738,2762,2772,2788,3118,3126,3150,3158,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7573 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7573 2716 5
  · have he : independentCachedBranchMembers7573.erase 2716=independentCachedBranchMembers7571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7571
  · have he : independentCachedBranchMembers7573.filter (independentCachedEdge 2716)=independentCachedBranchMembers7572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7572
def independentCachedBranchMembers7574 : Finset ℕ := ([1594,1596,1650,1652,1686,1702,1752,1768,2662,2738,2762,3126,3150,3192,3226,3228,3242,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7574 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7574 5 (fun x => (if x<2762 then (if x<1702 then (if x<1650 then (if x<1596 then 0 else 1) else (if x<1652 then 1 else (if x<1686 then 0 else 0))) else (if x<1768 then (if x<1752 then 1 else 0) else (if x<2662 then 1 else (if x<2738 then 2 else 2)))) else (if x<3228 then (if x<3150 then (if x<3126 then 2 else 0) else (if x<3192 then 2 else (if x<3226 then 0 else 0))) else (if x<3282 then (if x<3242 then 3 else 3) else (if x<3298 then 3 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7575 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2638,2662,2680,2716,2732,2738,2762,2772,2788,3118,3126,3150,3158,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7575 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7575 2638 5
  · have he : independentCachedBranchMembers7575.erase 2638=independentCachedBranchMembers7573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7573
  · have he : independentCachedBranchMembers7575.filter (independentCachedEdge 2638)=independentCachedBranchMembers7574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7574
def independentCachedBranchMembers7576 : Finset ℕ := ([1626,1628,1642,1644,1678,1720,1734,1776,2662,2738,2762,3126,3150,3192,3226,3228,3242,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7576 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7576 5 (fun x => (if x<2762 then (if x<1720 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1644 then 1 else (if x<1678 then 0 else 0))) else (if x<1776 then (if x<1734 then 0 else 1) else (if x<2662 then 1 else (if x<2738 then 2 else 2)))) else (if x<3228 then (if x<3150 then (if x<3126 then 2 else 2) else (if x<3192 then 0 else (if x<3226 then 0 else 0))) else (if x<3282 then (if x<3242 then 3 else 3) else (if x<3298 then 3 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7577 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2614,2638,2662,2680,2716,2732,2738,2762,2772,2788,3118,3126,3150,3158,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7577 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7577 2614 5
  · have he : independentCachedBranchMembers7577.erase 2614=independentCachedBranchMembers7575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7575
  · have he : independentCachedBranchMembers7577.filter (independentCachedEdge 2614)=independentCachedBranchMembers7576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7576
def independentCachedBranchMembers7578 : Finset ℕ := ([1594,1596,1626,1628,1678,1686,1768,1776,2662,2680,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7578 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7578 5 (fun x => (if x<2738 then (if x<1686 then (if x<1626 then (if x<1596 then 0 else 1) else (if x<1628 then 1 else (if x<1678 then 0 else 0))) else (if x<2662 then (if x<1768 then 1 else (if x<1776 then 0 else 1)) else (if x<2680 then 2 else (if x<2732 then 0 else 2)))) else (if x<3150 then (if x<2772 then (if x<2762 then 2 else 2) else (if x<3118 then 2 else (if x<3126 then 3 else 4))) else (if x<3228 then (if x<3158 then 4 else (if x<3226 then 3 else 3)) else (if x<3298 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7579 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2614,2638,2662,2680,2716,2732,2738,2762,2772,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7579 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7579 3174 5
  · have he : independentCachedBranchMembers7579.erase 3174=independentCachedBranchMembers7577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7577
  · have he : independentCachedBranchMembers7579.filter (independentCachedEdge 3174)=independentCachedBranchMembers7578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7578
def independentCachedBranchMembers7580 : Finset ℕ := ([1594,1626,1644,1652,1678,1686,1720,1752,2662,2716,2738,2762,2788,3118,3126,3150,3158,3192,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7580 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7580 5 (fun x => (if x<2762 then (if x<1686 then (if x<1644 then (if x<1626 then 0 else 1) else (if x<1652 then 0 else (if x<1678 then 1 else 0))) else (if x<2662 then (if x<1720 then 1 else (if x<1752 then 1 else 0)) else (if x<2716 then 2 else (if x<2738 then 3 else 2)))) else (if x<3158 then (if x<3118 then (if x<2788 then 2 else 3) else (if x<3126 then 0 else (if x<3150 then 2 else 2))) else (if x<3252 then (if x<3192 then 1 else (if x<3226 then 0 else 0)) else (if x<3276 then 1 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7581 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2614,2638,2662,2680,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7581 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7581 2786 5
  · have he : independentCachedBranchMembers7581.erase 2786=independentCachedBranchMembers7579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7579
  · have he : independentCachedBranchMembers7581.filter (independentCachedEdge 2786)=independentCachedBranchMembers7580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7580
def independentCachedBranchMembers7582 : Finset ℕ := ([1596,1628,1642,1650,1702,1734,1768,1776,2662,2716,2738,2762,2788,3118,3126,3150,3158,3192,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7582 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7582 5 (fun x => (if x<2762 then (if x<1734 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1650 then 0 else (if x<1702 then 1 else 0))) else (if x<2662 then (if x<1768 then 1 else (if x<1776 then 1 else 0)) else (if x<2716 then 2 else (if x<2738 then 3 else 2)))) else (if x<3158 then (if x<3118 then (if x<2788 then 2 else 3) else (if x<3126 then 0 else (if x<3150 then 2 else 2))) else (if x<3252 then (if x<3192 then 1 else (if x<3226 then 0 else 2)) else (if x<3276 then 0 else (if x<3298 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7583 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2614,2638,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7583 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7583 2714 5
  · have he : independentCachedBranchMembers7583.erase 2714=independentCachedBranchMembers7581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7581
  · have he : independentCachedBranchMembers7583.filter (independentCachedEdge 2714)=independentCachedBranchMembers7582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7582
end EntropyDesigns.QuadraticRefinement
