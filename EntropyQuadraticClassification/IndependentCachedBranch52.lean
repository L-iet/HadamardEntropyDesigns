/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch51
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4448 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4448 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4448 34 6
  · have he : independentCachedBranchMembers4448.erase 34=independentCachedBranchMembers4254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4254
  · have he : independentCachedBranchMembers4448.filter (independentCachedEdge 34)=independentCachedBranchMembers4447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4447
def independentCachedBranchMembers4449 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,2620,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4449 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4449 6 (fun x => (if x<2758 then (if x<2662 then (if x<1738 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else 0)) else (if x<2620 then (if x<1748 then 0 else 0) else (if x<2646 then 1 else 1))) else (if x<2730 then (if x<2714 then (if x<2680 then 2 else 2) else (if x<2716 then 1 else 3)) else (if x<2738 then (if x<2732 then 2 else 4) else (if x<2740 then 3 else 2)))) else (if x<3178 then (if x<3118 then (if x<2792 then (if x<2776 then 3 else 4) else (if x<2800 then 3 else 1)) else (if x<3162 then (if x<3126 then 4 else 5) else (if x<3164 then 4 else 5))) else (if x<3256 then (if x<3214 then (if x<3188 then 2 else 1) else (if x<3222 then 5 else 3)) else (if x<3282 then (if x<3276 then 1 else 3) else (if x<3298 then 1 else (if x<3300 then 3 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4450 : Finset ℕ := ([1650,1702,1748,2646,2662,2738,2740,2758,2800,3126,3188,3222,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4450 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4450 5 (fun x => (if x<2758 then (if x<2646 then (if x<1702 then 0 else (if x<1748 then 0 else 0)) else (if x<2738 then (if x<2662 then 1 else 2) else (if x<2740 then 1 else 2))) else (if x<3222 then (if x<3126 then (if x<2800 then 3 else 3) else (if x<3188 then 1 else 2)) else (if x<3298 then (if x<3282 then 4 else 1) else (if x<3300 then 3 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4451 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4451 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4451 2638 5
  · have he : independentCachedBranchMembers4451.erase 2638=independentCachedBranchMembers4449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4449
  · have he : independentCachedBranchMembers4451.filter (independentCachedEdge 2638)=independentCachedBranchMembers4450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4450
def independentCachedBranchMembers4452 : Finset ℕ := ([1644,1702,1738,2620,2680,2714,2730,2738,2758,3164,3188,3214,3222,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4452 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4452 5 (fun x => (if x<2738 then (if x<2620 then (if x<1702 then 0 else (if x<1738 then 0 else 0)) else (if x<2714 then (if x<2680 then 1 else 2) else (if x<2730 then 1 else 2))) else (if x<3214 then (if x<3164 then (if x<2758 then 3 else 3) else (if x<3188 then 2 else 1)) else (if x<3282 then (if x<3222 then 2 else 3) else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4453 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4453 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4453 2618 5
  · have he : independentCachedBranchMembers4453.erase 2618=independentCachedBranchMembers4451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4451
  · have he : independentCachedBranchMembers4453.filter (independentCachedEdge 2618)=independentCachedBranchMembers4452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4452
def independentCachedBranchMembers4454 : Finset ℕ := ([1644,1702,1748,2620,2638,2646,2680,2716,2730,2738,2776,3118,3126,3164,3178,3214,3222,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4454 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4454 5 (fun x => (if x<2776 then (if x<2646 then (if x<1748 then (if x<1702 then 0 else 0) else (if x<2620 then 0 else (if x<2638 then 1 else 1))) else (if x<2716 then (if x<2680 then 2 else 2) else (if x<2730 then 2 else (if x<2738 then 1 else 2)))) else (if x<3214 then (if x<3126 then (if x<3118 then 1 else 0) else (if x<3164 then 3 else (if x<3178 then 0 else 3))) else (if x<3256 then (if x<3222 then 3 else 0) else (if x<3282 then 1 else (if x<3300 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4455 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4455 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4455 1764 5
  · have he : independentCachedBranchMembers4455.erase 1764=independentCachedBranchMembers4453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4453
  · have he : independentCachedBranchMembers4455.filter (independentCachedEdge 1764)=independentCachedBranchMembers4454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4454
def independentCachedBranchMembers4456 : Finset ℕ := ([1650,1702,1738,2618,2620,2646,2662,2738,2740,2776,2792,3126,3162,3164,3178,3214,3256,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4456 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4456 5 (fun x => (if x<2792 then (if x<2646 then (if x<1738 then (if x<1702 then 0 else 0) else (if x<2618 then 0 else (if x<2620 then 1 else 2))) else (if x<2738 then (if x<2662 then 1 else 2) else (if x<2740 then 2 else (if x<2776 then 1 else 1)))) else (if x<3214 then (if x<3162 then (if x<3126 then 2 else 0) else (if x<3164 then 0 else (if x<3178 then 3 else 3))) else (if x<3282 then (if x<3256 then 0 else 1) else (if x<3298 then 3 else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4457 : Finset ℕ := ([1644,1650,1678,1702,1720,1738,1748,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4457 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4457 1678 5
  · have he : independentCachedBranchMembers4457.erase 1678=independentCachedBranchMembers4455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4455
  · have he : independentCachedBranchMembers4457.filter (independentCachedEdge 1678)=independentCachedBranchMembers4456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4456
def independentCachedBranchMembers4458 : Finset ℕ := ([1644,1702,1748,2618,2662,2714,2732,2740,2758,2792,2800,3118,3126,3164,3178,3214,3222,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4458 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4458 5 (fun x => (if x<2800 then (if x<2714 then (if x<1748 then (if x<1702 then 0 else 0) else (if x<2618 then 0 else (if x<2662 then 1 else 1))) else (if x<2740 then (if x<2732 then 2 else 1) else (if x<2758 then 2 else (if x<2792 then 2 else 2)))) else (if x<3214 then (if x<3126 then (if x<3118 then 1 else 0) else (if x<3164 then 3 else (if x<3178 then 0 else 3))) else (if x<3256 then (if x<3222 then 3 else 0) else (if x<3282 then 1 else (if x<3300 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4459 : Finset ℕ := ([1628,1644,1650,1678,1702,1720,1738,1748,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4459 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4459 1628 5
  · have he : independentCachedBranchMembers4459.erase 1628=independentCachedBranchMembers4457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4457
  · have he : independentCachedBranchMembers4459.filter (independentCachedEdge 1628)=independentCachedBranchMembers4458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4458
def independentCachedBranchMembers4460 : Finset ℕ := ([1650,1702,1738,2638,2680,2714,2716,2730,2732,2758,2800,3126,3162,3164,3178,3214,3256,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4460 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4460 5 (fun x => (if x<2800 then (if x<2714 then (if x<1738 then (if x<1702 then 0 else 0) else (if x<2638 then 0 else (if x<2680 then 1 else 1))) else (if x<2730 then (if x<2716 then 1 else 2) else (if x<2732 then 2 else (if x<2758 then 1 else 2)))) else (if x<3214 then (if x<3162 then (if x<3126 then 2 else 0) else (if x<3164 then 0 else (if x<3178 then 3 else 3))) else (if x<3282 then (if x<3256 then 0 else 1) else (if x<3298 then 3 else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4461 : Finset ℕ := ([1590,1628,1644,1650,1678,1702,1720,1738,1748,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4461 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4461 1590 5
  · have he : independentCachedBranchMembers4461.erase 1590=independentCachedBranchMembers4459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4459
  · have he : independentCachedBranchMembers4461.filter (independentCachedEdge 1590)=independentCachedBranchMembers4460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4460
def independentCachedBranchMembers4462 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,2618,2620,2638,2646,2714,2716,2792,2800,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4462 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4462 5 (fun x => (if x<2716 then (if x<1748 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else (if x<1738 then 0 else 0))) else (if x<2638 then (if x<2618 then 0 else (if x<2620 then 1 else 2)) else (if x<2646 then 1 else (if x<2714 then 2 else 2)))) else (if x<3162 then (if x<2800 then (if x<2792 then 1 else 1) else (if x<3118 then 2 else (if x<3126 then 3 else 4))) else (if x<3222 then (if x<3164 then 3 else (if x<3214 then 4 else 4)) else (if x<3298 then 3 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4463 : Finset ℕ := ([1590,1628,1644,1650,1678,1702,1720,1738,1748,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4463 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4463 3238 5
  · have he : independentCachedBranchMembers4463.erase 3238=independentCachedBranchMembers4461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4461
  · have he : independentCachedBranchMembers4463.filter (independentCachedEdge 3238)=independentCachedBranchMembers4462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4462
def independentCachedBranchMembers4464 : Finset ℕ := ([1628,1650,1702,1738,1764,2618,2638,2646,2680,2714,2732,2740,2776,3118,3126,3162,3188,3214,3222,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4464 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4464 5 (fun x => (if x<2740 then (if x<2618 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1738 then 1 else (if x<1764 then 0 else 0))) else (if x<2680 then (if x<2638 then 2 else (if x<2646 then 2 else 3)) else (if x<2714 then 1 else (if x<2732 then 3 else 1)))) else (if x<3188 then (if x<3118 then (if x<2776 then 3 else 2) else (if x<3126 then 2 else (if x<3162 then 4 else 0))) else (if x<3256 then (if x<3214 then 0 else (if x<3222 then 1 else 3)) else (if x<3276 then 2 else (if x<3298 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4465 : Finset ℕ := ([1590,1628,1644,1650,1678,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4465 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4465 1762 5
  · have he : independentCachedBranchMembers4465.erase 1762=independentCachedBranchMembers4463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4463
  · have he : independentCachedBranchMembers4465.filter (independentCachedEdge 1762)=independentCachedBranchMembers4464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4464
def independentCachedBranchMembers4466 : Finset ℕ := ([1590,1644,1678,1702,1748,2618,2620,2638,2662,2730,2732,2776,2800,3118,3162,3164,3188,3222,3256,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4466 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4466 5 (fun x => (if x<2776 then (if x<2618 then (if x<1678 then (if x<1644 then 0 else 0) else (if x<1702 then 0 else (if x<1748 then 1 else 0))) else (if x<2662 then (if x<2620 then 2 else (if x<2638 then 3 else 2)) else (if x<2730 then 1 else (if x<2732 then 1 else 2)))) else (if x<3188 then (if x<3118 then (if x<2800 then 2 else 3) else (if x<3162 then 0 else (if x<3164 then 2 else 4))) else (if x<3276 then (if x<3222 then 0 else (if x<3256 then 0 else 2)) else (if x<3298 then 0 else (if x<3300 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4467 : Finset ℕ := ([1590,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4467 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4467 1686 5
  · have he : independentCachedBranchMembers4467.erase 1686=independentCachedBranchMembers4465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4465
  · have he : independentCachedBranchMembers4467.filter (independentCachedEdge 1686)=independentCachedBranchMembers4466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4466
def independentCachedBranchMembers4468 : Finset ℕ := ([1628,1650,1702,1738,1764,2620,2662,2716,2730,2738,2758,2792,2800,3118,3126,3162,3188,3214,3222,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4468 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4468 5 (fun x => (if x<2792 then (if x<2620 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1738 then 1 else (if x<1764 then 0 else 0))) else (if x<2730 then (if x<2662 then 2 else (if x<2716 then 1 else 3)) else (if x<2738 then 1 else (if x<2758 then 2 else 3)))) else (if x<3188 then (if x<3118 then (if x<2800 then 2 else 3) else (if x<3126 then 1 else (if x<3162 then 2 else 0))) else (if x<3256 then (if x<3214 then 0 else (if x<3222 then 3 else 4)) else (if x<3276 then 2 else (if x<3298 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4469 : Finset ℕ := ([1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4469 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4469 1626 5
  · have he : independentCachedBranchMembers4469.erase 1626=independentCachedBranchMembers4467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4467
  · have he : independentCachedBranchMembers4469.filter (independentCachedEdge 1626)=independentCachedBranchMembers4468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4468
def independentCachedBranchMembers4470 : Finset ℕ := ([1590,1644,1678,1702,1748,2646,2680,2714,2716,2738,2740,2758,2792,3118,3162,3164,3188,3222,3256,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4470 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4470 5 (fun x => (if x<2758 then (if x<2646 then (if x<1678 then (if x<1644 then 0 else 0) else (if x<1702 then 0 else (if x<1748 then 1 else 0))) else (if x<2716 then (if x<2680 then 2 else (if x<2714 then 1 else 2)) else (if x<2738 then 3 else (if x<2740 then 1 else 2)))) else (if x<3188 then (if x<3118 then (if x<2792 then 3 else 3) else (if x<3162 then 0 else (if x<3164 then 2 else 1))) else (if x<3276 then (if x<3222 then 0 else (if x<3256 then 0 else 2)) else (if x<3298 then 0 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4471 : Finset ℕ := ([1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4471 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4471 1582 5
  · have he : independentCachedBranchMembers4471.erase 1582=independentCachedBranchMembers4469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4469
  · have he : independentCachedBranchMembers4471.filter (independentCachedEdge 1582)=independentCachedBranchMembers4470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4470
def independentCachedBranchMembers4472 : Finset ℕ := ([1582,1626,1628,1644,1678,1720,1738,2618,2620,2638,2680,2714,2716,2730,2732,2776,2792,3118,3162,3164,3178,3214,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4472 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4472 5 (fun x => (if x<2716 then (if x<1738 then (if x<1644 then (if x<1626 then 0 else (if x<1628 then 0 else 1)) else (if x<1678 then 2 else (if x<1720 then 1 else 0))) else (if x<2638 then (if x<2618 then 2 else (if x<2620 then 0 else 2)) else (if x<2680 then 0 else (if x<2714 then 1 else 2)))) else (if x<3162 then (if x<2776 then (if x<2730 then 1 else (if x<2732 then 1 else 0)) else (if x<2792 then 0 else (if x<3118 then 2 else 3))) else (if x<3214 then (if x<3164 then 3 else (if x<3178 then 4 else 4)) else (if x<3256 then 4 else (if x<3276 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4473 : Finset ℕ := ([246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4473 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4473 246 5
  · have he : independentCachedBranchMembers4473.erase 246=independentCachedBranchMembers4471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4471
  · have he : independentCachedBranchMembers4473.filter (independentCachedEdge 246)=independentCachedBranchMembers4472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4472
def independentCachedBranchMembers4474 : Finset ℕ := ([1582,1590,1626,1650,1720,1748,1764,2618,2638,2646,2662,2732,2740,2776,2792,2800,3118,3126,3162,3178,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4474 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4474 5 (fun x => (if x<2732 then (if x<1748 then (if x<1626 then (if x<1590 then 0 else 1) else (if x<1650 then 0 else (if x<1720 then 2 else 0))) else (if x<2638 then (if x<1764 then 1 else (if x<2618 then 2 else 0)) else (if x<2646 then 0 else (if x<2662 then 1 else 2)))) else (if x<3126 then (if x<2792 then (if x<2740 then 0 else (if x<2776 then 1 else 0)) else (if x<2800 then 3 else (if x<3118 then 2 else 4))) else (if x<3256 then (if x<3162 then 3 else (if x<3178 then 4 else 3)) else (if x<3276 then 3 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4475 : Finset ℕ := ([1582,1590,1626,1764,2662,2732,2740,2776,3118,3126,3162,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4475 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4475 4 (fun x => (if x<2740 then (if x<1764 then (if x<1590 then 0 else (if x<1626 then 1 else 0)) else (if x<2662 then 1 else (if x<2732 then 1 else 0))) else (if x<3126 then (if x<2776 then 1 else (if x<3118 then 0 else 2)) else (if x<3162 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4476 : Finset ℕ := ([1582,1590,1626,1650,1720,1748,1764,2618,2638,2646,2662,2716,2732,2740,2776,2792,2800,3118,3126,3162,3178,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4476 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4476 2716 4
  · have he : independentCachedBranchMembers4476.erase 2716=independentCachedBranchMembers4474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4474
  · have he : independentCachedBranchMembers4476.filter (independentCachedEdge 2716)=independentCachedBranchMembers4475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4475
def independentCachedBranchMembers4477 : Finset ℕ := ([130,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4477 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4477 130 5
  · have he : independentCachedBranchMembers4477.erase 130=independentCachedBranchMembers4473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4473
  · have he : independentCachedBranchMembers4477.filter (independentCachedEdge 130)=independentCachedBranchMembers4476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4476
def independentCachedBranchMembers4478 : Finset ℕ := ([1590,1644,1686,1720,1738,1762,1764,2618,2620,2638,2662,2714,2716,2738,2740,2758,2792,3126,3178,3222,3256,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4478 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4478 5 (fun x => (if x<2716 then (if x<1764 then (if x<1720 then (if x<1644 then 0 else (if x<1686 then 0 else 1)) else (if x<1738 then 0 else (if x<1762 then 1 else 0))) else (if x<2638 then (if x<2618 then 1 else (if x<2620 then 2 else 0)) else (if x<2662 then 2 else (if x<2714 then 0 else 1)))) else (if x<3178 then (if x<2758 then (if x<2738 then 2 else (if x<2740 then 0 else 1)) else (if x<2792 then 1 else (if x<3126 then 0 else 3))) else (if x<3276 then (if x<3222 then 2 else (if x<3256 then 4 else 2)) else (if x<3298 then 2 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4479 : Finset ℕ := ([80,130,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4479 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4479 80 5
  · have he : independentCachedBranchMembers4479.erase 80=independentCachedBranchMembers4477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4477
  · have he : independentCachedBranchMembers4479.filter (independentCachedEdge 80)=independentCachedBranchMembers4478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4478
end EntropyDesigns.QuadraticRefinement
