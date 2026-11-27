/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch213
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9632 : Finset ℕ := ([48,72,192,222,1590,1614,1706,1716,1734,1740,1746,1752,2614,2620,2638,2650,2758,2776,3118,3130,3158,3164,3238,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9632 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9632 48 4
  · have he : independentCachedBranchMembers9632.erase 48=independentCachedBranchMembers9630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9630
  · have he : independentCachedBranchMembers9632.filter (independentCachedEdge 48)=independentCachedBranchMembers9631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9631
def independentCachedBranchMembers9633 : Finset ℕ := ([48,192,1614,1716,1746,1752,2614,2620,2650,2758,3118,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9633 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9633 4 (fun x => (if x<2614 then (if x<1716 then (if x<192 then 0 else (if x<1614 then 0 else 1)) else (if x<1746 then 2 else (if x<1752 then 1 else 2))) else (if x<2758 then (if x<2620 then 0 else (if x<2650 then 3 else 1)) else (if x<3118 then 0 else (if x<3256 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9634 : Finset ℕ := ([48,72,192,222,1590,1614,1626,1706,1716,1734,1740,1746,1752,2614,2620,2638,2650,2758,2776,3118,3130,3158,3164,3238,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9634 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9634 1626 4
  · have he : independentCachedBranchMembers9634.erase 1626=independentCachedBranchMembers9632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9632
  · have he : independentCachedBranchMembers9634.filter (independentCachedEdge 1626)=independentCachedBranchMembers9633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9633
def independentCachedBranchMembers9635 : Finset ℕ := ([72,222,1590,1716,1734,1746,2620,2638,2650,2776,3158,3238] : List ℕ).toFinset
theorem independentCachedBranchBound9635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9635 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9635 4 (fun x => (if x<2620 then (if x<1716 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1734 then 2 else (if x<1746 then 1 else 2))) else (if x<2776 then (if x<2638 then 1 else (if x<2650 then 0 else 2)) else (if x<3158 then 0 else (if x<3238 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9636 : Finset ℕ := ([48,72,192,222,1590,1596,1614,1626,1706,1716,1734,1740,1746,1752,2614,2620,2638,2650,2758,2776,3118,3130,3158,3164,3238,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9636 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9636 1596 4
  · have he : independentCachedBranchMembers9636.erase 1596=independentCachedBranchMembers9634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9634
  · have he : independentCachedBranchMembers9636.filter (independentCachedEdge 1596)=independentCachedBranchMembers9635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9635
def independentCachedBranchMembers9637 : Finset ℕ := ([72,192,1590,1706,1740,1752,2614,2776,3118,3130,3164,3238] : List ℕ).toFinset
theorem independentCachedBranchBound9637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9637 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9637 4 (fun x => (if x<2614 then (if x<1706 then (if x<192 then 0 else (if x<1590 then 1 else 0)) else (if x<1740 then 2 else (if x<1752 then 1 else 2))) else (if x<3130 then (if x<2776 then 1 else (if x<3118 then 0 else 2)) else (if x<3164 then 1 else (if x<3238 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9638 : Finset ℕ := ([48,66,72,192,222,1590,1596,1614,1626,1706,1716,1734,1740,1746,1752,2614,2620,2638,2650,2758,2776,3118,3130,3158,3164,3238,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9638 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9638 66 4
  · have he : independentCachedBranchMembers9638.erase 66=independentCachedBranchMembers9636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9636
  · have he : independentCachedBranchMembers9638.filter (independentCachedEdge 66)=independentCachedBranchMembers9637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9637
def independentCachedBranchMembers9639 : Finset ℕ := ([48,222,1614,1706,1734,1740,2638,2758,3130,3158,3164,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9639 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9639 4 (fun x => (if x<2638 then (if x<1706 then (if x<222 then 0 else (if x<1614 then 1 else 0)) else (if x<1734 then 2 else (if x<1740 then 1 else 2))) else (if x<3158 then (if x<2758 then 1 else (if x<3130 then 0 else 2)) else (if x<3164 then 1 else (if x<3256 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9640 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1706,1716,1734,1740,1746,1752,2614,2620,2638,2650,2758,2776,3118,3130,3158,3164,3238,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9640 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9640 36 4
  · have he : independentCachedBranchMembers9640.erase 36=independentCachedBranchMembers9638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9638
  · have he : independentCachedBranchMembers9640.filter (independentCachedEdge 36)=independentCachedBranchMembers9639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9639
def independentCachedBranchMembers9641 : Finset ℕ := ([192,222,1706,1716,1734,1740,1746,1752,2614,2620,2638,2650,3118,3130,3158,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9641 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9641 4 (fun x => (if x<2614 then (if x<1734 then (if x<1706 then (if x<222 then 0 else 0) else (if x<1716 then 1 else 1)) else (if x<1746 then (if x<1740 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3118 then (if x<2638 then (if x<2620 then 2 else 3) else (if x<2650 then 2 else 3)) else (if x<3158 then (if x<3130 then 2 else 3) else (if x<3164 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9642 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1706,1716,1734,1740,1746,1752,2614,2620,2638,2650,2740,2758,2776,3118,3130,3158,3164,3238,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9642 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9642 2740 4
  · have he : independentCachedBranchMembers9642.erase 2740=independentCachedBranchMembers9640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9640
  · have he : independentCachedBranchMembers9642.filter (independentCachedEdge 2740)=independentCachedBranchMembers9641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9641
def independentCachedBranchMembers9643 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9643 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9643 3242 5
  · have he : independentCachedBranchMembers9643.erase 3242=independentCachedBranchMembers9629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9629
  · have he : independentCachedBranchMembers9643.filter (independentCachedEdge 3242)=independentCachedBranchMembers9642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9642
def independentCachedBranchMembers9644 : Finset ℕ := ([48,66,72,160,190,1590,1596,1614,1626,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2740,2758,2776,3126,3132,3150,3162,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9644 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9644 5 (fun x => (if x<1748 then (if x<1614 then (if x<160 then (if x<66 then 0 else (if x<72 then 0 else 1)) else (if x<1590 then (if x<190 then 1 else 2) else (if x<1596 then 2 else 0))) else (if x<1708 then (if x<1626 then 0 else (if x<1702 then 1 else 3)) else (if x<1720 then (if x<1714 then 2 else 1) else (if x<1738 then 3 else 3)))) else (if x<2776 then (if x<2646 then (if x<2606 then 3 else (if x<2618 then 2 else 4)) else (if x<2740 then (if x<2652 then 4 else 1) else (if x<2758 then 0 else 0))) else (if x<3150 then (if x<3126 then 3 else (if x<3132 then 4 else 2)) else (if x<3238 then (if x<3162 then 1 else 4) else (if x<3256 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9645 : Finset ℕ := ([48,160,1614,1714,1720,1748,2618,2646,2652,2758,3150,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9645 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9645 4 (fun x => (if x<2618 then (if x<1714 then (if x<160 then 0 else (if x<1614 then 1 else 0)) else (if x<1720 then 1 else (if x<1748 then 2 else 2))) else (if x<2758 then (if x<2646 then 2 else (if x<2652 then 2 else 1)) else (if x<3150 then 0 else (if x<3256 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9646 : Finset ℕ := ([36,48,66,72,160,190,1590,1596,1614,1626,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2740,2758,2776,3126,3132,3150,3162,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9646 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9646 36 4
  · have he : independentCachedBranchMembers9646.erase 36=independentCachedBranchMembers9644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9644
  · have he : independentCachedBranchMembers9646.filter (independentCachedEdge 36)=independentCachedBranchMembers9645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9645
def independentCachedBranchMembers9647 : Finset ℕ := ([160,190,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,3126,3132,3150,3162] : List ℕ).toFinset
theorem independentCachedBranchBound9647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9647 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9647 4 (fun x => (if x<2606 then (if x<1714 then (if x<1702 then (if x<190 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1738 then (if x<1720 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<3126 then (if x<2646 then (if x<2618 then 2 else 3) else (if x<2652 then 2 else 3)) else (if x<3150 then (if x<3132 then 2 else 3) else (if x<3162 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9648 : Finset ℕ := ([36,48,66,72,160,190,1590,1596,1614,1626,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2740,2758,2776,3126,3132,3150,3162,3238,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9648 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9648 3274 4
  · have he : independentCachedBranchMembers9648.erase 3274=independentCachedBranchMembers9646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9646
  · have he : independentCachedBranchMembers9648.filter (independentCachedEdge 3274)=independentCachedBranchMembers9647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9647
def independentCachedBranchMembers9649 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9649 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9649 2772 5
  · have he : independentCachedBranchMembers9649.erase 2772=independentCachedBranchMembers9643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9643
  · have he : independentCachedBranchMembers9649.filter (independentCachedEdge 2772)=independentCachedBranchMembers9648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9648
def independentCachedBranchMembers9650 : Finset ℕ := ([36,72,192,222,1590,1626,1702,1720,1738,1740,1746,1748,2618,2620,2638,2646,2732,2738,2740,2758,2776,3118,3126,3162,3164,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9650 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9650 5 (fun x => (if x<2646 then (if x<1720 then (if x<222 then (if x<72 then 0 else (if x<192 then 0 else 1)) else (if x<1626 then (if x<1590 then 1 else 0) else (if x<1702 then 0 else 2))) else (if x<1748 then (if x<1740 then (if x<1738 then 2 else 1) else (if x<1746 then 2 else 2)) else (if x<2620 then (if x<2618 then 1 else 3) else (if x<2638 then 4 else 3)))) else (if x<3126 then (if x<2740 then (if x<2732 then 4 else (if x<2738 then 2 else 2)) else (if x<2776 then (if x<2758 then 0 else 1) else (if x<3118 then 0 else 3))) else (if x<3256 then (if x<3164 then (if x<3162 then 4 else 3) else (if x<3238 then 4 else 0)) else (if x<3276 then (if x<3274 then 3 else 0) else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9651 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2744,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9651 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9651 2744 5
  · have he : independentCachedBranchMembers9651.erase 2744=independentCachedBranchMembers9649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9649
  · have he : independentCachedBranchMembers9651.filter (independentCachedEdge 2744)=independentCachedBranchMembers9650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9650
def independentCachedBranchMembers9652 : Finset ℕ := ([48,66,192,222,1596,1614,1702,1720,1738,1740,1746,1748,2606,2614,2650,2652,2732,2738,2740,2758,2776,3130,3132,3150,3158,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9652 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9652 5 (fun x => (if x<2652 then (if x<1720 then (if x<222 then (if x<66 then 0 else (if x<192 then 0 else 1)) else (if x<1614 then (if x<1596 then 1 else 0) else (if x<1702 then 0 else 2))) else (if x<1748 then (if x<1740 then (if x<1738 then 2 else 1) else (if x<1746 then 2 else 2)) else (if x<2614 then (if x<2606 then 1 else 3) else (if x<2650 then 4 else 3)))) else (if x<3132 then (if x<2740 then (if x<2732 then 4 else (if x<2738 then 2 else 2)) else (if x<2776 then (if x<2758 then 0 else 0) else (if x<3130 then 1 else 3))) else (if x<3256 then (if x<3158 then (if x<3150 then 4 else 3) else (if x<3238 then 4 else 3)) else (if x<3276 then (if x<3274 then 0 else 0) else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9653 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9653 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9653 2726 5
  · have he : independentCachedBranchMembers9653.erase 2726=independentCachedBranchMembers9651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9651
  · have he : independentCachedBranchMembers9653.filter (independentCachedEdge 2726)=independentCachedBranchMembers9652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9652
def independentCachedBranchMembers9654 : Finset ℕ := ([72,192,222,1590,1614,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2758,2762,2776,3118,3132,3158,3162,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9654 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9654 5 (fun x => (if x<2652 then (if x<1734 then (if x<1590 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1708 then (if x<1614 then 1 else 0) else (if x<1714 then 2 else 2))) else (if x<1752 then (if x<1738 then 1 else (if x<1748 then 2 else 2)) else (if x<2618 then (if x<2614 then 0 else 3) else (if x<2638 then 1 else 3)))) else (if x<3158 then (if x<2762 then (if x<2732 then 0 else (if x<2758 then 3 else 4)) else (if x<3118 then (if x<2776 then 0 else 4) else (if x<3132 then 3 else 1))) else (if x<3252 then (if x<3162 then 3 else (if x<3238 then 0 else 4)) else (if x<3276 then (if x<3256 then 2 else 4) else (if x<3282 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9655 : Finset ℕ := ([222,1708,1748,1752,2652,2732,2776,3118,3158,3162,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9655 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9655 4 (fun x => (if x<2776 then (if x<1752 then (if x<1708 then 0 else (if x<1748 then 1 else 0)) else (if x<2652 then 1 else (if x<2732 then 0 else 2))) else (if x<3162 then (if x<3118 then 2 else (if x<3158 then 1 else 0)) else (if x<3238 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9656 : Finset ℕ := ([48,72,192,222,1590,1614,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2758,2762,2776,3118,3132,3158,3162,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9656 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9656 48 4
  · have he : independentCachedBranchMembers9656.erase 48=independentCachedBranchMembers9654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9654
  · have he : independentCachedBranchMembers9656.filter (independentCachedEdge 48)=independentCachedBranchMembers9655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9655
def independentCachedBranchMembers9657 : Finset ℕ := ([48,72,192,222,1590,1614,1734,1752,2614,2638,2758,2776,3118,3158,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9657 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9657 4 (fun x => (if x<2614 then (if x<1590 then (if x<192 then (if x<72 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1734 then (if x<1614 then 0 else 0) else (if x<1752 then 1 else 1))) else (if x<3118 then (if x<2758 then (if x<2638 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3238 then (if x<3158 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9658 : Finset ℕ := ([48,72,192,222,1590,1614,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2758,2762,2776,3118,3132,3158,3162,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9658 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9658 3242 4
  · have he : independentCachedBranchMembers9658.erase 3242=independentCachedBranchMembers9656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9656
  · have he : independentCachedBranchMembers9658.filter (independentCachedEdge 3242)=independentCachedBranchMembers9657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9657
def independentCachedBranchMembers9659 : Finset ℕ := ([48,72,1590,1614,1708,1714,1738,1748,2618,2652,2758,2776,3132,3162,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9659 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9659 4 (fun x => (if x<2618 then (if x<1708 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3132 then (if x<2758 then (if x<2652 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3238 then (if x<3162 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9660 : Finset ℕ := ([48,72,192,222,1590,1614,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2758,2762,2772,2776,3118,3132,3158,3162,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9660 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9660 2772 4
  · have he : independentCachedBranchMembers9660.erase 2772=independentCachedBranchMembers9658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9658
  · have he : independentCachedBranchMembers9660.filter (independentCachedEdge 2772)=independentCachedBranchMembers9659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9659
def independentCachedBranchMembers9661 : Finset ℕ := ([192,222,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,3118,3132,3158,3162] : List ℕ).toFinset
theorem independentCachedBranchBound9661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9661 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9661 4 (fun x => (if x<2614 then (if x<1734 then (if x<1708 then (if x<222 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3118 then (if x<2638 then (if x<2618 then 2 else 3) else (if x<2652 then 2 else 3)) else (if x<3158 then (if x<3132 then 2 else 3) else (if x<3162 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9662 : Finset ℕ := ([48,72,192,222,1590,1614,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2738,2758,2762,2772,2776,3118,3132,3158,3162,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9662 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9662 2738 4
  · have he : independentCachedBranchMembers9662.erase 2738=independentCachedBranchMembers9660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9660
  · have he : independentCachedBranchMembers9662.filter (independentCachedEdge 2738)=independentCachedBranchMembers9661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9661
def independentCachedBranchMembers9663 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9663 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9663 3244 5
  · have he : independentCachedBranchMembers9663.erase 3244=independentCachedBranchMembers9653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9653
  · have he : independentCachedBranchMembers9663.filter (independentCachedEdge 3244)=independentCachedBranchMembers9662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9662
end EntropyDesigns.QuadraticRefinement
