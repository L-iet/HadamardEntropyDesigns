/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch214
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9664 : Finset ℕ := ([160,190,1590,1614,1702,1706,1716,1720,1740,1746,2606,2620,2646,2650,2732,2738,2758,2762,2776,3126,3130,3150,3164,3238,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9664 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9664 5 (fun x => (if x<2650 then (if x<1716 then (if x<1614 then (if x<190 then 0 else (if x<1590 then 0 else 1)) else (if x<1702 then 1 else (if x<1706 then 0 else 1))) else (if x<1746 then (if x<1720 then 2 else (if x<1740 then 0 else 2)) else (if x<2620 then (if x<2606 then 1 else 1) else (if x<2646 then 3 else 1)))) else (if x<3130 then (if x<2758 then (if x<2732 then 3 else (if x<2738 then 0 else 0)) else (if x<2776 then (if x<2762 then 4 else 1) else (if x<3126 then 4 else 2))) else (if x<3238 then (if x<3150 then 3 else (if x<3164 then 2 else 3)) else (if x<3256 then (if x<3252 then 4 else 0) else (if x<3282 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9665 : Finset ℕ := ([190,1706,1720,1746,2606,2620,2646,2732,2758,3130,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9665 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9665 4 (fun x => (if x<2646 then (if x<1746 then (if x<1706 then 0 else (if x<1720 then 0 else 1)) else (if x<2606 then 1 else (if x<2620 then 0 else 1))) else (if x<3130 then (if x<2732 then 1 else (if x<2758 then 2 else 2)) else (if x<3256 then 0 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9666 : Finset ℕ := ([72,160,190,1590,1614,1702,1706,1716,1720,1740,1746,2606,2620,2646,2650,2732,2738,2758,2762,2776,3126,3130,3150,3164,3238,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9666 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9666 72 4
  · have he : independentCachedBranchMembers9666.erase 72=independentCachedBranchMembers9664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9664
  · have he : independentCachedBranchMembers9666.filter (independentCachedEdge 72)=independentCachedBranchMembers9665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9665
def independentCachedBranchMembers9667 : Finset ℕ := ([160,1702,1706,1746,2606,2646,2650,2732,2776,3164,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9667 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9667 4 (fun x => (if x<2650 then (if x<1746 then (if x<1702 then 0 else (if x<1706 then 0 else 1)) else (if x<2606 then 1 else (if x<2646 then 1 else 1))) else (if x<3164 then (if x<2732 then 0 else (if x<2776 then 2 else 2)) else (if x<3238 then 0 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9668 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1706,1716,1720,1740,1746,2606,2620,2646,2650,2732,2738,2758,2762,2776,3126,3130,3150,3164,3238,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9668 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9668 48 4
  · have he : independentCachedBranchMembers9668.erase 48=independentCachedBranchMembers9666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9666
  · have he : independentCachedBranchMembers9668.filter (independentCachedEdge 48)=independentCachedBranchMembers9667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9667
def independentCachedBranchMembers9669 : Finset ℕ := ([160,190,1702,1706,1716,1720,1740,1746,2606,2620,2646,2650,3126,3130,3150,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9669 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9669 4 (fun x => (if x<2606 then (if x<1716 then (if x<1702 then (if x<190 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1740 then (if x<1720 then 1 else 0) else (if x<1746 then 1 else 1))) else (if x<3126 then (if x<2646 then (if x<2620 then 2 else 3) else (if x<2650 then 2 else 3)) else (if x<3150 then (if x<3130 then 2 else 3) else (if x<3164 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9670 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1706,1716,1720,1740,1746,2606,2620,2646,2650,2732,2738,2758,2762,2776,3126,3130,3150,3164,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9670 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9670 3276 4
  · have he : independentCachedBranchMembers9670.erase 3276=independentCachedBranchMembers9668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9668
  · have he : independentCachedBranchMembers9670.filter (independentCachedEdge 3276)=independentCachedBranchMembers9669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9669
def independentCachedBranchMembers9671 : Finset ℕ := ([48,72,1590,1614,1706,1716,1740,1746,2620,2650,2758,2776,3130,3164,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9671 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9671 4 (fun x => (if x<2620 then (if x<1706 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1740 then (if x<1716 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3130 then (if x<2758 then (if x<2650 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3238 then (if x<3164 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9672 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1706,1716,1720,1740,1746,2606,2620,2646,2650,2732,2738,2758,2762,2776,3126,3130,3150,3164,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9672 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9672 3242 4
  · have he : independentCachedBranchMembers9672.erase 3242=independentCachedBranchMembers9670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9670
  · have he : independentCachedBranchMembers9672.filter (independentCachedEdge 3242)=independentCachedBranchMembers9671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9671
def independentCachedBranchMembers9673 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1720,2606,2646,2758,2776,3126,3150,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9673 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9673 4 (fun x => (if x<2606 then (if x<1590 then (if x<160 then (if x<72 then 0 else 0) else (if x<190 then 1 else 1)) else (if x<1702 then (if x<1614 then 0 else 0) else (if x<1720 then 1 else 1))) else (if x<3126 then (if x<2758 then (if x<2646 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3238 then (if x<3150 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9674 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1706,1716,1720,1740,1746,2606,2620,2646,2650,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9674 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9674 2772 4
  · have he : independentCachedBranchMembers9674.erase 2772=independentCachedBranchMembers9672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9672
  · have he : independentCachedBranchMembers9674.filter (independentCachedEdge 2772)=independentCachedBranchMembers9673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9673
def independentCachedBranchMembers9675 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9675 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9675 2770 5
  · have he : independentCachedBranchMembers9675.erase 2770=independentCachedBranchMembers9663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9663
  · have he : independentCachedBranchMembers9675.filter (independentCachedEdge 2770)=independentCachedBranchMembers9674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9674
def independentCachedBranchMembers9676 : Finset ℕ := ([48,192,1590,1614,1626,1706,1708,1720,1734,1746,1748,2606,2618,2620,2646,2738,2740,2762,2776,3118,3130,3132,3158,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9676 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9676 5 (fun x => (if x<2620 then (if x<1708 then (if x<1614 then (if x<192 then 0 else (if x<1590 then 0 else 0)) else (if x<1626 then 1 else (if x<1706 then 2 else 1))) else (if x<1746 then (if x<1720 then 3 else (if x<1734 then 2 else 0)) else (if x<2606 then (if x<1748 then 1 else 2) else (if x<2618 then 1 else 0)))) else (if x<3130 then (if x<2740 then (if x<2646 then 3 else (if x<2738 then 1 else 1)) else (if x<2776 then (if x<2762 then 2 else 0) else (if x<3118 then 2 else 3))) else (if x<3238 then (if x<3132 then 4 else (if x<3158 then 0 else 4)) else (if x<3274 then (if x<3252 then 4 else 3) else (if x<3276 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9677 : Finset ℕ := ([192,1614,1626,1734,1746,1748,2646,2762,2776,3158,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9677 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9677 4 (fun x => (if x<2646 then (if x<1734 then (if x<1614 then 0 else (if x<1626 then 1 else 2)) else (if x<1746 then 0 else (if x<1748 then 1 else 2))) else (if x<3158 then (if x<2762 then 1 else (if x<2776 then 0 else 2)) else (if x<3274 then 3 else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9678 : Finset ℕ := ([48,190,192,1590,1614,1626,1706,1708,1720,1734,1746,1748,2606,2618,2620,2646,2738,2740,2762,2776,3118,3130,3132,3158,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9678 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9678 190 4
  · have he : independentCachedBranchMembers9678.erase 190=independentCachedBranchMembers9676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9676
  · have he : independentCachedBranchMembers9678.filter (independentCachedEdge 190)=independentCachedBranchMembers9677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9677
def independentCachedBranchMembers9679 : Finset ℕ := ([48,1614,1706,1720,1734,1748,2618,2646,2738,3130,3158,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9679 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9679 4 (fun x => (if x<2618 then (if x<1720 then (if x<1614 then 0 else (if x<1706 then 0 else 1)) else (if x<1734 then 2 else (if x<1748 then 1 else 2))) else (if x<3130 then (if x<2646 then 1 else (if x<2738 then 1 else 0)) else (if x<3158 then 2 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9680 : Finset ℕ := ([36,48,190,192,1590,1614,1626,1706,1708,1720,1734,1746,1748,2606,2618,2620,2646,2738,2740,2762,2776,3118,3130,3132,3158,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9680 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9680 36 4
  · have he : independentCachedBranchMembers9680.erase 36=independentCachedBranchMembers9678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9678
  · have he : independentCachedBranchMembers9680.filter (independentCachedEdge 36)=independentCachedBranchMembers9679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9679
def independentCachedBranchMembers9681 : Finset ℕ := ([190,1614,1706,1708,1734,2618,2620,2646,2738,2740,2776,3118,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9681 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9681 4 (fun x => (if x<2646 then (if x<1708 then (if x<1614 then 0 else (if x<1706 then 1 else 0)) else (if x<2618 then (if x<1734 then 1 else 2) else (if x<2620 then 0 else 2))) else (if x<3118 then (if x<2740 then (if x<2738 then 1 else 3) else (if x<2776 then 1 else 3)) else (if x<3274 then (if x<3238 then 0 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9682 : Finset ℕ := ([1706,1708,2646,2776,3118,3238] : List ℕ).toFinset
theorem independentCachedBranchBound9682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9682 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9682 3 (fun x => (if x<2776 then (if x<1708 then 0 else (if x<2646 then 1 else 0)) else (if x<3118 then 2 else (if x<3238 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9683 : Finset ℕ := ([48,190,1614,1706,1708,1734,2618,2620,2646,2738,2740,2776,3118,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9683 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9683 48 3
  · have he : independentCachedBranchMembers9683.erase 48=independentCachedBranchMembers9681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9681
  · have he : independentCachedBranchMembers9683.filter (independentCachedEdge 48)=independentCachedBranchMembers9682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9682
def independentCachedBranchMembers9684 : Finset ℕ := ([36,48,190,192,1590,1614,1626,1706,1708,1720,1734,1746,1748,2606,2618,2620,2646,2738,2740,2762,2776,3118,3130,3132,3158,3238,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9684 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9684 3288 4
  · have he : independentCachedBranchMembers9684.erase 3288=independentCachedBranchMembers9680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9680
  · have he : independentCachedBranchMembers9684.filter (independentCachedEdge 3288)=independentCachedBranchMembers9683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9683
def independentCachedBranchMembers9685 : Finset ℕ := ([48,192,1614,1720,1746,1748,2606,2738,2740,2776,3130,3132,3158,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9685 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9685 4 (fun x => (if x<2740 then (if x<1746 then (if x<1614 then (if x<192 then 0 else 0) else (if x<1720 then 1 else 2)) else (if x<2606 then (if x<1748 then 1 else 2) else (if x<2738 then 1 else 1))) else (if x<3158 then (if x<3130 then (if x<2776 then 2 else 2) else (if x<3132 then 0 else 3)) else (if x<3274 then (if x<3238 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9686 : Finset ℕ := ([36,48,190,192,1590,1614,1626,1706,1708,1720,1734,1746,1748,2606,2618,2620,2646,2726,2738,2740,2762,2776,3118,3130,3132,3158,3238,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9686 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9686 2726 4
  · have he : independentCachedBranchMembers9686.erase 2726=independentCachedBranchMembers9684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9684
  · have he : independentCachedBranchMembers9686.filter (independentCachedEdge 2726)=independentCachedBranchMembers9685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9685
def independentCachedBranchMembers9687 : Finset ℕ := ([192,1706,1708,1720,1734,1746,1748,2606,2618,2620,2646,3118,3130,3132,3158] : List ℕ).toFinset
theorem independentCachedBranchBound9687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9687 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9687 4 (fun x => (if x<2606 then (if x<1720 then (if x<1706 then 0 else (if x<1708 then 1 else 2)) else (if x<1746 then (if x<1734 then 3 else 0) else (if x<1748 then 1 else 2))) else (if x<3118 then (if x<2620 then (if x<2618 then 1 else 0) else (if x<2646 then 3 else 1)) else (if x<3132 then (if x<3130 then 2 else 3) else (if x<3158 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9688 : Finset ℕ := ([192,1734,1746,1748,2646,3158] : List ℕ).toFinset
theorem independentCachedBranchBound9688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9688 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9688 3 (fun x => (if x<1748 then (if x<1734 then 0 else (if x<1746 then 0 else 1)) else (if x<2646 then 2 else (if x<3158 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9689 : Finset ℕ := ([190,192,1706,1708,1720,1734,1746,1748,2606,2618,2620,2646,3118,3130,3132,3158] : List ℕ).toFinset
theorem independentCachedBranchBound9689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9689 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9689 190 3
  · have he : independentCachedBranchMembers9689.erase 190=independentCachedBranchMembers9687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9687
  · have he : independentCachedBranchMembers9689.filter (independentCachedEdge 190)=independentCachedBranchMembers9688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9688
def independentCachedBranchMembers9690 : Finset ℕ := ([36,48,72,190,192,1590,1614,1626,1706,1708,1720,1734,1746,1748,2606,2618,2620,2646,2726,2738,2740,2762,2776,3118,3130,3132,3158,3238,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9690 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9690 72 4
  · have he : independentCachedBranchMembers9690.erase 72=independentCachedBranchMembers9686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9686
  · have he : independentCachedBranchMembers9690.filter (independentCachedEdge 72)=independentCachedBranchMembers9689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9689
def independentCachedBranchMembers9691 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1622,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9691 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9691 1622 5
  · have he : independentCachedBranchMembers9691.erase 1622=independentCachedBranchMembers9675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9675
  · have he : independentCachedBranchMembers9691.filter (independentCachedEdge 1622)=independentCachedBranchMembers9690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9690
def independentCachedBranchMembers9692 : Finset ℕ := ([66,72,160,222,1590,1596,1614,1702,1706,1708,1746,1748,1752,2606,2646,2650,2652,2738,2740,2758,2762,3118,3158,3162,3164,3252,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9692 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9692 5 (fun x => (if x<2646 then (if x<1702 then (if x<222 then (if x<72 then 0 else (if x<160 then 1 else 0)) else (if x<1596 then (if x<1590 then 1 else 2) else (if x<1614 then 3 else 0))) else (if x<1746 then (if x<1706 then 3 else (if x<1708 then 2 else 0)) else (if x<1752 then (if x<1748 then 2 else 3) else (if x<2606 then 1 else 2)))) else (if x<3118 then (if x<2738 then (if x<2650 then 0 else (if x<2652 then 1 else 3)) else (if x<2758 then (if x<2740 then 2 else 0) else (if x<2762 then 3 else 2))) else (if x<3252 then (if x<3162 then (if x<3158 then 4 else 4) else (if x<3164 then 0 else 1)) else (if x<3274 then (if x<3256 then 4 else 0) else (if x<3276 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9693 : Finset ℕ := ([160,1590,1706,1708,1752,2606,2650,2652,2738,2740,2758,3158,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9693 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9693 4 (fun x => (if x<2652 then (if x<1708 then (if x<1590 then 0 else (if x<1706 then 1 else 0)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2650 then 1 else 2))) else (if x<3158 then (if x<2740 then (if x<2738 then 0 else 3) else (if x<2758 then 1 else 3)) else (if x<3274 then (if x<3256 then 0 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9694 : Finset ℕ := ([1706,1708,2606,2758,3158,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9694 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9694 3 (fun x => (if x<2758 then (if x<1708 then 0 else (if x<2606 then 1 else 0)) else (if x<3158 then 2 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9695 : Finset ℕ := ([72,160,1590,1706,1708,1752,2606,2650,2652,2738,2740,2758,3158,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9695 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9695 72 3
  · have he : independentCachedBranchMembers9695.erase 72=independentCachedBranchMembers9693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9693
  · have he : independentCachedBranchMembers9695.filter (independentCachedEdge 72)=independentCachedBranchMembers9694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9694
end EntropyDesigns.QuadraticRefinement
