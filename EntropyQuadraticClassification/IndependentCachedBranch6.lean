/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch5
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers768 : Finset ℕ := ([72,252,1590,1626,1642,1652,1692,1708,1714,1776,2620,2638,2710,2762,2772,2788,3102,3118,3164,3180,3186,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers768 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers768 72 4
  · have he : independentCachedBranchMembers768.erase 72=independentCachedBranchMembers766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound766
  · have he : independentCachedBranchMembers768.filter (independentCachedEdge 72)=independentCachedBranchMembers767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound767
def independentCachedBranchMembers769 : Finset ℕ := ([72,252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2668,2674,2710,2714,2730,2740,2758,2762,2772,2776,2788,2792,3102,3118,3150,3164,3180,3186,3226,3238,3252,3256,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers769 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers769 2758 5
  · have he : independentCachedBranchMembers769.erase 2758=independentCachedBranchMembers763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound763
  · have he : independentCachedBranchMembers769.filter (independentCachedEdge 2758)=independentCachedBranchMembers768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound768
def independentCachedBranchMembers770 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers770 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers770 1650 6
  · have he : independentCachedBranchMembers770.erase 1650=independentCachedBranchMembers720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound720
  · have he : independentCachedBranchMembers770.filter (independentCachedEdge 1650)=independentCachedBranchMembers769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound769
def independentCachedBranchMembers771 : Finset ℕ := ([1596,1614,1628,1642,1652,1686,1708,1714,1746,1764,1768,2614,2646,2650,2668,2716,2730,2740,2758,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers771 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers771 6 (fun x => (if x<2730 then (if x<1746 then (if x<1652 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1642 then 1 else 1)) else (if x<1708 then (if x<1686 then 2 else 0) else (if x<1714 then 1 else 2))) else (if x<2646 then (if x<1768 then (if x<1764 then 3 else 0) else (if x<2614 then 2 else 2)) else (if x<2668 then (if x<2650 then 3 else 1) else (if x<2716 then 0 else 1)))) else (if x<3180 then (if x<2800 then (if x<2758 then (if x<2740 then 1 else 0) else (if x<2786 then 0 else 3)) else (if x<3130 then (if x<3102 then 2 else 4) else (if x<3158 then 5 else 5))) else (if x<3252 then (if x<3214 then (if x<3186 then 4 else 3) else (if x<3238 then 5 else 4)) else (if x<3274 then (if x<3256 then 5 else 4) else (if x<3284 then 4 else (if x<3298 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers772 : Finset ℕ := ([1614,1628,1708,1714,1764,1768,2646,2650,2730,2740,2786,2800,3102,3158,3238,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers772 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers772 5 (fun x => (if x<2740 then (if x<1764 then (if x<1708 then (if x<1628 then 0 else 1) else (if x<1714 then 0 else 2)) else (if x<2646 then (if x<1768 then 1 else 2) else (if x<2650 then 0 else (if x<2730 then 1 else 2)))) else (if x<3158 then (if x<2800 then (if x<2786 then 0 else 1) else (if x<3102 then 2 else 1)) else (if x<3252 then (if x<3238 then 3 else 1) else (if x<3256 then 3 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers773 : Finset ℕ := ([1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2646,2650,2668,2716,2730,2740,2758,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers773 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers773 1740 5
  · have he : independentCachedBranchMembers773.erase 1740=independentCachedBranchMembers771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound771
  · have he : independentCachedBranchMembers773.filter (independentCachedEdge 1740)=independentCachedBranchMembers772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound772
def independentCachedBranchMembers774 : Finset ℕ := ([1596,1628,1642,1714,1746,1764,1768,2716,2730,2758,2800,3130,3158,3180,3214,3252,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers774 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers774 5 (fun x => (if x<2758 then (if x<1746 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1714 then 0 else 0)) else (if x<1768 then (if x<1764 then 1 else 0) else (if x<2716 then 1 else (if x<2730 then 2 else 2)))) else (if x<3214 then (if x<3130 then (if x<2800 then 2 else 2) else (if x<3158 then 0 else (if x<3180 then 1 else 0))) else (if x<3256 then (if x<3252 then 2 else 0) else (if x<3284 then 2 else (if x<3298 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers775 : Finset ℕ := ([1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2646,2650,2668,2702,2716,2730,2740,2758,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers775 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers775 2702 5
  · have he : independentCachedBranchMembers775.erase 2702=independentCachedBranchMembers773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound773
  · have he : independentCachedBranchMembers775.filter (independentCachedEdge 2702)=independentCachedBranchMembers774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound774
def independentCachedBranchMembers776 : Finset ℕ := ([1614,1628,1652,1686,1708,1746,1768,2614,2650,2730,2758,3130,3158,3180,3214,3238,3252,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers776 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers776 5 (fun x => (if x<2730 then (if x<1708 then (if x<1652 then (if x<1628 then 0 else 1) else (if x<1686 then 0 else 0)) else (if x<1768 then (if x<1746 then 0 else 1) else (if x<2614 then 1 else (if x<2650 then 2 else 2)))) else (if x<3214 then (if x<3130 then (if x<2758 then 2 else 2) else (if x<3158 then 2 else (if x<3180 then 0 else 0))) else (if x<3252 then (if x<3238 then 0 else 2) else (if x<3274 then 0 else (if x<3298 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers777 : Finset ℕ := ([1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2702,2716,2730,2740,2758,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers777 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers777 2618 5
  · have he : independentCachedBranchMembers777.erase 2618=independentCachedBranchMembers775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound775
  · have he : independentCachedBranchMembers777.filter (independentCachedEdge 2618)=independentCachedBranchMembers776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound776
def independentCachedBranchMembers778 : Finset ℕ := ([1596,1614,1628,1652,1714,1746,1768,2614,2646,2668,2730,2786,2800,3102,3158,3180,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers778 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers778 5 (fun x => (if x<2668 then (if x<1714 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<1768 then (if x<1746 then 2 else 1) else (if x<2614 then 0 else (if x<2646 then 2 else 1)))) else (if x<3158 then (if x<2786 then (if x<2730 then 0 else 2) else (if x<2800 then 1 else (if x<3102 then 2 else 3))) else (if x<3256 then (if x<3180 then 4 else 3) else (if x<3274 then 3 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers779 : Finset ℕ := ([132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2702,2716,2730,2740,2758,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers779 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers779 132 5
  · have he : independentCachedBranchMembers779.erase 132=independentCachedBranchMembers777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound777
  · have he : independentCachedBranchMembers779.filter (independentCachedEdge 132)=independentCachedBranchMembers778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound778
def independentCachedBranchMembers780 : Finset ℕ := ([1628,1642,1686,1708,1746,1764,1768,2646,2650,2668,2716,2730,2786,3102,3158,3180,3238,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers780 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers780 5 (fun x => (if x<2668 then (if x<1746 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1708 then 1 else 0)) else (if x<1768 then (if x<1764 then 2 else 1) else (if x<2646 then 2 else (if x<2650 then 2 else 0)))) else (if x<3158 then (if x<2730 then (if x<2716 then 0 else 0) else (if x<2786 then 0 else (if x<3102 then 2 else 1))) else (if x<3238 then (if x<3180 then 3 else 1) else (if x<3284 then 1 else (if x<3298 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers781 : Finset ℕ := ([48,132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2702,2716,2730,2740,2758,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers781 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers781 48 5
  · have he : independentCachedBranchMembers781.erase 48=independentCachedBranchMembers779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound779
  · have he : independentCachedBranchMembers781.filter (independentCachedEdge 48)=independentCachedBranchMembers780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound780
def independentCachedBranchMembers782 : Finset ℕ := ([48,132,1596,1614,1642,1652,1686,1708,1714,1764,2618,2646,2668,2702,2730,2740,2758,2786,3238,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers782 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers782 5 (fun x => (if x<2646 then (if x<1652 then (if x<1596 then (if x<132 then 0 else 0) else (if x<1614 then 1 else (if x<1642 then 1 else 2))) else (if x<1714 then (if x<1686 then 2 else (if x<1708 then 1 else 2)) else (if x<1764 then 2 else (if x<2618 then 1 else 0)))) else (if x<2758 then (if x<2702 then (if x<2668 then 3 else 1) else (if x<2730 then 0 else (if x<2740 then 2 else 0))) else (if x<3256 then (if x<2786 then 1 else (if x<3238 then 3 else 4)) else (if x<3274 then 4 else (if x<3284 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers783 : Finset ℕ := ([48,132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2702,2716,2730,2740,2758,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers783 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers783 3288 5
  · have he : independentCachedBranchMembers783.erase 3288=independentCachedBranchMembers781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound781
  · have he : independentCachedBranchMembers783.filter (independentCachedEdge 3288)=independentCachedBranchMembers782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound782
def independentCachedBranchMembers784 : Finset ℕ := ([1628,1642,1652,1708,1714,1768,2614,2650,2668,2716,2730,2740,2758,2800,3130,3158,3214,3238,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers784 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers784 5 (fun x => (if x<2740 then (if x<1768 then (if x<1652 then (if x<1642 then 0 else 0) else (if x<1708 then 1 else (if x<1714 then 0 else 1))) else (if x<2668 then (if x<2614 then 1 else (if x<2650 then 1 else 0)) else (if x<2716 then 0 else (if x<2730 then 0 else 0)))) else (if x<3214 then (if x<2800 then (if x<2758 then 2 else 2) else (if x<3130 then 1 else (if x<3158 then 3 else 3))) else (if x<3274 then (if x<3238 then 3 else (if x<3256 then 2 else 2)) else (if x<3284 then 2 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers785 : Finset ℕ := ([48,132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2702,2716,2730,2740,2758,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers785 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers785 3270 5
  · have he : independentCachedBranchMembers785.erase 3270=independentCachedBranchMembers783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound783
  · have he : independentCachedBranchMembers785.filter (independentCachedEdge 3270)=independentCachedBranchMembers784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound784
def independentCachedBranchMembers786 : Finset ℕ := ([48,1596,1614,1708,1714,1768,2618,2646,2716,2730,2740,2758,2800,3102,3180,3186,3214,3238,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers786 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers786 5 (fun x => (if x<2758 then (if x<1768 then (if x<1614 then (if x<1596 then 0 else 0) else (if x<1708 then 0 else (if x<1714 then 1 else 1))) else (if x<2716 then (if x<2618 then 2 else (if x<2646 then 3 else 2)) else (if x<2730 then 3 else (if x<2740 then 1 else 0)))) else (if x<3214 then (if x<3102 then (if x<2800 then 0 else 2) else (if x<3180 then 2 else (if x<3186 then 4 else 3))) else (if x<3274 then (if x<3238 then 4 else (if x<3256 then 1 else 0)) else (if x<3284 then 0 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers787 : Finset ℕ := ([48,132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2702,2716,2730,2740,2758,2772,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers787 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers787 2772 5
  · have he : independentCachedBranchMembers787.erase 2772=independentCachedBranchMembers785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound785
  · have he : independentCachedBranchMembers787.filter (independentCachedEdge 2772)=independentCachedBranchMembers786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound786
def independentCachedBranchMembers788 : Finset ℕ := ([132,1628,1686,1708,1714,1764,2614,2650,2702,2730,2740,2758,2786,3102,3130,3158,3180,3186,3238,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers788 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers788 5 (fun x => (if x<2758 then (if x<1764 then (if x<1686 then (if x<1628 then 0 else 1) else (if x<1708 then 0 else (if x<1714 then 0 else 2))) else (if x<2702 then (if x<2614 then 1 else (if x<2650 then 2 else 1)) else (if x<2730 then 0 else (if x<2740 then 2 else 0)))) else (if x<3180 then (if x<3102 then (if x<2786 then 3 else 1) else (if x<3130 then 1 else (if x<3158 then 2 else 3))) else (if x<3256 then (if x<3186 then 4 else (if x<3238 then 4 else 0)) else (if x<3274 then 4 else (if x<3284 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers789 : Finset ℕ := ([48,132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2702,2716,2730,2740,2758,2762,2772,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers789 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers789 2762 5
  · have he : independentCachedBranchMembers789.erase 2762=independentCachedBranchMembers787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound787
  · have he : independentCachedBranchMembers789.filter (independentCachedEdge 2762)=independentCachedBranchMembers788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound788
def independentCachedBranchMembers790 : Finset ℕ := ([1596,1614,1628,1686,1764,1768,2614,2618,2646,2650,2702,2716,2786,2800,3102,3180,3186,3238,3252,3256,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers790 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers790 5 (fun x => (if x<2786 then (if x<2614 then (if x<1686 then (if x<1614 then 0 else (if x<1628 then 0 else 1)) else (if x<1764 then 0 else (if x<1768 then 0 else 1))) else (if x<2650 then (if x<2618 then 2 else (if x<2646 then 3 else 1)) else (if x<2702 then 2 else (if x<2716 then 2 else 3)))) else (if x<3252 then (if x<3180 then (if x<2800 then 1 else (if x<3102 then 3 else 0)) else (if x<3186 then 0 else (if x<3238 then 2 else 2))) else (if x<3274 then (if x<3256 then 0 else (if x<3270 then 3 else 0)) else (if x<3284 then 2 else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers791 : Finset ℕ := ([48,132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2674,2702,2716,2730,2740,2758,2762,2772,2786,2800,3102,3130,3158,3180,3186,3214,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers791 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers791 2674 5
  · have he : independentCachedBranchMembers791.erase 2674=independentCachedBranchMembers789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound789
  · have he : independentCachedBranchMembers791.filter (independentCachedEdge 2674)=independentCachedBranchMembers790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound790
def independentCachedBranchMembers792 : Finset ℕ := ([1614,1652,1714,1746,1764,1768,2614,2618,2646,2650,2668,2716,2730,2758,2762,2800,3102,3186,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers792 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers792 5 (fun x => (if x<2730 then (if x<2614 then (if x<1746 then (if x<1652 then 0 else (if x<1714 then 0 else 1)) else (if x<1764 then 0 else (if x<1768 then 1 else 0))) else (if x<2650 then (if x<2618 then 2 else (if x<2646 then 1 else 0)) else (if x<2668 then 2 else (if x<2716 then 0 else 2)))) else (if x<3214 then (if x<2800 then (if x<2758 then 2 else (if x<2762 then 2 else 0)) else (if x<3102 then 0 else (if x<3186 then 3 else 3))) else (if x<3284 then (if x<3252 then 4 else (if x<3256 then 3 else 4)) else (if x<3288 then 4 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers793 : Finset ℕ := ([1746,1764,1768,2646,2650,2668,2716,2730,3102,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers793 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers793 4 (fun x => (if x<2716 then (if x<2646 then (if x<1764 then 0 else (if x<1768 then 0 else 1)) else (if x<2650 then 1 else (if x<2668 then 0 else 0))) else (if x<3284 then (if x<2730 then 2 else (if x<3102 then 2 else 1)) else (if x<3288 then 2 else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers794 : Finset ℕ := ([48,1614,1652,1714,1746,1764,1768,2614,2618,2646,2650,2668,2716,2730,2758,2762,2800,3102,3186,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers794 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers794 48 4
  · have he : independentCachedBranchMembers794.erase 48=independentCachedBranchMembers792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound792
  · have he : independentCachedBranchMembers794.filter (independentCachedEdge 48)=independentCachedBranchMembers793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound793
def independentCachedBranchMembers795 : Finset ℕ := ([48,132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2674,2702,2716,2730,2740,2758,2762,2772,2786,2800,3102,3130,3158,3180,3186,3214,3228,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers795 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers795 3228 5
  · have he : independentCachedBranchMembers795.erase 3228=independentCachedBranchMembers791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound791
  · have he : independentCachedBranchMembers795.filter (independentCachedEdge 3228)=independentCachedBranchMembers794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound794
def independentCachedBranchMembers796 : Finset ℕ := ([1614,1628,1642,1708,1746,1764,2614,2650,2668,2702,2716,2730,2758,2772,2786,2800,3102,3130,3158,3186,3238,3252,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers796 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers796 5 (fun x => (if x<2758 then (if x<2614 then (if x<1708 then (if x<1628 then 0 else (if x<1642 then 1 else 1)) else (if x<1746 then 0 else (if x<1764 then 1 else 1))) else (if x<2702 then (if x<2650 then 2 else (if x<2668 then 0 else 0)) else (if x<2716 then 0 else (if x<2730 then 2 else 2)))) else (if x<3158 then (if x<2800 then (if x<2772 then 2 else (if x<2786 then 1 else 1)) else (if x<3102 then 2 else (if x<3130 then 3 else 4))) else (if x<3252 then (if x<3186 then 4 else (if x<3238 then 3 else 3)) else (if x<3274 then 4 else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers797 : Finset ℕ := ([1614,1628,1746,2614,2668,2730,2786,2800,3102,3158,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers797 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers797 4 (fun x => (if x<2786 then (if x<2614 then (if x<1628 then 0 else (if x<1746 then 1 else 0)) else (if x<2668 then 2 else (if x<2730 then 0 else 1))) else (if x<3158 then (if x<2800 then 2 else (if x<3102 then 0 else 2)) else (if x<3274 then 1 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers798 : Finset ℕ := ([132,1614,1628,1642,1708,1746,1764,2614,2650,2668,2702,2716,2730,2758,2772,2786,2800,3102,3130,3158,3186,3238,3252,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers798 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers798 132 4
  · have he : independentCachedBranchMembers798.erase 132=independentCachedBranchMembers796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound796
  · have he : independentCachedBranchMembers798.filter (independentCachedEdge 132)=independentCachedBranchMembers797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound797
def independentCachedBranchMembers799 : Finset ℕ := ([48,132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2674,2702,2716,2730,2740,2758,2762,2772,2786,2800,3102,3126,3130,3158,3180,3186,3214,3228,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers799 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers799 3126 5
  · have he : independentCachedBranchMembers799.erase 3126=independentCachedBranchMembers795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound795
  · have he : independentCachedBranchMembers799.filter (independentCachedEdge 3126)=independentCachedBranchMembers798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound798
def independentCachedBranchMembers800 : Finset ℕ := ([132,1596,1614,1642,1652,1686,1708,1714,1764,2614,2650,2716,2762,2772,2800,3102,3130,3158,3180,3186,3214,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers800 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers800 5 (fun x => (if x<2762 then (if x<1708 then (if x<1642 then (if x<1596 then 0 else (if x<1614 then 1 else 1)) else (if x<1652 then 0 else (if x<1686 then 2 else 1))) else (if x<2614 then (if x<1714 then 0 else (if x<1764 then 2 else 1)) else (if x<2650 then 2 else (if x<2716 then 0 else 0)))) else (if x<3180 then (if x<3102 then (if x<2772 then 3 else (if x<2800 then 3 else 2)) else (if x<3130 then 1 else (if x<3158 then 4 else 4))) else (if x<3252 then (if x<3186 then 1 else (if x<3214 then 0 else 4)) else (if x<3288 then (if x<3270 then 0 else 1) else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers801 : Finset ℕ := ([1642,1686,1708,1764,2650,2716,2772,3102,3158,3180,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers801 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers801 4 (fun x => (if x<2772 then (if x<1764 then (if x<1686 then 0 else (if x<1708 then 1 else 0)) else (if x<2650 then 1 else (if x<2716 then 0 else 0))) else (if x<3180 then (if x<3102 then 1 else (if x<3158 then 2 else 3)) else (if x<3288 then 2 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers802 : Finset ℕ := ([48,132,1596,1614,1642,1652,1686,1708,1714,1764,2614,2650,2716,2762,2772,2800,3102,3130,3158,3180,3186,3214,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers802 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers802 48 4
  · have he : independentCachedBranchMembers802.erase 48=independentCachedBranchMembers800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound800
  · have he : independentCachedBranchMembers802.filter (independentCachedEdge 48)=independentCachedBranchMembers801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound801
def independentCachedBranchMembers803 : Finset ℕ := ([48,132,1596,1614,1628,1642,1652,1686,1708,1714,1740,1746,1764,1768,2614,2618,2646,2650,2668,2674,2702,2716,2730,2740,2758,2762,2772,2776,2786,2800,3102,3126,3130,3158,3180,3186,3214,3228,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers803 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers803 2776 5
  · have he : independentCachedBranchMembers803.erase 2776=independentCachedBranchMembers799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound799
  · have he : independentCachedBranchMembers803.filter (independentCachedEdge 2776)=independentCachedBranchMembers802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound802
def independentCachedBranchMembers804 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers804 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers804 1644 6
  · have he : independentCachedBranchMembers804.erase 1644=independentCachedBranchMembers770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound770
  · have he : independentCachedBranchMembers804.filter (independentCachedEdge 1644)=independentCachedBranchMembers803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound803
def independentCachedBranchMembers805 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,2618,2620,2662,2680,2730,2732,2740,2800,3118,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers805 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers805 6 (fun x => (if x<2680 then (if x<1714 then (if x<1642 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1652 then (if x<1650 then 1 else 2) else (if x<1702 then 1 else 1))) else (if x<1768 then (if x<1720 then 3 else (if x<1764 then 1 else 2)) else (if x<2620 then (if x<2618 then 3 else 2) else (if x<2662 then 4 else 1)))) else (if x<3130 then (if x<2740 then (if x<2730 then 0 else (if x<2732 then 1 else 2)) else (if x<3118 then (if x<2800 then 0 else 2) else (if x<3126 then 4 else 3))) else (if x<3244 then (if x<3188 then (if x<3180 then 5 else 3) else (if x<3192 then 0 else 4)) else (if x<3256 then (if x<3252 then 5 else 4) else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers806 : Finset ℕ := ([48,1650,1702,1720,2620,2662,2680,2732,3126,3130,3180,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers806 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers806 5 (fun x => (if x<2732 then (if x<1720 then (if x<1650 then 0 else (if x<1702 then 0 else 1)) else (if x<2662 then (if x<2620 then 0 else 2) else (if x<2680 then 1 else 0))) else (if x<3180 then (if x<3126 then 1 else (if x<3130 then 2 else 0)) else (if x<3256 then (if x<3252 then 2 else 3) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers807 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,2618,2620,2662,2668,2680,2730,2732,2740,2800,3118,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers807 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers807 2668 5
  · have he : independentCachedBranchMembers807.erase 2668=independentCachedBranchMembers805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound805
  · have he : independentCachedBranchMembers807.filter (independentCachedEdge 2668)=independentCachedBranchMembers806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound806
def independentCachedBranchMembers808 : Finset ℕ := ([252,1642,1720,1764,2618,2620,2662,2740,3126,3180,3192,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers808 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers808 5 (fun x => (if x<2740 then (if x<1764 then (if x<1642 then 0 else (if x<1720 then 1 else 0)) else (if x<2620 then (if x<2618 then 0 else 1) else (if x<2662 then 2 else 1))) else (if x<3192 then (if x<3126 then 0 else (if x<3180 then 2 else 2)) else (if x<3256 then (if x<3244 then 3 else 0) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers809 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,2614,2618,2620,2662,2668,2680,2730,2732,2740,2800,3118,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers809 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers809 2614 5
  · have he : independentCachedBranchMembers809.erase 2614=independentCachedBranchMembers807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound807
  · have he : independentCachedBranchMembers809.filter (independentCachedEdge 2614)=independentCachedBranchMembers808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound808
def independentCachedBranchMembers810 : Finset ℕ := ([48,1596,1650,1652,1702,1714,1768,2618,2620,2662,2740,3126,3180,3192,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers810 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers810 5 (fun x => (if x<2620 then (if x<1702 then (if x<1650 then (if x<1596 then 0 else 0) else (if x<1652 then 0 else 1)) else (if x<1768 then (if x<1714 then 1 else 2) else (if x<2618 then 1 else 0))) else (if x<3180 then (if x<2740 then (if x<2662 then 3 else 3) else (if x<3126 then 2 else 0)) else (if x<3244 then (if x<3192 then 3 else 0) else (if x<3256 then 4 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers811 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,2614,2618,2620,2662,2668,2680,2730,2732,2740,2800,3118,3126,3130,3180,3188,3192,3244,3252,3256,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers811 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers811 3304 5
  · have he : independentCachedBranchMembers811.erase 3304=independentCachedBranchMembers809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound809
  · have he : independentCachedBranchMembers811.filter (independentCachedEdge 3304)=independentCachedBranchMembers810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound810
def independentCachedBranchMembers812 : Finset ℕ := ([252,1596,1642,1652,1714,1764,1768,2620,2662,2680,2732,3126,3130,3180,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers812 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers812 5 (fun x => (if x<2662 then (if x<1714 then (if x<1642 then (if x<1596 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1768 then (if x<1764 then 1 else 0) else (if x<2620 then 2 else 3))) else (if x<3130 then (if x<2732 then (if x<2680 then 3 else 2) else (if x<3126 then 0 else 3)) else (if x<3252 then (if x<3180 then 4 else 0) else (if x<3256 then 0 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers813 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,2614,2618,2620,2662,2668,2680,2730,2732,2740,2800,3118,3126,3130,3180,3188,3192,3244,3250,3252,3256,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers813 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers813 3250 5
  · have he : independentCachedBranchMembers813.erase 3250=independentCachedBranchMembers811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound811
  · have he : independentCachedBranchMembers813.filter (independentCachedEdge 3250)=independentCachedBranchMembers812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound812
def independentCachedBranchMembers814 : Finset ℕ := ([48,1596,1642,1650,1714,1720,1764,2614,2620,2680,2730,3130,3180,3188,3244,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers814 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers814 5 (fun x => (if x<2680 then (if x<1714 then (if x<1642 then (if x<1596 then 0 else 0) else (if x<1650 then 1 else 0)) else (if x<1764 then (if x<1720 then 1 else 2) else (if x<2614 then 1 else (if x<2620 then 0 else 2)))) else (if x<3188 then (if x<3130 then (if x<2730 then 0 else 2) else (if x<3180 then 0 else 1)) else (if x<3252 then (if x<3244 then 0 else 2) else (if x<3298 then 1 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers815 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,2614,2618,2620,2662,2668,2680,2730,2732,2740,2800,3118,3126,3130,3180,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers815 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers815 3300 5
  · have he : independentCachedBranchMembers815.erase 3300=independentCachedBranchMembers813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound813
  · have he : independentCachedBranchMembers815.filter (independentCachedEdge 3300)=independentCachedBranchMembers814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound814
def independentCachedBranchMembers816 : Finset ℕ := ([252,1596,1650,1702,1720,1764,1768,2620,2668,2730,2740,3126,3130,3188,3192,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers816 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers816 5 (fun x => (if x<2730 then (if x<1720 then (if x<1650 then (if x<1596 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<1768 then (if x<1764 then 1 else 0) else (if x<2620 then 2 else (if x<2668 then 3 else 0)))) else (if x<3188 then (if x<3126 then (if x<2740 then 2 else 0) else (if x<3130 then 3 else 4)) else (if x<3244 then (if x<3192 then 0 else 1) else (if x<3250 then 0 else (if x<3298 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers817 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,2614,2618,2620,2662,2668,2680,2730,2732,2740,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers817 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers817 3186 5
  · have he : independentCachedBranchMembers817.erase 3186=independentCachedBranchMembers815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound815
  · have he : independentCachedBranchMembers817.filter (independentCachedEdge 3186)=independentCachedBranchMembers816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound816
def independentCachedBranchMembers818 : Finset ℕ := ([1650,1652,1714,1720,1764,1768,2614,2618,2620,2662,2668,2730,2732,2800,3126,3130,3180,3244] : List ℕ).toFinset
theorem independentCachedBranchBound818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers818 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers818 5 (fun x => (if x<2662 then (if x<1764 then (if x<1714 then (if x<1652 then 0 else 1) else (if x<1720 then 1 else 0)) else (if x<2614 then (if x<1768 then 0 else 1) else (if x<2618 then 1 else (if x<2620 then 0 else 2)))) else (if x<2800 then (if x<2730 then (if x<2668 then 0 else 1) else (if x<2732 then 1 else 0)) else (if x<3130 then (if x<3126 then 0 else 2) else (if x<3180 then 3 else (if x<3244 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers819 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2680,2730,2732,2740,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers819 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers819 1776 5
  · have he : independentCachedBranchMembers819.erase 1776=independentCachedBranchMembers817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound817
  · have he : independentCachedBranchMembers819.filter (independentCachedEdge 1776)=independentCachedBranchMembers818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound818
def independentCachedBranchMembers820 : Finset ℕ := ([48,1596,1642,1650,1714,1720,1764,2618,2662,2668,2732,2740,2800,3118,3126,3186,3192,3250,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers820 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers820 5 (fun x => (if x<2732 then (if x<1720 then (if x<1642 then (if x<1596 then 0 else 0) else (if x<1650 then 1 else (if x<1714 then 0 else 1))) else (if x<2618 then (if x<1764 then 2 else 1) else (if x<2662 then 0 else (if x<2668 then 2 else 1)))) else (if x<3186 then (if x<2800 then (if x<2740 then 2 else 1) else (if x<3118 then 2 else (if x<3126 then 3 else 0))) else (if x<3250 then (if x<3192 then 3 else 0) else (if x<3256 then 4 else (if x<3300 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers821 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2680,2730,2732,2740,2788,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers821 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers821 2788 5
  · have he : independentCachedBranchMembers821.erase 2788=independentCachedBranchMembers819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound819
  · have he : independentCachedBranchMembers821.filter (independentCachedEdge 2788)=independentCachedBranchMembers820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound820
def independentCachedBranchMembers822 : Finset ℕ := ([252,1596,1650,1702,1720,1764,1768,2614,2618,2662,2680,2732,2800,3118,3180,3186,3252,3256,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers822 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers822 5 (fun x => (if x<2680 then (if x<1764 then (if x<1650 then (if x<1596 then 0 else 0) else (if x<1702 then 1 else (if x<1720 then 1 else 1))) else (if x<2614 then (if x<1768 then 0 else 2) else (if x<2618 then 2 else (if x<2662 then 3 else 1)))) else (if x<3186 then (if x<2800 then (if x<2732 then 1 else 0) else (if x<3118 then 2 else (if x<3180 then 3 else 0))) else (if x<3256 then (if x<3252 then 3 else 0) else (if x<3300 then 3 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers823 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2740,2788,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers823 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers823 2674 5
  · have he : independentCachedBranchMembers823.erase 2674=independentCachedBranchMembers821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound821
  · have he : independentCachedBranchMembers823.filter (independentCachedEdge 2674)=independentCachedBranchMembers822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound822
def independentCachedBranchMembers824 : Finset ℕ := ([48,1596,1650,1702,1720,1764,1768,2614,2618,2662,2680,2732,2800,3126,3130,3188,3192,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers824 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers824 5 (fun x => (if x<2680 then (if x<1764 then (if x<1650 then (if x<1596 then 0 else 0) else (if x<1702 then 0 else (if x<1720 then 1 else 1))) else (if x<2614 then (if x<1768 then 2 else 3) else (if x<2618 then 0 else (if x<2662 then 2 else 1)))) else (if x<3188 then (if x<2800 then (if x<2732 then 0 else 1) else (if x<3126 then 2 else (if x<3130 then 3 else 0))) else (if x<3244 then (if x<3192 then 0 else 3) else (if x<3250 then 3 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers825 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1708,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2740,2788,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers825 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers825 1708 5
  · have he : independentCachedBranchMembers825.erase 1708=independentCachedBranchMembers823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound823
  · have he : independentCachedBranchMembers825.filter (independentCachedEdge 1708)=independentCachedBranchMembers824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound824
def independentCachedBranchMembers826 : Finset ℕ := ([252,1596,1642,1650,1714,1720,1764,2618,2662,2668,2732,2740,2800,3130,3180,3188,3244,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers826 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers826 5 (fun x => (if x<2732 then (if x<1720 then (if x<1642 then (if x<1596 then 0 else 0) else (if x<1650 then 1 else (if x<1714 then 2 else 1))) else (if x<2618 then (if x<1764 then 2 else 0) else (if x<2662 then 1 else (if x<2668 then 2 else 0)))) else (if x<3188 then (if x<2800 then (if x<2740 then 2 else 0) else (if x<3130 then 2 else (if x<3180 then 3 else 3))) else (if x<3252 then (if x<3244 then 0 else 0) else (if x<3298 then 3 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers827 : Finset ℕ := ([48,252,1594,1596,1642,1650,1652,1702,1708,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2740,2788,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers827 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers827 1594 5
  · have he : independentCachedBranchMembers827.erase 1594=independentCachedBranchMembers825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound825
  · have he : independentCachedBranchMembers827.filter (independentCachedEdge 1594)=independentCachedBranchMembers826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound826
def independentCachedBranchMembers828 : Finset ℕ := ([48,1596,1650,1652,1702,1714,1768,2614,2668,2680,2730,2732,2788,2800,3118,3130,3186,3188,3250,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers828 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers828 5 (fun x => (if x<2730 then (if x<1714 then (if x<1650 then (if x<1596 then 0 else 0) else (if x<1652 then 0 else (if x<1702 then 1 else 1))) else (if x<2614 then (if x<1768 then 2 else 1) else (if x<2668 then 0 else (if x<2680 then 2 else 0)))) else (if x<3130 then (if x<2788 then (if x<2732 then 1 else 3) else (if x<2800 then 1 else (if x<3118 then 2 else 3))) else (if x<3250 then (if x<3186 then 0 else (if x<3188 then 3 else 0)) else (if x<3252 then 4 else (if x<3304 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers829 : Finset ℕ := ([1596,1650,1714,2668,2732,2800,3130,3188,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers829 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers829 4 (fun x => (if x<2800 then (if x<1714 then (if x<1650 then 0 else 0) else (if x<2668 then 1 else (if x<2732 then 1 else 0))) else (if x<3188 then (if x<3130 then 1 else 2) else (if x<3252 then 2 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers830 : Finset ℕ := ([48,1594,1596,1650,1652,1702,1714,1768,2614,2668,2680,2730,2732,2788,2800,3118,3130,3186,3188,3250,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers830 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers830 1594 4
  · have he : independentCachedBranchMembers830.erase 1594=independentCachedBranchMembers828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound828
  · have he : independentCachedBranchMembers830.filter (independentCachedEdge 1594)=independentCachedBranchMembers829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound829
def independentCachedBranchMembers831 : Finset ℕ := ([48,252,1594,1596,1642,1650,1652,1702,1708,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2740,2788,2792,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers831 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers831 2792 5
  · have he : independentCachedBranchMembers831.erase 2792=independentCachedBranchMembers827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound827
  · have he : independentCachedBranchMembers831.filter (independentCachedEdge 2792)=independentCachedBranchMembers830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound830
def independentCachedBranchMembers832 : Finset ℕ := ([252,1596,1642,1652,1708,1714,1764,1768,2614,2618,2668,2674,2730,2740,2800,3118,3188,3192,3244,3250,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers832 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers832 5 (fun x => (if x<2674 then (if x<1714 then (if x<1642 then (if x<1596 then 0 else 0) else (if x<1652 then 1 else (if x<1708 then 1 else 1))) else (if x<2614 then (if x<1764 then 1 else (if x<1768 then 0 else 2)) else (if x<2618 then 2 else (if x<2668 then 3 else 0)))) else (if x<3188 then (if x<2740 then (if x<2730 then 1 else 1) else (if x<2800 then 0 else (if x<3118 then 2 else 3))) else (if x<3250 then (if x<3192 then 0 else (if x<3244 then 3 else 0)) else (if x<3300 then 3 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers833 : Finset ℕ := ([48,252,1594,1596,1642,1650,1652,1702,1708,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2738,2740,2788,2792,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers833 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers833 2738 5
  · have he : independentCachedBranchMembers833.erase 2738=independentCachedBranchMembers831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound831
  · have he : independentCachedBranchMembers833.filter (independentCachedEdge 2738)=independentCachedBranchMembers832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound832
def independentCachedBranchMembers834 : Finset ℕ := ([48,1596,1642,1652,1708,1714,1764,1768,2614,2618,2668,2674,2730,2740,2800,3126,3130,3180,3186,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers834 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers834 5 (fun x => (if x<2674 then (if x<1714 then (if x<1642 then (if x<1596 then 0 else 0) else (if x<1652 then 1 else (if x<1708 then 1 else 1))) else (if x<2614 then (if x<1764 then 0 else (if x<1768 then 2 else 3)) else (if x<2618 then 0 else (if x<2668 then 2 else 1)))) else (if x<3130 then (if x<2740 then (if x<2730 then 1 else 1) else (if x<2800 then 1 else (if x<3126 then 2 else 3))) else (if x<3252 then (if x<3180 then 0 else (if x<3186 then 3 else 4)) else (if x<3256 then 0 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers835 : Finset ℕ := ([48,252,1594,1596,1642,1644,1650,1652,1702,1708,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2738,2740,2788,2792,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers835 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers835 1644 5
  · have he : independentCachedBranchMembers835.erase 1644=independentCachedBranchMembers833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound833
  · have he : independentCachedBranchMembers835.filter (independentCachedEdge 1644)=independentCachedBranchMembers834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound834
def independentCachedBranchMembers836 : Finset ℕ := ([252,1594,1596,1650,1652,1702,1714,1768,2614,2668,2680,2730,2732,2788,2800,3126,3180,3192,3244,3256,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers836 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers836 5 (fun x => (if x<2730 then (if x<1702 then (if x<1596 then (if x<1594 then 0 else 1) else (if x<1650 then 0 else (if x<1652 then 2 else 1))) else (if x<2614 then (if x<1714 then 1 else (if x<1768 then 3 else 0)) else (if x<2668 then 1 else (if x<2680 then 0 else 1)))) else (if x<3180 then (if x<2788 then (if x<2732 then 1 else 2) else (if x<2800 then 1 else (if x<3126 then 2 else 3))) else (if x<3256 then (if x<3192 then 3 else (if x<3244 then 0 else 0)) else (if x<3298 then 3 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers837 : Finset ℕ := ([48,252,1590,1594,1596,1642,1644,1650,1652,1702,1708,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2738,2740,2788,2792,2800,3118,3126,3130,3180,3186,3188,3192,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers837 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers837 1590 5
  · have he : independentCachedBranchMembers837.erase 1590=independentCachedBranchMembers835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound835
  · have he : independentCachedBranchMembers837.filter (independentCachedEdge 1590)=independentCachedBranchMembers836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound836
def independentCachedBranchMembers838 : Finset ℕ := ([48,252,1596,1642,1650,1652,1702,1720,1768,1776,2618,2620,2668,2674,2792,2800,3118,3126,3192,3244,3250,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers838 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers838 5 (fun x => (if x<2668 then (if x<1702 then (if x<1642 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1650 then 1 else (if x<1652 then 2 else 1))) else (if x<1776 then (if x<1720 then 1 else (if x<1768 then 1 else 2)) else (if x<2618 then 0 else (if x<2620 then 3 else 4)))) else (if x<3192 then (if x<2800 then (if x<2674 then 3 else (if x<2792 then 4 else 4)) else (if x<3118 then 2 else (if x<3126 then 3 else 4))) else (if x<3252 then (if x<3244 then 0 else (if x<3250 then 4 else 3)) else (if x<3298 then 0 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers839 : Finset ℕ := ([48,1596,1642,1652,1768,2618,2668,2674,2800,3126,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers839 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers839 4 (fun x => (if x<2668 then (if x<1652 then (if x<1596 then 0 else (if x<1642 then 0 else 1)) else (if x<1768 then 1 else (if x<2618 then 2 else 0))) else (if x<3126 then (if x<2674 then 1 else (if x<2800 then 1 else 2)) else (if x<3252 then 0 else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers840 : Finset ℕ := ([48,252,1596,1642,1644,1650,1652,1702,1720,1768,1776,2618,2620,2668,2674,2792,2800,3118,3126,3192,3244,3250,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers840 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers840 1644 4
  · have he : independentCachedBranchMembers840.erase 1644=independentCachedBranchMembers838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound838
  · have he : independentCachedBranchMembers840.filter (independentCachedEdge 1644)=independentCachedBranchMembers839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound839
def independentCachedBranchMembers841 : Finset ℕ := ([252,1596,1642,1650,1720,2618,2668,2792,2800,3244,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers841 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers841 4 (fun x => (if x<2668 then (if x<1650 then (if x<1596 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then 2 else (if x<2618 then 1 else 1))) else (if x<3244 then (if x<2792 then 0 else (if x<2800 then 1 else 2)) else (if x<3252 then 0 else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers842 : Finset ℕ := ([48,252,1594,1596,1642,1644,1650,1652,1702,1720,1768,1776,2618,2620,2668,2674,2792,2800,3118,3126,3192,3244,3250,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers842 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers842 1594 4
  · have he : independentCachedBranchMembers842.erase 1594=independentCachedBranchMembers840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound840
  · have he : independentCachedBranchMembers842.filter (independentCachedEdge 1594)=independentCachedBranchMembers841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound841
def independentCachedBranchMembers843 : Finset ℕ := ([48,252,1590,1594,1596,1642,1644,1650,1652,1702,1708,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2738,2740,2788,2792,2800,3118,3126,3130,3180,3186,3188,3192,3238,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers843 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers843 3238 5
  · have he : independentCachedBranchMembers843.erase 3238=independentCachedBranchMembers837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound837
  · have he : independentCachedBranchMembers843.filter (independentCachedEdge 3238)=independentCachedBranchMembers842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound842
def independentCachedBranchMembers844 : Finset ℕ := ([48,252,1596,1642,1652,1702,1714,1720,1764,1776,2614,2620,2732,2738,2788,2800,3118,3130,3180,3186,3192,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers844 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers844 5 (fun x => (if x<2732 then (if x<1714 then (if x<1642 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1652 then 1 else (if x<1702 then 1 else 1))) else (if x<1776 then (if x<1720 then 2 else (if x<1764 then 1 else 2)) else (if x<2614 then 0 else (if x<2620 then 3 else 4)))) else (if x<3180 then (if x<2800 then (if x<2738 then 3 else (if x<2788 then 4 else 4)) else (if x<3118 then 2 else (if x<3130 then 3 else 4))) else (if x<3252 then (if x<3186 then 4 else (if x<3192 then 3 else 0)) else (if x<3298 then 0 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers845 : Finset ℕ := ([48,1596,1702,1720,1764,2614,2732,2738,2800,3130,3192,3298] : List ℕ).toFinset
theorem independentCachedBranchBound845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers845 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers845 4 (fun x => (if x<2732 then (if x<1720 then (if x<1596 then 0 else (if x<1702 then 0 else 1)) else (if x<1764 then 1 else (if x<2614 then 2 else 0))) else (if x<3130 then (if x<2738 then 1 else (if x<2800 then 1 else 2)) else (if x<3192 then 0 else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers846 : Finset ℕ := ([48,252,1596,1642,1652,1702,1708,1714,1720,1764,1776,2614,2620,2732,2738,2788,2800,3118,3130,3180,3186,3192,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers846 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers846 1708 4
  · have he : independentCachedBranchMembers846.erase 1708=independentCachedBranchMembers844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound844
  · have he : independentCachedBranchMembers846.filter (independentCachedEdge 1708)=independentCachedBranchMembers845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound845
def independentCachedBranchMembers847 : Finset ℕ := ([252,1596,1652,1702,1714,2614,2732,2788,2800,3180,3192,3298] : List ℕ).toFinset
theorem independentCachedBranchBound847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers847 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers847 4 (fun x => (if x<2732 then (if x<1702 then (if x<1596 then 0 else (if x<1652 then 0 else 1)) else (if x<1714 then 1 else (if x<2614 then 2 else 1))) else (if x<3180 then (if x<2788 then 0 else (if x<2800 then 1 else 2)) else (if x<3192 then 0 else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers848 : Finset ℕ := ([48,252,1590,1596,1642,1652,1702,1708,1714,1720,1764,1776,2614,2620,2732,2738,2788,2800,3118,3130,3180,3186,3192,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers848 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers848 1590 4
  · have he : independentCachedBranchMembers848.erase 1590=independentCachedBranchMembers846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound846
  · have he : independentCachedBranchMembers848.filter (independentCachedEdge 1590)=independentCachedBranchMembers847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound847
def independentCachedBranchMembers849 : Finset ℕ := ([48,252,1590,1594,1596,1642,1644,1650,1652,1702,1708,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2738,2740,2788,2792,2800,3118,3126,3130,3178,3180,3186,3188,3192,3238,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers849 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers849 3178 5
  · have he : independentCachedBranchMembers849.erase 3178=independentCachedBranchMembers843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound843
  · have he : independentCachedBranchMembers849.filter (independentCachedEdge 3178)=independentCachedBranchMembers848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound848
def independentCachedBranchMembers850 : Finset ℕ := ([48,252,1594,1652,1708,1720,2620,2662,2674,2730,2738,2788,2792,2800,3118,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers850 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers850 5 (fun x => (if x<2792 then (if x<2620 then (if x<1652 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1708 then 0 else (if x<1720 then 1 else 0))) else (if x<2730 then (if x<2662 then 0 else (if x<2674 then 2 else 1)) else (if x<2738 then 1 else (if x<2788 then 2 else 1)))) else (if x<3188 then (if x<3126 then (if x<2800 then 2 else (if x<3118 then 0 else 3)) else (if x<3130 then 2 else (if x<3180 then 4 else 2))) else (if x<3252 then (if x<3192 then 3 else (if x<3244 then 0 else 4)) else (if x<3256 then 0 else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers851 : Finset ℕ := ([48,1652,1708,2674,2730,2800,3126,3130,3180,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers851 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers851 4 (fun x => (if x<3126 then (if x<2674 then (if x<1652 then 0 else (if x<1708 then 0 else 1)) else (if x<2730 then 0 else (if x<2800 then 1 else 2))) else (if x<3252 then (if x<3130 then 0 else (if x<3180 then 3 else 3)) else (if x<3256 then 2 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers852 : Finset ℕ := ([48,252,1594,1644,1652,1708,1720,2620,2662,2674,2730,2738,2788,2792,2800,3118,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers852 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers852 1644 4
  · have he : independentCachedBranchMembers852.erase 1644=independentCachedBranchMembers850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound850
  · have he : independentCachedBranchMembers852.filter (independentCachedEdge 1644)=independentCachedBranchMembers851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound851
def independentCachedBranchMembers853 : Finset ℕ := ([252,1594,1652,2730,2788,2800,3126,3180,3192,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers853 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers853 4 (fun x => (if x<3126 then (if x<2730 then (if x<1594 then 0 else (if x<1652 then 1 else 0)) else (if x<2788 then 1 else (if x<2800 then 0 else 2))) else (if x<3244 then (if x<3180 then 3 else (if x<3192 then 0 else 2)) else (if x<3256 then 3 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers854 : Finset ℕ := ([48,252,1590,1594,1644,1652,1708,1720,2620,2662,2674,2730,2738,2788,2792,2800,3118,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers854 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers854 1590 4
  · have he : independentCachedBranchMembers854.erase 1590=independentCachedBranchMembers852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound852
  · have he : independentCachedBranchMembers854.filter (independentCachedEdge 1590)=independentCachedBranchMembers853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound853
def independentCachedBranchMembers855 : Finset ℕ := ([48,252,1590,1594,1596,1642,1644,1650,1652,1702,1708,1714,1720,1764,1768,1776,2614,2618,2620,2662,2668,2674,2680,2730,2732,2738,2740,2786,2788,2792,2800,3118,3126,3130,3178,3180,3186,3188,3192,3238,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers855 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers855 2786 5
  · have he : independentCachedBranchMembers855.erase 2786=independentCachedBranchMembers849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound849
  · have he : independentCachedBranchMembers855.filter (independentCachedEdge 2786)=independentCachedBranchMembers854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound854
def independentCachedBranchMembers856 : Finset ℕ := ([48,252,1652,1714,1720,1768,2614,2618,2620,2662,2668,2730,2732,2800,3118,3186,3188,3192,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers856 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers856 5 (fun x => (if x<2732 then (if x<2614 then (if x<1714 then (if x<252 then 0 else (if x<1652 then 0 else 0)) else (if x<1720 then 1 else (if x<1768 then 0 else 1))) else (if x<2662 then (if x<2618 then 1 else (if x<2620 then 2 else 0)) else (if x<2668 then 2 else (if x<2730 then 1 else 1)))) else (if x<3250 then (if x<3186 then (if x<2800 then 2 else (if x<3118 then 0 else 2)) else (if x<3188 then 2 else (if x<3192 then 3 else 0))) else (if x<3298 then (if x<3252 then 3 else (if x<3256 then 0 else 2)) else (if x<3300 then 4 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers857 : Finset ℕ := ([48,1652,1768,2614,2620,2730,3118,3186,3192,3250,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers857 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers857 4 (fun x => (if x<3118 then (if x<2614 then (if x<1652 then 0 else (if x<1768 then 0 else 1)) else (if x<2620 then 0 else (if x<2730 then 2 else 1))) else (if x<3250 then (if x<3186 then 2 else (if x<3192 then 0 else 2)) else (if x<3256 then 3 else (if x<3300 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers858 : Finset ℕ := ([48,252,1652,1714,1720,1764,1768,2614,2618,2620,2662,2668,2730,2732,2800,3118,3186,3188,3192,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers858 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers858 1764 4
  · have he : independentCachedBranchMembers858.erase 1764=independentCachedBranchMembers856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound856
  · have he : independentCachedBranchMembers858.filter (independentCachedEdge 1764)=independentCachedBranchMembers857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound857
def independentCachedBranchMembers859 : Finset ℕ := ([252,1652,1714,2620,2668,2730,3118,3186,3252,3256,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers859 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers859 4 (fun x => (if x<3118 then (if x<2620 then (if x<1652 then 0 else (if x<1714 then 0 else 1)) else (if x<2668 then 0 else (if x<2730 then 1 else 1))) else (if x<3256 then (if x<3186 then 2 else (if x<3252 then 2 else 0)) else (if x<3300 then 2 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers860 : Finset ℕ := ([48,252,1650,1652,1714,1720,1764,1768,2614,2618,2620,2662,2668,2730,2732,2800,3118,3186,3188,3192,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers860 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers860 1650 4
  · have he : independentCachedBranchMembers860.erase 1650=independentCachedBranchMembers858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound858
  · have he : independentCachedBranchMembers860.filter (independentCachedEdge 1650)=independentCachedBranchMembers859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound859
def independentCachedBranchMembers861 : Finset ℕ := ([48,252,1590,1594,1596,1642,1644,1650,1652,1702,1708,1714,1720,1764,1768,1776,2606,2614,2618,2620,2662,2668,2674,2680,2730,2732,2738,2740,2786,2788,2792,2800,3118,3126,3130,3178,3180,3186,3188,3192,3238,3244,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers861 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers861 2606 5
  · have he : independentCachedBranchMembers861.erase 2606=independentCachedBranchMembers855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound855
  · have he : independentCachedBranchMembers861.filter (independentCachedEdge 2606)=independentCachedBranchMembers860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound860
def independentCachedBranchMembers862 : Finset ℕ := ([48,72,132,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers862 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers862 222 6
  · have he : independentCachedBranchMembers862.erase 222=independentCachedBranchMembers804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound804
  · have he : independentCachedBranchMembers862.filter (independentCachedEdge 222)=independentCachedBranchMembers861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound861
def independentCachedBranchMembers863 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1692,1702,1714,1720,2650,2662,2680,2710,2730,2732,2740,3150,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers863 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers863 6 (fun x => (if x<2680 then (if x<1678 then (if x<1642 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1644 then 1 else (if x<1652 then 2 else 1))) else (if x<1714 then (if x<1692 then 2 else (if x<1702 then 3 else 1)) else (if x<2650 then (if x<1720 then 3 else 1) else (if x<2662 then 4 else 1)))) else (if x<3178 then (if x<2732 then (if x<2710 then 0 else (if x<2730 then 2 else 1)) else (if x<3150 then (if x<2740 then 2 else 0) else (if x<3164 then 4 else 3))) else (if x<3226 then (if x<3186 then 0 else (if x<3192 then 3 else 4)) else (if x<3244 then (if x<3238 then 3 else 0) else (if x<3252 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers864 : Finset ℕ := ([132,1642,1678,1720,2650,2680,2730,3164,3178,3186,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers864 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers864 5 (fun x => (if x<2730 then (if x<1720 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<2650 then 1 else (if x<2680 then 2 else 0))) else (if x<3186 then (if x<3164 then 1 else (if x<3178 then 2 else 2)) else (if x<3244 then (if x<3226 then 0 else 1) else (if x<3252 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers865 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1692,1702,1714,1720,2650,2652,2662,2680,2710,2730,2732,2740,3150,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers865 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers865 2652 5
  · have he : independentCachedBranchMembers865.erase 2652=independentCachedBranchMembers863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound863
  · have he : independentCachedBranchMembers865.filter (independentCachedEdge 2652)=independentCachedBranchMembers864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound864
def independentCachedBranchMembers866 : Finset ℕ := ([72,132,1642,1644,1678,1692,1702,1714,2680,2740,3150,3164,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers866 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers866 5 (fun x => (if x<1714 then (if x<1644 then (if x<132 then 0 else (if x<1642 then 0 else 0)) else (if x<1692 then (if x<1678 then 1 else 1) else (if x<1702 then 2 else 0))) else (if x<3150 then (if x<2680 then 2 else (if x<2740 then 0 else 0)) else (if x<3186 then (if x<3164 then 1 else 2) else (if x<3244 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers867 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1692,1702,1714,1720,2650,2652,2662,2680,2710,2730,2732,2740,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers867 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers867 3158 5
  · have he : independentCachedBranchMembers867.erase 3158=independentCachedBranchMembers865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound865
  · have he : independentCachedBranchMembers867.filter (independentCachedEdge 3158)=independentCachedBranchMembers866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound866
def independentCachedBranchMembers868 : Finset ℕ := ([72,1644,1702,1720,2650,2662,2680,2732,3150,3164,3186,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers868 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers868 5 (fun x => (if x<2732 then (if x<1720 then (if x<1644 then 0 else (if x<1702 then 0 else 0)) else (if x<2662 then (if x<2650 then 1 else 2) else (if x<2680 then 1 else 0))) else (if x<3186 then (if x<3150 then 1 else (if x<3164 then 2 else 0)) else (if x<3238 then (if x<3226 then 2 else 2) else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers869 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1692,1702,1714,1720,2650,2652,2662,2674,2680,2710,2730,2732,2740,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers869 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers869 2674 5
  · have he : independentCachedBranchMembers869.erase 2674=independentCachedBranchMembers867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound867
  · have he : independentCachedBranchMembers869.filter (independentCachedEdge 2674)=independentCachedBranchMembers868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound868
def independentCachedBranchMembers870 : Finset ℕ := ([132,1652,1692,1702,2650,2652,2662,2740,3150,3186,3192,3226,3238,3244] : List ℕ).toFinset
theorem independentCachedBranchBound870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers870 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers870 5 (fun x => (if x<2740 then (if x<1702 then (if x<1652 then 0 else (if x<1692 then 1 else 0)) else (if x<2652 then (if x<2650 then 0 else 2) else (if x<2662 then 1 else 1))) else (if x<3192 then (if x<3150 then 0 else (if x<3186 then 2 else 2)) else (if x<3238 then (if x<3226 then 3 else 2) else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers871 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1692,1702,1714,1720,2638,2650,2652,2662,2674,2680,2710,2730,2732,2740,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers871 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers871 2638 5
  · have he : independentCachedBranchMembers871.erase 2638=independentCachedBranchMembers869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound869
  · have he : independentCachedBranchMembers871.filter (independentCachedEdge 2638)=independentCachedBranchMembers870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound870
def independentCachedBranchMembers872 : Finset ℕ := ([132,1626,1642,1652,1678,1692,1714,2650,2662,2680,2732,3150,3164,3186,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers872 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers872 5 (fun x => (if x<2662 then (if x<1678 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1714 then (if x<1692 then 0 else 2) else (if x<2650 then 1 else 3))) else (if x<3164 then (if x<2732 then (if x<2680 then 2 else 0) else (if x<3150 then 0 else 3)) else (if x<3226 then (if x<3186 then 4 else 0) else (if x<3238 then 2 else (if x<3252 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers873 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1692,1702,1714,1720,2638,2650,2652,2662,2674,2680,2710,2730,2732,2740,3150,3158,3164,3178,3186,3192,3226,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers873 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers873 3250 5
  · have he : independentCachedBranchMembers873.erase 3250=independentCachedBranchMembers871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound871
  · have he : independentCachedBranchMembers873.filter (independentCachedEdge 3250)=independentCachedBranchMembers872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound872
def independentCachedBranchMembers874 : Finset ℕ := ([72,1626,1644,1652,1692,1702,1714,2638,2650,2680,2730,3164,3178,3186,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers874 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers874 5 (fun x => (if x<2650 then (if x<1692 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1652 then 0 else 1)) else (if x<1714 then (if x<1702 then 1 else 1) else (if x<2638 then 2 else 0))) else (if x<3178 then (if x<2730 then (if x<2680 then 3 else 0) else (if x<3164 then 2 else 0)) else (if x<3226 then (if x<3186 then 0 else 3) else (if x<3244 then 2 else (if x<3252 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers875 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1692,1702,1714,1720,2638,2650,2652,2662,2674,2680,2710,2730,2732,2740,3150,3158,3164,3178,3186,3192,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers875 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers875 3228 5
  · have he : independentCachedBranchMembers875.erase 3228=independentCachedBranchMembers873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound873
  · have he : independentCachedBranchMembers875.filter (independentCachedEdge 3228)=independentCachedBranchMembers874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound874
def independentCachedBranchMembers876 : Finset ℕ := ([72,1626,1642,1644,1678,1714,1720,2650,2652,2662,2740,3150,3186,3192,3226,3228,3238,3244] : List ℕ).toFinset
theorem independentCachedBranchBound876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers876 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers876 5 (fun x => (if x<2662 then (if x<1678 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1644 then 1 else 0)) else (if x<1720 then (if x<1714 then 1 else 1) else (if x<2650 then 2 else (if x<2652 then 3 else 0)))) else (if x<3192 then (if x<3150 then (if x<2740 then 2 else 2) else (if x<3186 then 0 else 1)) else (if x<3228 then (if x<3226 then 0 else 3) else (if x<3238 then 2 else (if x<3244 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers877 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1692,1702,1714,1720,2638,2650,2652,2662,2674,2680,2710,2730,2732,2740,3150,3158,3164,3178,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers877 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers877 3214 5
  · have he : independentCachedBranchMembers877.erase 3214=independentCachedBranchMembers875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound875
  · have he : independentCachedBranchMembers877.filter (independentCachedEdge 3214)=independentCachedBranchMembers876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound876
def independentCachedBranchMembers878 : Finset ℕ := ([132,1626,1644,1678,1692,1702,1720,2650,2674,2730,2740,3150,3164,3178,3192,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers878 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers878 5 (fun x => (if x<2730 then (if x<1692 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1678 then 1 else 0)) else (if x<1720 then (if x<1702 then 1 else 1) else (if x<2650 then 2 else (if x<2674 then 3 else 0)))) else (if x<3178 then (if x<3150 then (if x<2740 then 2 else 2) else (if x<3164 then 3 else 1)) else (if x<3226 then (if x<3192 then 4 else 0) else (if x<3244 then 3 else (if x<3250 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers879 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1692,1702,1714,1720,2638,2650,2652,2662,2674,2680,2710,2730,2732,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers879 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers879 3180 5
  · have he : independentCachedBranchMembers879.erase 3180=independentCachedBranchMembers877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound877
  · have he : independentCachedBranchMembers879.filter (independentCachedEdge 3180)=independentCachedBranchMembers878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound878
def independentCachedBranchMembers880 : Finset ℕ := ([1642,1644,1678,1692,1702,1714,2638,2650,2652,2662,2674,2710,2730,2732,3150,3164,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers880 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers880 5 (fun x => (if x<2662 then (if x<1702 then (if x<1678 then (if x<1644 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<2638 then (if x<1714 then 1 else 0) else (if x<2650 then 0 else (if x<2652 then 2 else 1)))) else (if x<2732 then (if x<2710 then (if x<2674 then 1 else 0) else (if x<2730 then 0 else 0)) else (if x<3164 then (if x<3150 then 1 else 2) else (if x<3186 then 3 else (if x<3244 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers881 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1686,1692,1702,1714,1720,2638,2650,2652,2662,2674,2680,2710,2730,2732,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers881 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers881 1686 5
  · have he : independentCachedBranchMembers881.erase 1686=independentCachedBranchMembers879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound879
  · have he : independentCachedBranchMembers881.filter (independentCachedEdge 1686)=independentCachedBranchMembers880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound880
def independentCachedBranchMembers882 : Finset ℕ := ([72,1626,1644,1652,1692,1702,1714,2652,2662,2674,2710,2732,2740,3150,3158,3180,3192,3228,3238,3250] : List ℕ).toFinset
theorem independentCachedBranchBound882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers882 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers882 5 (fun x => (if x<2710 then (if x<1702 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1652 then 0 else (if x<1692 then 1 else 1))) else (if x<2652 then (if x<1714 then 1 else 2) else (if x<2662 then 0 else (if x<2674 then 1 else 2)))) else (if x<3180 then (if x<2740 then (if x<2732 then 2 else 3) else (if x<3150 then 1 else (if x<3158 then 0 else 3))) else (if x<3228 then (if x<3192 then 3 else 0) else (if x<3238 then 3 else (if x<3250 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers883 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1686,1692,1702,1714,1720,2638,2650,2652,2662,2674,2680,2710,2716,2730,2732,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers883 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers883 2716 5
  · have he : independentCachedBranchMembers883.erase 2716=independentCachedBranchMembers881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound881
  · have he : independentCachedBranchMembers883.filter (independentCachedEdge 2716)=independentCachedBranchMembers882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound882
def independentCachedBranchMembers884 : Finset ℕ := ([132,1626,1644,1678,1692,1702,1720,2638,2652,2662,2680,2710,2732,3158,3180,3186,3214,3228,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers884 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers884 5 (fun x => (if x<2680 then (if x<1702 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1678 then 1 else (if x<1692 then 0 else 1))) else (if x<2638 then (if x<1720 then 1 else 2) else (if x<2652 then 2 else (if x<2662 then 1 else 1)))) else (if x<3186 then (if x<2732 then (if x<2710 then 0 else 1) else (if x<3158 then 0 else (if x<3180 then 2 else 3))) else (if x<3228 then (if x<3214 then 0 else 3) else (if x<3238 then 4 else (if x<3252 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers885 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1686,1692,1702,1714,1720,2638,2650,2652,2662,2668,2674,2680,2710,2716,2730,2732,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers885 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers885 2668 5
  · have he : independentCachedBranchMembers885.erase 2668=independentCachedBranchMembers883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound883
  · have he : independentCachedBranchMembers885.filter (independentCachedEdge 2668)=independentCachedBranchMembers884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound884
def independentCachedBranchMembers886 : Finset ℕ := ([72,1626,1644,1678,1692,1702,1720,2638,2652,2662,2680,2710,2732,3150,3164,3178,3192,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers886 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers886 5 (fun x => (if x<2680 then (if x<1702 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1678 then 0 else (if x<1692 then 1 else 2))) else (if x<2638 then (if x<1720 then 2 else 1) else (if x<2652 then 0 else (if x<2662 then 2 else 2)))) else (if x<3178 then (if x<2732 then (if x<2710 then 0 else 2) else (if x<3150 then 1 else (if x<3164 then 3 else 0))) else (if x<3226 then (if x<3192 then 0 else 3) else (if x<3244 then 3 else (if x<3250 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers887 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1686,1692,1702,1708,1714,1720,2638,2650,2652,2662,2668,2674,2680,2710,2716,2730,2732,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers887 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers887 1708 5
  · have he : independentCachedBranchMembers887.erase 1708=independentCachedBranchMembers885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound885
  · have he : independentCachedBranchMembers887.filter (independentCachedEdge 1708)=independentCachedBranchMembers886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound886
def independentCachedBranchMembers888 : Finset ℕ := ([132,1626,1644,1652,1692,1702,1714,2652,2662,2674,2710,2732,2740,3164,3178,3186,3214,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers888 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers888 5 (fun x => (if x<2710 then (if x<1702 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else (if x<1692 then 2 else 0))) else (if x<2652 then (if x<1714 then 1 else 2) else (if x<2662 then 1 else (if x<2674 then 1 else 0)))) else (if x<3186 then (if x<2740 then (if x<2732 then 1 else 1) else (if x<3164 then 0 else (if x<3178 then 2 else 0))) else (if x<3226 then (if x<3214 then 2 else 3) else (if x<3244 then 2 else (if x<3252 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers889 : Finset ℕ := ([72,132,1626,1628,1642,1644,1652,1678,1686,1692,1702,1708,1714,1720,2638,2650,2652,2662,2668,2674,2680,2710,2716,2730,2732,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers889 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers889 1628 5
  · have he : independentCachedBranchMembers889.erase 1628=independentCachedBranchMembers887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound887
  · have he : independentCachedBranchMembers889.filter (independentCachedEdge 1628)=independentCachedBranchMembers888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound888
def independentCachedBranchMembers890 : Finset ℕ := ([132,1626,1642,1652,1678,1692,1708,1714,2638,2652,2668,2674,2710,2730,2740,3158,3178,3192,3214,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers890 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers890 5 (fun x => (if x<2674 then (if x<1692 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else (if x<1678 then 1 else 0))) else (if x<2638 then (if x<1708 then 2 else (if x<1714 then 1 else 1)) else (if x<2652 then 3 else (if x<2668 then 2 else 1)))) else (if x<3178 then (if x<2730 then (if x<2710 then 0 else 2) else (if x<2740 then 1 else (if x<3158 then 1 else 3))) else (if x<3228 then (if x<3192 then 3 else (if x<3214 then 0 else 3)) else (if x<3244 then 4 else (if x<3250 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers891 : Finset ℕ := ([72,132,1626,1628,1642,1644,1652,1678,1686,1692,1702,1708,1714,1720,2638,2650,2652,2662,2668,2674,2680,2710,2716,2730,2732,2738,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers891 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers891 2738 5
  · have he : independentCachedBranchMembers891.erase 2738=independentCachedBranchMembers889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound889
  · have he : independentCachedBranchMembers891.filter (independentCachedEdge 2738)=independentCachedBranchMembers890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound890
def independentCachedBranchMembers892 : Finset ℕ := ([72,1626,1628,1642,1644,1678,1714,1720,2638,2674,2680,2710,2716,2730,2732,3158,3164,3178,3180,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers892 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers892 5 (fun x => (if x<2710 then (if x<1678 then (if x<1628 then (if x<1626 then 0 else 0) else (if x<1642 then 1 else (if x<1644 then 1 else 0))) else (if x<2638 then (if x<1714 then 1 else (if x<1720 then 2 else 1)) else (if x<2674 then 0 else (if x<2680 then 2 else 0)))) else (if x<3164 then (if x<2730 then (if x<2716 then 2 else 1) else (if x<2732 then 1 else (if x<3158 then 3 else 3))) else (if x<3214 then (if x<3178 then 0 else (if x<3180 then 0 else 3)) else (if x<3250 then 3 else (if x<3252 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers893 : Finset ℕ := ([72,132,1626,1628,1642,1644,1652,1678,1686,1692,1702,1708,1714,1720,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers893 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers893 2702 5
  · have he : independentCachedBranchMembers893.erase 2702=independentCachedBranchMembers891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound891
  · have he : independentCachedBranchMembers893.filter (independentCachedEdge 2702)=independentCachedBranchMembers892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound892
def independentCachedBranchMembers894 : Finset ℕ := ([72,1626,1642,1652,1692,1708,1714,2638,2652,2668,2674,2710,2730,2740,3150,3164,3180,3186,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers894 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers894 5 (fun x => (if x<2674 then (if x<1708 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else (if x<1692 then 1 else 2))) else (if x<2638 then (if x<1714 then 1 else 0) else (if x<2652 then 0 else (if x<2668 then 2 else 1)))) else (if x<3164 then (if x<2730 then (if x<2710 then 1 else 2) else (if x<2740 then 1 else (if x<3150 then 1 else 3))) else (if x<3226 then (if x<3180 then 0 else (if x<3186 then 4 else 3)) else (if x<3238 then 3 else (if x<3252 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers895 : Finset ℕ := ([72,1652,1692,1708,2652,2668,2740,3164,3180,3252] : List ℕ).toFinset
theorem independentCachedBranchBound895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers895 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers895 4 (fun x => (if x<2668 then (if x<1692 then (if x<1652 then 0 else 1) else (if x<1708 then 1 else (if x<2652 then 2 else 0))) else (if x<3164 then (if x<2740 then 2 else 0) else (if x<3180 then 1 else (if x<3252 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
