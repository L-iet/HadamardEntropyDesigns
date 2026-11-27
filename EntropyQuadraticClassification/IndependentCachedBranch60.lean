/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch59
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4704 : Finset ℕ := ([18,36,80,130,192,222,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4704 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4704 18 4
  · have he : independentCachedBranchMembers4704.erase 18=independentCachedBranchMembers4702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4702
  · have he : independentCachedBranchMembers4704.filter (independentCachedEdge 18)=independentCachedBranchMembers4703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4703
def independentCachedBranchMembers4705 : Finset ℕ := ([36,246,1626,1686,1738,1748,2646,2714,2758,2776,3126,3178,3188,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4705 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4705 4 (fun x => (if x<2758 then (if x<1738 then (if x<1626 then (if x<246 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1748 then 2 else 2) else (if x<2714 then 1 else 1))) else (if x<3188 then (if x<3126 then (if x<2776 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4706 : Finset ℕ := ([12,18,36,80,130,192,222,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4706 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4706 12 4
  · have he : independentCachedBranchMembers4706.erase 12=independentCachedBranchMembers4704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4704
  · have he : independentCachedBranchMembers4706.filter (independentCachedEdge 12)=independentCachedBranchMembers4705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4705
def independentCachedBranchMembers4707 : Finset ℕ := ([12,18,34,36,72,80,130,132,192,222,238,246,1582,1590,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1738,1740,1746,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3072,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4707 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4707 1642 5
  · have he : independentCachedBranchMembers4707.erase 1642=independentCachedBranchMembers4687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4687
  · have he : independentCachedBranchMembers4707.filter (independentCachedEdge 1642)=independentCachedBranchMembers4706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4706
def independentCachedBranchMembers4708 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4708 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4708 2744 6
  · have he : independentCachedBranchMembers4708.erase 2744=independentCachedBranchMembers4448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4448
  · have he : independentCachedBranchMembers4708.filter (independentCachedEdge 2744)=independentCachedBranchMembers4707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4707
def independentCachedBranchMembers4709 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,2614,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4709 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4709 6 (fun x => (if x<2758 then (if x<2662 then (if x<1738 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else 0)) else (if x<2614 then (if x<1748 then 0 else 0) else (if x<2652 then 1 else 1))) else (if x<2730 then (if x<2702 then (if x<2680 then 2 else 2) else (if x<2710 then 1 else 3)) else (if x<2738 then (if x<2732 then 2 else 3) else (if x<2740 then 4 else 2)))) else (if x<3178 then (if x<3130 then (if x<2786 then (if x<2776 then 4 else 3) else (if x<2788 then 3 else 1)) else (if x<3150 then (if x<3132 then 4 else 5) else (if x<3158 then 4 else 5))) else (if x<3238 then (if x<3226 then (if x<3188 then 2 else 1) else (if x<3228 then 5 else 3)) else (if x<3282 then (if x<3276 then 1 else 1) else (if x<3304 then 3 else (if x<3312 then 3 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4710 : Finset ℕ := ([1644,1720,1748,2652,2680,2732,2740,2776,2788,3132,3188,3228,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4710 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4710 5 (fun x => (if x<2776 then (if x<2652 then (if x<1720 then 0 else (if x<1748 then 0 else 0)) else (if x<2732 then (if x<2680 then 1 else 2) else (if x<2740 then 1 else 2))) else (if x<3228 then (if x<3132 then (if x<2788 then 3 else 3) else (if x<3188 then 1 else 2)) else (if x<3304 then (if x<3276 then 4 else 1) else (if x<3312 then 3 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4711 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4711 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4711 2650 5
  · have he : independentCachedBranchMembers4711.erase 2650=independentCachedBranchMembers4709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4709
  · have he : independentCachedBranchMembers4711.filter (independentCachedEdge 2650)=independentCachedBranchMembers4710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4710
def independentCachedBranchMembers4712 : Finset ℕ := ([1650,1720,1738,2614,2662,2702,2730,2732,2776,3158,3188,3226,3228,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4712 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4712 5 (fun x => (if x<2732 then (if x<2614 then (if x<1720 then 0 else (if x<1738 then 0 else 0)) else (if x<2702 then (if x<2662 then 1 else 2) else (if x<2730 then 1 else 2))) else (if x<3226 then (if x<3158 then (if x<2776 then 3 else 3) else (if x<3188 then 2 else 1)) else (if x<3276 then (if x<3228 then 2 else 3) else (if x<3304 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4713 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4713 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4713 2606 5
  · have he : independentCachedBranchMembers4713.erase 2606=independentCachedBranchMembers4711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4711
  · have he : independentCachedBranchMembers4713.filter (independentCachedEdge 2606)=independentCachedBranchMembers4712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4712
def independentCachedBranchMembers4714 : Finset ℕ := ([1650,1720,1748,2614,2650,2652,2662,2710,2730,2732,2758,3130,3132,3158,3178,3226,3228,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4714 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4714 5 (fun x => (if x<2758 then (if x<2652 then (if x<1748 then (if x<1720 then 0 else 0) else (if x<2614 then 0 else (if x<2650 then 1 else 1))) else (if x<2710 then (if x<2662 then 2 else 2) else (if x<2730 then 2 else (if x<2732 then 1 else 2)))) else (if x<3226 then (if x<3132 then (if x<3130 then 1 else 0) else (if x<3158 then 3 else (if x<3178 then 0 else 3))) else (if x<3238 then (if x<3228 then 3 else 0) else (if x<3276 then 1 else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4715 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4715 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4715 1776 5
  · have he : independentCachedBranchMembers4715.erase 1776=independentCachedBranchMembers4713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4713
  · have he : independentCachedBranchMembers4715.filter (independentCachedEdge 1776)=independentCachedBranchMembers4714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4714
def independentCachedBranchMembers4716 : Finset ℕ := ([1644,1720,1738,2606,2614,2652,2680,2732,2740,2758,2786,3132,3150,3158,3178,3226,3238,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4716 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4716 5 (fun x => (if x<2786 then (if x<2652 then (if x<1738 then (if x<1720 then 0 else 0) else (if x<2606 then 0 else (if x<2614 then 1 else 2))) else (if x<2732 then (if x<2680 then 1 else 2) else (if x<2740 then 2 else (if x<2758 then 1 else 1)))) else (if x<3226 then (if x<3150 then (if x<3132 then 2 else 0) else (if x<3158 then 0 else (if x<3178 then 3 else 3))) else (if x<3276 then (if x<3238 then 0 else 1) else (if x<3304 then 3 else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4717 : Finset ℕ := ([1644,1650,1690,1702,1720,1738,1748,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4717 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4717 1690 5
  · have he : independentCachedBranchMembers4717.erase 1690=independentCachedBranchMembers4715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4715
  · have he : independentCachedBranchMembers4717.filter (independentCachedEdge 1690)=independentCachedBranchMembers4716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4716
def independentCachedBranchMembers4718 : Finset ℕ := ([1650,1720,1748,2606,2680,2702,2738,2740,2776,2786,2788,3130,3132,3158,3178,3226,3228,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4718 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4718 5 (fun x => (if x<2788 then (if x<2702 then (if x<1748 then (if x<1720 then 0 else 0) else (if x<2606 then 0 else (if x<2680 then 1 else 1))) else (if x<2740 then (if x<2738 then 2 else 1) else (if x<2776 then 2 else (if x<2786 then 2 else 2)))) else (if x<3226 then (if x<3132 then (if x<3130 then 1 else 0) else (if x<3158 then 3 else (if x<3178 then 0 else 3))) else (if x<3238 then (if x<3228 then 3 else 0) else (if x<3276 then 1 else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4719 : Finset ℕ := ([1622,1644,1650,1690,1702,1720,1738,1748,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4719 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4719 1622 5
  · have he : independentCachedBranchMembers4719.erase 1622=independentCachedBranchMembers4717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4717
  · have he : independentCachedBranchMembers4719.filter (independentCachedEdge 1622)=independentCachedBranchMembers4718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4718
def independentCachedBranchMembers4720 : Finset ℕ := ([1644,1720,1738,2650,2662,2702,2710,2730,2738,2776,2788,3132,3150,3158,3178,3226,3238,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4720 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4720 5 (fun x => (if x<2788 then (if x<2702 then (if x<1738 then (if x<1720 then 0 else 0) else (if x<2650 then 0 else (if x<2662 then 1 else 1))) else (if x<2730 then (if x<2710 then 1 else 2) else (if x<2738 then 2 else (if x<2776 then 1 else 2)))) else (if x<3226 then (if x<3150 then (if x<3132 then 2 else 0) else (if x<3158 then 0 else (if x<3178 then 3 else 3))) else (if x<3276 then (if x<3238 then 0 else 1) else (if x<3304 then 3 else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4721 : Finset ℕ := ([1596,1622,1644,1650,1690,1702,1720,1738,1748,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4721 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4721 1596 5
  · have he : independentCachedBranchMembers4721.erase 1596=independentCachedBranchMembers4719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4719
  · have he : independentCachedBranchMembers4721.filter (independentCachedEdge 1596)=independentCachedBranchMembers4720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4720
def independentCachedBranchMembers4722 : Finset ℕ := ([1644,1650,1702,1720,1738,1748,2606,2614,2650,2652,2702,2710,2786,2788,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4722 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4722 5 (fun x => (if x<2710 then (if x<1748 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else (if x<1738 then 0 else 0))) else (if x<2650 then (if x<2606 then 0 else (if x<2614 then 1 else 2)) else (if x<2652 then 1 else (if x<2702 then 2 else 2)))) else (if x<3150 then (if x<2788 then (if x<2786 then 1 else 1) else (if x<3130 then 2 else (if x<3132 then 3 else 4))) else (if x<3228 then (if x<3158 then 3 else (if x<3226 then 4 else 4)) else (if x<3304 then 3 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4723 : Finset ℕ := ([1596,1622,1644,1650,1690,1702,1720,1738,1748,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4723 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4723 3256 5
  · have he : independentCachedBranchMembers4723.erase 3256=independentCachedBranchMembers4721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4721
  · have he : independentCachedBranchMembers4723.filter (independentCachedEdge 3256)=independentCachedBranchMembers4722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4722
def independentCachedBranchMembers4724 : Finset ℕ := ([1622,1644,1720,1738,1776,2606,2650,2652,2662,2702,2738,2740,2758,3130,3132,3150,3188,3226,3228,3238,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4724 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4724 5 (fun x => (if x<2740 then (if x<2606 then (if x<1720 then (if x<1644 then 0 else 0) else (if x<1738 then 1 else (if x<1776 then 0 else 0))) else (if x<2662 then (if x<2650 then 2 else (if x<2652 then 2 else 3)) else (if x<2702 then 1 else (if x<2738 then 3 else 1)))) else (if x<3188 then (if x<3130 then (if x<2758 then 3 else 2) else (if x<3132 then 2 else (if x<3150 then 4 else 0))) else (if x<3238 then (if x<3226 then 0 else (if x<3228 then 1 else 3)) else (if x<3282 then 2 else (if x<3304 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4725 : Finset ℕ := ([1596,1622,1644,1650,1690,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4725 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4725 1768 5
  · have he : independentCachedBranchMembers4725.erase 1768=independentCachedBranchMembers4723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4723
  · have he : independentCachedBranchMembers4725.filter (independentCachedEdge 1768)=independentCachedBranchMembers4724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4724
def independentCachedBranchMembers4726 : Finset ℕ := ([1596,1650,1690,1720,1748,2606,2614,2650,2680,2730,2738,2758,2788,3130,3150,3158,3188,3228,3238,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4726 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4726 5 (fun x => (if x<2758 then (if x<2606 then (if x<1690 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else (if x<1748 then 1 else 0))) else (if x<2680 then (if x<2614 then 2 else (if x<2650 then 3 else 2)) else (if x<2730 then 1 else (if x<2738 then 1 else 2)))) else (if x<3188 then (if x<3130 then (if x<2788 then 2 else 3) else (if x<3150 then 0 else (if x<3158 then 2 else 4))) else (if x<3282 then (if x<3228 then 0 else (if x<3238 then 0 else 2)) else (if x<3304 then 0 else (if x<3312 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4727 : Finset ℕ := ([1596,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4727 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4727 1692 5
  · have he : independentCachedBranchMembers4727.erase 1692=independentCachedBranchMembers4725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4725
  · have he : independentCachedBranchMembers4727.filter (independentCachedEdge 1692)=independentCachedBranchMembers4726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4726
def independentCachedBranchMembers4728 : Finset ℕ := ([1622,1644,1720,1738,1776,2614,2680,2710,2730,2732,2776,2786,2788,3130,3132,3150,3188,3226,3228,3238,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4728 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4728 5 (fun x => (if x<2786 then (if x<2614 then (if x<1720 then (if x<1644 then 0 else 0) else (if x<1738 then 1 else (if x<1776 then 0 else 0))) else (if x<2730 then (if x<2680 then 2 else (if x<2710 then 1 else 3)) else (if x<2732 then 1 else (if x<2776 then 2 else 3)))) else (if x<3188 then (if x<3130 then (if x<2788 then 2 else 3) else (if x<3132 then 1 else (if x<3150 then 2 else 0))) else (if x<3238 then (if x<3226 then 0 else (if x<3228 then 3 else 4)) else (if x<3282 then 2 else (if x<3304 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4729 : Finset ℕ := ([1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4729 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4729 1614 5
  · have he : independentCachedBranchMembers4729.erase 1614=independentCachedBranchMembers4727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4727
  · have he : independentCachedBranchMembers4729.filter (independentCachedEdge 1614)=independentCachedBranchMembers4728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4728
def independentCachedBranchMembers4730 : Finset ℕ := ([1596,1650,1690,1720,1748,2652,2662,2702,2710,2732,2740,2776,2786,3130,3150,3158,3188,3228,3238,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4730 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4730 5 (fun x => (if x<2776 then (if x<2652 then (if x<1690 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else (if x<1748 then 1 else 0))) else (if x<2710 then (if x<2662 then 2 else (if x<2702 then 1 else 2)) else (if x<2732 then 3 else (if x<2740 then 1 else 2)))) else (if x<3188 then (if x<3130 then (if x<2786 then 3 else 3) else (if x<3150 then 0 else (if x<3158 then 2 else 1))) else (if x<3282 then (if x<3228 then 0 else (if x<3238 then 0 else 2)) else (if x<3304 then 0 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4731 : Finset ℕ := ([1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4731 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4731 1594 5
  · have he : independentCachedBranchMembers4731.erase 1594=independentCachedBranchMembers4729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4729
  · have he : independentCachedBranchMembers4731.filter (independentCachedEdge 1594)=independentCachedBranchMembers4730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4730
def independentCachedBranchMembers4732 : Finset ℕ := ([1594,1614,1622,1650,1690,1702,1738,2606,2614,2650,2662,2702,2710,2730,2738,2758,2786,3130,3150,3158,3178,3226,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4732 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4732 5 (fun x => (if x<2710 then (if x<1738 then (if x<1650 then (if x<1614 then 0 else (if x<1622 then 0 else 1)) else (if x<1690 then 2 else (if x<1702 then 1 else 0))) else (if x<2650 then (if x<2606 then 2 else (if x<2614 then 0 else 2)) else (if x<2662 then 0 else (if x<2702 then 1 else 2)))) else (if x<3150 then (if x<2758 then (if x<2730 then 1 else (if x<2738 then 1 else 0)) else (if x<2786 then 0 else (if x<3130 then 2 else 3))) else (if x<3226 then (if x<3158 then 3 else (if x<3178 then 4 else 4)) else (if x<3238 then 4 else (if x<3282 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4733 : Finset ℕ := ([252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4733 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4733 252 5
  · have he : independentCachedBranchMembers4733.erase 252=independentCachedBranchMembers4731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4731
  · have he : independentCachedBranchMembers4733.filter (independentCachedEdge 252)=independentCachedBranchMembers4732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4732
def independentCachedBranchMembers4734 : Finset ℕ := ([1594,1596,1614,1644,1702,1748,1776,2606,2650,2652,2680,2738,2740,2758,2786,2788,3130,3132,3150,3178,3238,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4734 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4734 5 (fun x => (if x<2738 then (if x<1748 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1644 then 0 else (if x<1702 then 2 else 0))) else (if x<2650 then (if x<1776 then 1 else (if x<2606 then 2 else 0)) else (if x<2652 then 0 else (if x<2680 then 1 else 2)))) else (if x<3132 then (if x<2786 then (if x<2740 then 0 else (if x<2758 then 1 else 0)) else (if x<2788 then 3 else (if x<3130 then 2 else 4))) else (if x<3238 then (if x<3150 then 3 else (if x<3178 then 4 else 3)) else (if x<3282 then 3 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4735 : Finset ℕ := ([1594,1596,1614,1776,2680,2738,2740,2758,3130,3132,3150,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4735 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4735 4 (fun x => (if x<2740 then (if x<1776 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<2680 then 1 else (if x<2738 then 1 else 0))) else (if x<3132 then (if x<2758 then 1 else (if x<3130 then 0 else 2)) else (if x<3150 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
