/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch31
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3808 : Finset ℕ := ([18,80,144,222,1622,1626,1628,1686,1690,1746,1748,1752,2646,2650,2652,2710,2714,2716,2770,2772,2776,3102,3158,3162,3222,3226,3228,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3808 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3808 3222 4
  · have he : independentCachedBranchMembers3808.erase 3222=independentCachedBranchMembers3806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3806
  · have he : independentCachedBranchMembers3808.filter (independentCachedEdge 3222)=independentCachedBranchMembers3807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3807
def independentCachedBranchMembers3809 : Finset ℕ := ([18,80,1628,1686,1690,1748,1752,2646,2650,2716,2770,3158,3162,3228,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3809 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3809 4 (fun x => (if x<2646 then (if x<1686 then (if x<80 then 0 else (if x<1628 then 1 else 1)) else (if x<1748 then (if x<1690 then 0 else 2) else (if x<1752 then 2 else 3))) else (if x<3158 then (if x<2716 then (if x<2650 then 0 else 1) else (if x<2770 then 2 else 2)) else (if x<3228 then (if x<3162 then 1 else 3) else (if x<3282 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3810 : Finset ℕ := ([18,80,144,222,1622,1626,1628,1686,1690,1692,1746,1748,1752,2646,2650,2652,2710,2714,2716,2770,2772,2776,3102,3158,3162,3222,3226,3228,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3810 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3810 1692 4
  · have he : independentCachedBranchMembers3810.erase 1692=independentCachedBranchMembers3808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3808
  · have he : independentCachedBranchMembers3810.filter (independentCachedEdge 1692)=independentCachedBranchMembers3809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3809
def independentCachedBranchMembers3811 : Finset ℕ := ([18,144,1628,1686,1690,1746,2652,2710,2714,2770,3102,3158,3162,3228,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3811 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3811 4 (fun x => (if x<2714 then (if x<1690 then (if x<1628 then (if x<144 then 0 else 1) else (if x<1686 then 2 else 0)) else (if x<2652 then (if x<1746 then 1 else 2) else (if x<2710 then 3 else 1))) else (if x<3162 then (if x<3102 then (if x<2770 then 0 else 3) else (if x<3158 then 0 else 2)) else (if x<3284 then (if x<3228 then 3 else 1) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3812 : Finset ℕ := ([18,80,144,222,1622,1626,1628,1686,1690,1692,1746,1748,1752,2646,2650,2652,2710,2714,2716,2770,2772,2776,3102,3158,3162,3164,3222,3226,3228,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3812 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3812 3164 4
  · have he : independentCachedBranchMembers3812.erase 3164=independentCachedBranchMembers3810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3810
  · have he : independentCachedBranchMembers3812.filter (independentCachedEdge 3164)=independentCachedBranchMembers3811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3811
def independentCachedBranchMembers3813 : Finset ℕ := ([18,48,80,144,222,246,250,252,1590,1594,1596,1622,1626,1628,1650,1652,1686,1690,1692,1714,1720,1746,1748,1752,1776,2614,2618,2620,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3813 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3813 48 5
  · have he : independentCachedBranchMembers3813.erase 48=independentCachedBranchMembers3803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3803
  · have he : independentCachedBranchMembers3813.filter (independentCachedEdge 48)=independentCachedBranchMembers3812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3812
def independentCachedBranchMembers3814 : Finset ℕ := ([80,144,246,250,1596,1626,1650,1686,1714,1748,1752,1776,2620,2646,2674,2710,2714,2738,2772,2776,2800,3102,3126,3130,3164,3188,3192,3228,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3814 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3814 5 (fun x => (if x<2710 then (if x<1686 then (if x<250 then (if x<144 then 0 else (if x<246 then 1 else 0)) else (if x<1626 then (if x<1596 then 1 else 2) else (if x<1650 then 2 else 0))) else (if x<1776 then (if x<1748 then (if x<1714 then 2 else 1) else (if x<1752 then 0 else 1)) else (if x<2646 then (if x<2620 then 2 else 3) else (if x<2674 then 0 else 3)))) else (if x<3130 then (if x<2776 then (if x<2738 then (if x<2714 then 3 else 1) else (if x<2772 then 4 else 4)) else (if x<3102 then (if x<2800 then 3 else 0) else (if x<3126 then 2 else 3))) else (if x<3228 then (if x<3188 then (if x<3164 then 4 else 4) else (if x<3192 then 0 else 2)) else (if x<3256 then (if x<3252 then 3 else 2) else (if x<3282 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3815 : Finset ℕ := ([144,246,1596,1626,1686,1714,1748,1776,2646,2674,2714,2776,3126,3188,3228,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3815 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3815 4 (fun x => (if x<2646 then (if x<1686 then (if x<1596 then (if x<246 then 0 else 0) else (if x<1626 then 1 else 1)) else (if x<1748 then (if x<1714 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3126 then (if x<2714 then (if x<2674 then 2 else 3) else (if x<2776 then 2 else 3)) else (if x<3228 then (if x<3188 then 3 else 2) else (if x<3256 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3816 : Finset ℕ := ([80,144,246,250,1596,1626,1650,1686,1714,1748,1752,1776,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3102,3126,3130,3164,3188,3192,3228,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3816 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3816 2650 4
  · have he : independentCachedBranchMembers3816.erase 2650=independentCachedBranchMembers3814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3814
  · have he : independentCachedBranchMembers3816.filter (independentCachedEdge 2650)=independentCachedBranchMembers3815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3815
def independentCachedBranchMembers3817 : Finset ℕ := ([246,1626,1686,1714,1752,2620,2646,2674,2714,2772,2800,3126,3164,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound3817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3817 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3817 4 (fun x => (if x<2674 then (if x<1714 then (if x<1626 then 0 else (if x<1686 then 1 else 0)) else (if x<2620 then (if x<1752 then 1 else 2) else (if x<2646 then 3 else 0))) else (if x<3126 then (if x<2772 then (if x<2714 then 1 else 1) else (if x<2800 then 2 else 3)) else (if x<3192 then (if x<3164 then 0 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3818 : Finset ℕ := ([1686,1714,2620,2714,3126,3252] : List ℕ).toFinset
theorem independentCachedBranchBound3818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3818 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3818 3 (fun x => (if x<2714 then (if x<1714 then 0 else (if x<2620 then 1 else 2)) else (if x<3126 then 0 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3819 : Finset ℕ := ([80,246,1626,1686,1714,1752,2620,2646,2674,2714,2772,2800,3126,3164,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound3819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3819 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3819 80 3
  · have he : independentCachedBranchMembers3819.erase 80=independentCachedBranchMembers3817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3817
  · have he : independentCachedBranchMembers3819.filter (independentCachedEdge 80)=independentCachedBranchMembers3818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3818
def independentCachedBranchMembers3820 : Finset ℕ := ([80,144,246,250,1596,1626,1650,1686,1690,1714,1748,1752,1776,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3102,3126,3130,3164,3188,3192,3228,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3820 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3820 1690 4
  · have he : independentCachedBranchMembers3820.erase 1690=independentCachedBranchMembers3816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3816
  · have he : independentCachedBranchMembers3820.filter (independentCachedEdge 1690)=independentCachedBranchMembers3819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3819
def independentCachedBranchMembers3821 : Finset ℕ := ([250,1626,1650,1686,1748,2620,2646,2714,2738,2776,2800,3130,3192,3228,3252] : List ℕ).toFinset
theorem independentCachedBranchBound3821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3821 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3821 4 (fun x => (if x<2714 then (if x<1686 then (if x<1626 then 0 else (if x<1650 then 0 else 1)) else (if x<2620 then (if x<1748 then 1 else 2) else (if x<2646 then 3 else 1))) else (if x<3130 then (if x<2776 then (if x<2738 then 0 else 1) else (if x<2800 then 2 else 3)) else (if x<3228 then (if x<3192 then 0 else 3) else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3822 : Finset ℕ := ([1626,1650,2620,2646,3130,3192] : List ℕ).toFinset
theorem independentCachedBranchBound3822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3822 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3822 3 (fun x => (if x<2646 then (if x<1650 then 0 else (if x<2620 then 1 else 2)) else (if x<3130 then 0 else (if x<3192 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3823 : Finset ℕ := ([144,250,1626,1650,1686,1748,2620,2646,2714,2738,2776,2800,3130,3192,3228,3252] : List ℕ).toFinset
theorem independentCachedBranchBound3823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3823 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3823 144 3
  · have he : independentCachedBranchMembers3823.erase 144=independentCachedBranchMembers3821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3821
  · have he : independentCachedBranchMembers3823.filter (independentCachedEdge 144)=independentCachedBranchMembers3822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3822
def independentCachedBranchMembers3824 : Finset ℕ := ([80,144,246,250,1596,1622,1626,1650,1686,1690,1714,1748,1752,1776,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3102,3126,3130,3164,3188,3192,3228,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3824 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3824 1622 4
  · have he : independentCachedBranchMembers3824.erase 1622=independentCachedBranchMembers3820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3820
  · have he : independentCachedBranchMembers3824.filter (independentCachedEdge 1622)=independentCachedBranchMembers3823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3823
def independentCachedBranchMembers3825 : Finset ℕ := ([246,250,1596,1650,1714,1776,2620,2674,2738,2800,3126,3130,3188,3192,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3825 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3825 4 (fun x => (if x<2738 then (if x<1714 then (if x<1596 then (if x<250 then 0 else 1) else (if x<1650 then 2 else 0)) else (if x<2620 then (if x<1776 then 1 else 2) else (if x<2674 then 3 else 1))) else (if x<3188 then (if x<3126 then (if x<2800 then 0 else 3) else (if x<3130 then 0 else 1)) else (if x<3252 then (if x<3192 then 2 else 3) else (if x<3256 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3826 : Finset ℕ := ([80,144,222,246,250,1596,1622,1626,1650,1686,1690,1714,1748,1752,1776,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3102,3126,3130,3164,3188,3192,3228,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3826 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3826 222 4
  · have he : independentCachedBranchMembers3826.erase 222=independentCachedBranchMembers3824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3824
  · have he : independentCachedBranchMembers3826.filter (independentCachedEdge 222)=independentCachedBranchMembers3825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3825
def independentCachedBranchMembers3827 : Finset ℕ := ([80,144,1596,1748,1752,1776,2620,2772,2776,2800,3164,3188,3192,3228,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3827 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3827 4 (fun x => (if x<2776 then (if x<1752 then (if x<1596 then (if x<144 then 0 else 1) else (if x<1748 then 2 else 0)) else (if x<2620 then (if x<1776 then 1 else 2) else (if x<2772 then 3 else 1))) else (if x<3192 then (if x<3164 then (if x<2800 then 0 else 3) else (if x<3188 then 0 else 2)) else (if x<3252 then (if x<3228 then 3 else 1) else (if x<3256 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3828 : Finset ℕ := ([18,80,144,222,246,250,1596,1622,1626,1650,1686,1690,1714,1748,1752,1776,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3102,3126,3130,3164,3188,3192,3228,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3828 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3828 18 4
  · have he : independentCachedBranchMembers3828.erase 18=independentCachedBranchMembers3826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3826
  · have he : independentCachedBranchMembers3828.filter (independentCachedEdge 18)=independentCachedBranchMembers3827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3827
def independentCachedBranchMembers3829 : Finset ℕ := ([18,48,80,144,222,246,250,252,1590,1594,1596,1622,1626,1628,1650,1652,1686,1690,1692,1714,1720,1746,1748,1752,1776,2614,2618,2620,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3132,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3829 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3829 3132 5
  · have he : independentCachedBranchMembers3829.erase 3132=independentCachedBranchMembers3813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3813
  · have he : independentCachedBranchMembers3829.filter (independentCachedEdge 3132)=independentCachedBranchMembers3828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3828
def independentCachedBranchMembers3830 : Finset ℕ := ([12,18,36,40,48,66,72,80,130,132,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3830 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3830 238 6
  · have he : independentCachedBranchMembers3830.erase 238=independentCachedBranchMembers3674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3674
  · have he : independentCachedBranchMembers3830.filter (independentCachedEdge 238)=independentCachedBranchMembers3829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3829
def independentCachedBranchMembers3831 : Finset ℕ := ([40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2680,2738,2740,2758,2770,2786,3132,3178,3250,3270,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3831 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3831 6 (fun x => (if x<1776 then (if x<1614 then (if x<192 then (if x<130 then 0 else (if x<144 then 0 else 1)) else (if x<1594 then (if x<246 then 2 else 1) else (if x<1596 then 2 else 0))) else (if x<1702 then (if x<1644 then 3 else (if x<1686 then 4 else 0)) else (if x<1748 then (if x<1746 then 3 else 1) else (if x<1762 then 3 else 2)))) else (if x<2786 then (if x<2738 then (if x<2606 then 4 else (if x<2680 then 3 else 0)) else (if x<2758 then (if x<2740 then 1 else 3) else (if x<2770 then 2 else 0))) else (if x<3250 then (if x<3132 then 5 else (if x<3178 then 2 else 5)) else (if x<3282 then (if x<3270 then 4 else 0) else (if x<3312 then 5 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3832 : Finset ℕ := ([40,246,1594,1686,1702,1748,2680,2740,2758,3178,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3832 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3832 5 (fun x => (if x<1748 then (if x<1594 then (if x<246 then 0 else 1) else (if x<1686 then 0 else (if x<1702 then 0 else 1))) else (if x<2758 then (if x<2680 then 1 else (if x<2740 then 0 else 1)) else (if x<3178 then 1 else (if x<3270 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3833 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2680,2738,2740,2758,2770,2786,3132,3178,3250,3270,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3833 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3833 12 5
  · have he : independentCachedBranchMembers3833.erase 12=independentCachedBranchMembers3831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3831
  · have he : independentCachedBranchMembers3833.filter (independentCachedEdge 12)=independentCachedBranchMembers3832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3832
def independentCachedBranchMembers3834 : Finset ℕ := ([12,130,1596,1614,1644,1702,1748,1762,2680,2738,2786,3178,3270,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3834 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3834 5 (fun x => (if x<1762 then (if x<1614 then (if x<130 then 0 else (if x<1596 then 0 else 0)) else (if x<1702 then (if x<1644 then 1 else 2) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2738 then (if x<2680 then 2 else 3) else (if x<2786 then 2 else 0)) else (if x<3282 then (if x<3270 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3835 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2680,2738,2740,2758,2770,2786,3132,3178,3250,3270,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3835 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3835 3284 5
  · have he : independentCachedBranchMembers3835.erase 3284=independentCachedBranchMembers3833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3833
  · have he : independentCachedBranchMembers3835.filter (independentCachedEdge 3284)=independentCachedBranchMembers3834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3834
def independentCachedBranchMembers3836 : Finset ℕ := ([192,246,1594,1644,1702,1748,1762,1776,2740,2758,2786,3132,3178,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3836 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3836 5 (fun x => (if x<1776 then (if x<1644 then (if x<246 then 0 else (if x<1594 then 0 else 1)) else (if x<1748 then (if x<1702 then 1 else 1) else (if x<1762 then 0 else 0))) else (if x<3132 then (if x<2758 then (if x<2740 then 1 else 2) else (if x<2786 then 0 else 2)) else (if x<3250 then (if x<3178 then 2 else 2) else (if x<3282 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3837 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2680,2738,2740,2758,2770,2786,3132,3178,3180,3250,3270,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3837 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3837 3180 5
  · have he : independentCachedBranchMembers3837.erase 3180=independentCachedBranchMembers3835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3835
  · have he : independentCachedBranchMembers3837.filter (independentCachedEdge 3180)=independentCachedBranchMembers3836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3836
def independentCachedBranchMembers3838 : Finset ℕ := ([40,130,144,246,1644,1702,1746,1748,2680,2738,2740,2758,2770,3132,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3838 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3838 5 (fun x => (if x<1748 then (if x<246 then (if x<130 then 0 else (if x<144 then 0 else 1)) else (if x<1702 then (if x<1644 then 1 else 0) else (if x<1746 then 2 else 1))) else (if x<2758 then (if x<2738 then (if x<2680 then 2 else 0) else (if x<2740 then 1 else 2)) else (if x<3132 then (if x<2770 then 2 else 0) else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3839 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2680,2738,2740,2758,2770,2786,3102,3132,3178,3180,3250,3270,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3839 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3839 3102 5
  · have he : independentCachedBranchMembers3839.erase 3102=independentCachedBranchMembers3837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3837
  · have he : independentCachedBranchMembers3839.filter (independentCachedEdge 3102)=independentCachedBranchMembers3838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3838
end EntropyDesigns.QuadraticRefinement
