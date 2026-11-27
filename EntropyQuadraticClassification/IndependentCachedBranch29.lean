/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch28
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3712 : Finset ℕ := ([1590,1776,2618,2770,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3712 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3712 3 (fun x => (if x<2770 then (if x<1776 then 0 else (if x<2618 then 0 else 1)) else (if x<3222 then 1 else (if x<3256 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3713 : Finset ℕ := ([144,1590,1748,1776,2618,2770,2776,3162,3188,3222,3228,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3713 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3713 3228 3
  · have he : independentCachedBranchMembers3713.erase 3228=independentCachedBranchMembers3711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3711
  · have he : independentCachedBranchMembers3713.filter (independentCachedEdge 3228)=independentCachedBranchMembers3712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3712
def independentCachedBranchMembers3714 : Finset ℕ := ([18,144,222,250,1590,1628,1650,1690,1748,1776,2618,2650,2710,2716,2738,2770,2776,3102,3130,3162,3188,3222,3228,3250,3256,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3714 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3714 2650 4
  · have he : independentCachedBranchMembers3714.erase 2650=independentCachedBranchMembers3710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3710
  · have he : independentCachedBranchMembers3714.filter (independentCachedEdge 2650)=independentCachedBranchMembers3713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3713
def independentCachedBranchMembers3715 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1652,1686,1690,1714,1720,1746,1748,1752,1776,2618,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3715 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3715 1652 5
  · have he : independentCachedBranchMembers3715.erase 1652=independentCachedBranchMembers3707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3707
  · have he : independentCachedBranchMembers3715.filter (independentCachedEdge 1652)=independentCachedBranchMembers3714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3714
def independentCachedBranchMembers3716 : Finset ℕ := ([18,144,246,250,1590,1628,1650,1686,1690,1720,1746,1776,2618,2674,2710,2714,2740,2770,2800,3102,3158,3162,3188,3192,3228,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3716 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3716 5 (fun x => (if x<2710 then (if x<1686 then (if x<250 then (if x<144 then 0 else (if x<246 then 1 else 0)) else (if x<1628 then (if x<1590 then 1 else 0) else (if x<1650 then 2 else 2))) else (if x<1746 then (if x<1690 then 2 else (if x<1720 then 1 else 2)) else (if x<2618 then (if x<1776 then 0 else 1) else (if x<2674 then 3 else 0)))) else (if x<3162 then (if x<2770 then (if x<2714 then 0 else (if x<2740 then 4 else 3)) else (if x<3102 then (if x<2800 then 1 else 4) else (if x<3158 then 4 else 0))) else (if x<3228 then (if x<3188 then 3 else (if x<3192 then 4 else 2)) else (if x<3284 then (if x<3250 then 2 else 0) else (if x<3288 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3717 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1652,1686,1690,1714,1720,1746,1748,1752,1776,2618,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3717 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3717 3164 5
  · have he : independentCachedBranchMembers3717.erase 3164=independentCachedBranchMembers3715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3715
  · have he : independentCachedBranchMembers3717.filter (independentCachedEdge 3164)=independentCachedBranchMembers3716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3716
def independentCachedBranchMembers3718 : Finset ℕ := ([80,144,222,250,1590,1626,1628,1690,1720,1746,1748,1776,2650,2680,2714,2716,2770,2772,2800,3102,3130,3158,3186,3188,3222,3250,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3718 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3718 5 (fun x => (if x<2714 then (if x<1690 then (if x<250 then (if x<144 then 0 else (if x<222 then 1 else 0)) else (if x<1626 then (if x<1590 then 1 else 2) else (if x<1628 then 0 else 2))) else (if x<1748 then (if x<1720 then 1 else (if x<1746 then 2 else 2)) else (if x<2650 then (if x<1776 then 0 else 1) else (if x<2680 then 3 else 4)))) else (if x<3158 then (if x<2772 then (if x<2716 then 4 else (if x<2770 then 3 else 0)) else (if x<3102 then (if x<2800 then 4 else 3) else (if x<3130 then 3 else 4))) else (if x<3222 then (if x<3186 then 0 else (if x<3188 then 3 else 4)) else (if x<3252 then (if x<3250 then 4 else 1) else (if x<3288 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3719 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1652,1686,1690,1714,1720,1746,1748,1752,1776,2618,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3719 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3719 3126 5
  · have he : independentCachedBranchMembers3719.erase 3126=independentCachedBranchMembers3717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3717
  · have he : independentCachedBranchMembers3719.filter (independentCachedEdge 3126)=independentCachedBranchMembers3718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3718
def independentCachedBranchMembers3720 : Finset ℕ := ([18,80,144,222,246,250,1626,1650,1686,1714,1748,1752,2618,2680,2716,2740,2770,3162,3186,3222,3226,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3720 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3720 5 (fun x => (if x<1752 then (if x<250 then (if x<144 then (if x<80 then 0 else 1) else (if x<222 then 2 else (if x<246 then 0 else 1))) else (if x<1686 then (if x<1626 then 2 else (if x<1650 then 0 else 1)) else (if x<1714 then 0 else (if x<1748 then 2 else 1)))) else (if x<3162 then (if x<2716 then (if x<2618 then 2 else (if x<2680 then 3 else 4)) else (if x<2740 then 3 else (if x<2770 then 4 else 0))) else (if x<3226 then (if x<3186 then 4 else (if x<3222 then 3 else 4)) else (if x<3284 then 0 else (if x<3312 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3721 : Finset ℕ := ([18,246,1650,1686,1714,1752,2618,2740,3162,3226,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3721 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3721 4 (fun x => (if x<2618 then (if x<1686 then (if x<246 then 0 else (if x<1650 then 0 else 0)) else (if x<1714 then 0 else (if x<1752 then 1 else 1))) else (if x<3226 then (if x<2740 then 2 else (if x<3162 then 2 else 2)) else (if x<3284 then 1 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3722 : Finset ℕ := ([18,80,144,222,246,250,1626,1650,1686,1714,1748,1752,2618,2680,2716,2740,2770,3162,3186,3222,3226,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3722 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3722 3288 4
  · have he : independentCachedBranchMembers3722.erase 3288=independentCachedBranchMembers3720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3720
  · have he : independentCachedBranchMembers3722.filter (independentCachedEdge 3288)=independentCachedBranchMembers3721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3721
def independentCachedBranchMembers3723 : Finset ℕ := ([80,222,1626,1714,1748,1752,2680,2716,3186,3222,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3723 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3723 4 (fun x => (if x<2680 then (if x<1714 then (if x<222 then 0 else (if x<1626 then 0 else 0)) else (if x<1748 then 1 else (if x<1752 then 0 else 1))) else (if x<3222 then (if x<2716 then 2 else (if x<3186 then 2 else 2)) else (if x<3226 then 2 else (if x<3312 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3724 : Finset ℕ := ([18,80,144,222,246,250,1626,1650,1686,1714,1748,1752,2618,2680,2716,2740,2770,3162,3186,3222,3226,3250,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3724 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3724 3250 4
  · have he : independentCachedBranchMembers3724.erase 3250=independentCachedBranchMembers3722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3722
  · have he : independentCachedBranchMembers3724.filter (independentCachedEdge 3250)=independentCachedBranchMembers3723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3723
def independentCachedBranchMembers3725 : Finset ℕ := ([18,222,1650,1714,1748,1752,2618,2716,3162,3222,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3725 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3725 4 (fun x => (if x<2618 then (if x<1714 then (if x<222 then 0 else (if x<1650 then 0 else 1)) else (if x<1748 then 2 else (if x<1752 then 1 else 2))) else (if x<3222 then (if x<2716 then 1 else (if x<3162 then 1 else 0)) else (if x<3226 then 0 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3726 : Finset ℕ := ([18,80,144,222,246,250,1626,1650,1686,1714,1748,1752,1776,2618,2680,2716,2740,2770,3162,3186,3222,3226,3250,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3726 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3726 1776 4
  · have he : independentCachedBranchMembers3726.erase 1776=independentCachedBranchMembers3724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3724
  · have he : independentCachedBranchMembers3726.filter (independentCachedEdge 1776)=independentCachedBranchMembers3725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3725
def independentCachedBranchMembers3727 : Finset ℕ := ([80,246,1626,1686,1714,1752,2680,2740,3186,3226,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3727 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3727 4 (fun x => (if x<2680 then (if x<1686 then (if x<246 then 0 else (if x<1626 then 0 else 1)) else (if x<1714 then 1 else (if x<1752 then 2 else 2))) else (if x<3226 then (if x<2740 then 1 else (if x<3186 then 1 else 0)) else (if x<3284 then 2 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3728 : Finset ℕ := ([18,80,144,222,246,250,1626,1650,1686,1690,1714,1748,1752,1776,2618,2680,2716,2740,2770,3162,3186,3222,3226,3250,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3728 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3728 1690 4
  · have he : independentCachedBranchMembers3728.erase 1690=independentCachedBranchMembers3726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3726
  · have he : independentCachedBranchMembers3728.filter (independentCachedEdge 1690)=independentCachedBranchMembers3727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3727
def independentCachedBranchMembers3729 : Finset ℕ := ([144,250,1690,1714,1752,1776,2618,2680,2716,2740,3162,3186,3222,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3729 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3729 4 (fun x => (if x<2680 then (if x<1714 then (if x<250 then 0 else (if x<1690 then 0 else 0)) else (if x<1776 then (if x<1752 then 1 else 1) else (if x<2618 then 0 else 2))) else (if x<3162 then (if x<2716 then 3 else (if x<2740 then 2 else 3)) else (if x<3222 then (if x<3186 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3730 : Finset ℕ := ([18,80,144,222,246,250,1626,1650,1686,1690,1714,1748,1752,1776,2618,2680,2716,2740,2770,3158,3162,3186,3222,3226,3250,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3730 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3730 3158 4
  · have he : independentCachedBranchMembers3730.erase 3158=independentCachedBranchMembers3728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3728
  · have he : independentCachedBranchMembers3730.filter (independentCachedEdge 3158)=independentCachedBranchMembers3729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3729
def independentCachedBranchMembers3731 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1652,1686,1690,1714,1720,1746,1748,1752,1776,2618,2620,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3731 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3731 2620 5
  · have he : independentCachedBranchMembers3731.erase 2620=independentCachedBranchMembers3719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3719
  · have he : independentCachedBranchMembers3731.filter (independentCachedEdge 2620)=independentCachedBranchMembers3730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3730
def independentCachedBranchMembers3732 : Finset ℕ := ([18,80,246,250,1628,1650,1686,1690,1720,1748,1752,2646,2650,2680,2738,2770,2800,3130,3158,3162,3188,3192,3228,3250,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3732 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3732 5 (fun x => (if x<2680 then (if x<1686 then (if x<250 then (if x<80 then 0 else (if x<246 then 1 else 0)) else (if x<1628 then 1 else (if x<1650 then 2 else 0))) else (if x<1748 then (if x<1690 then 0 else (if x<1720 then 2 else 3)) else (if x<2646 then (if x<1752 then 3 else 1) else (if x<2650 then 0 else 1)))) else (if x<3162 then (if x<2800 then (if x<2738 then 4 else (if x<2770 then 0 else 4)) else (if x<3130 then 1 else (if x<3158 then 3 else 3))) else (if x<3228 then (if x<3188 then 2 else (if x<3192 then 2 else 1)) else (if x<3282 then (if x<3250 then 2 else 2) else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3733 : Finset ℕ := ([18,80,246,250,3130,3158,3162,3188,3192,3228,3250,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3733 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3733 4 (fun x => (if x<3162 then (if x<250 then (if x<80 then 0 else (if x<246 then 1 else 0)) else (if x<3130 then 1 else (if x<3158 then 2 else 0))) else (if x<3228 then (if x<3188 then 1 else (if x<3192 then 2 else 3)) else (if x<3282 then (if x<3250 then 2 else 0) else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3734 : Finset ℕ := ([18,80,246,250,1628,1650,1686,1690,1720,1748,1752,2646,2650,2680,2716,2738,2770,2800,3130,3158,3162,3188,3192,3228,3250,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3734 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3734 2716 4
  · have he : independentCachedBranchMembers3734.erase 2716=independentCachedBranchMembers3732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3732
  · have he : independentCachedBranchMembers3734.filter (independentCachedEdge 2716)=independentCachedBranchMembers3733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3733
def independentCachedBranchMembers3735 : Finset ℕ := ([80,246,1628,1686,1752,2650,2680,2738,3130,3158,3188,3228,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3735 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3735 4 (fun x => (if x<2738 then (if x<1686 then (if x<246 then 0 else (if x<1628 then 0 else 1)) else (if x<2650 then (if x<1752 then 1 else 2) else (if x<2680 then 2 else 1))) else (if x<3188 then (if x<3130 then 1 else (if x<3158 then 3 else 0)) else (if x<3282 then (if x<3228 then 3 else 3) else (if x<3312 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3736 : Finset ℕ := ([18,80,246,250,1628,1650,1686,1690,1720,1748,1752,2618,2646,2650,2680,2716,2738,2770,2800,3130,3158,3162,3188,3192,3228,3250,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3736 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3736 2618 4
  · have he : independentCachedBranchMembers3736.erase 2618=independentCachedBranchMembers3734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3734
  · have he : independentCachedBranchMembers3736.filter (independentCachedEdge 2618)=independentCachedBranchMembers3735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3735
def independentCachedBranchMembers3737 : Finset ℕ := ([80,250,1628,1690,1720,1748,2680,2770,2800,3130,3158,3188,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3737 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3737 4 (fun x => (if x<2680 then (if x<1690 then (if x<250 then 0 else (if x<1628 then 0 else 1)) else (if x<1720 then 1 else (if x<1748 then 2 else 2))) else (if x<3130 then (if x<2770 then 0 else (if x<2800 then 0 else 2)) else (if x<3188 then (if x<3158 then 3 else 3) else (if x<3250 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3738 : Finset ℕ := ([80,250,3130,3158,3188,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3738 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3738 3 (fun x => (if x<3158 then (if x<250 then 0 else (if x<3130 then 0 else 1)) else (if x<3188 then 1 else (if x<3250 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3739 : Finset ℕ := ([80,250,1628,1690,1720,1748,2680,2716,2770,2800,3130,3158,3188,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3739 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3739 2716 3
  · have he : independentCachedBranchMembers3739.erase 2716=independentCachedBranchMembers3737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3737
  · have he : independentCachedBranchMembers3739.filter (independentCachedEdge 2716)=independentCachedBranchMembers3738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3738
def independentCachedBranchMembers3740 : Finset ℕ := ([1720,1748,2680,2770,3188,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3740 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3740 3 (fun x => (if x<2770 then (if x<1748 then 0 else (if x<2680 then 0 else 1)) else (if x<3188 then 1 else (if x<3250 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3741 : Finset ℕ := ([80,250,1628,1690,1720,1748,2650,2680,2716,2770,2800,3130,3158,3188,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3741 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3741 2650 3
  · have he : independentCachedBranchMembers3741.erase 2650=independentCachedBranchMembers3739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3739
  · have he : independentCachedBranchMembers3741.filter (independentCachedEdge 2650)=independentCachedBranchMembers3740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3740
def independentCachedBranchMembers3742 : Finset ℕ := ([18,80,246,250,1628,1650,1686,1690,1720,1748,1752,2618,2646,2650,2680,2716,2738,2770,2800,3126,3130,3158,3162,3188,3192,3228,3250,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3742 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3742 3126 4
  · have he : independentCachedBranchMembers3742.erase 3126=independentCachedBranchMembers3736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3736
  · have he : independentCachedBranchMembers3742.filter (independentCachedEdge 3126)=independentCachedBranchMembers3741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3741
def independentCachedBranchMembers3743 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1652,1686,1690,1692,1714,1720,1746,1748,1752,1776,2618,2620,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3743 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3743 1692 5
  · have he : independentCachedBranchMembers3743.erase 1692=independentCachedBranchMembers3731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3731
  · have he : independentCachedBranchMembers3743.filter (independentCachedEdge 1692)=independentCachedBranchMembers3742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3742
end EntropyDesigns.QuadraticRefinement
