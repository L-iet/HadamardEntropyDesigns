/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch29
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3744 : Finset ℕ := ([80,144,222,246,1590,1626,1650,1690,1714,1720,1748,2646,2710,2740,2770,2776,2800,3130,3158,3188,3222,3228,3252,3282,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3744 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3744 5 (fun x => (if x<2740 then (if x<1650 then (if x<246 then (if x<144 then 0 else (if x<222 then 1 else 0)) else (if x<1590 then 1 else (if x<1626 then 2 else 0))) else (if x<1720 then (if x<1690 then 3 else (if x<1714 then 2 else 1)) else (if x<2646 then (if x<1748 then 3 else 0) else (if x<2710 then 0 else 1)))) else (if x<3188 then (if x<2800 then (if x<2770 then 4 else (if x<2776 then 4 else 0)) else (if x<3130 then 1 else (if x<3158 then 2 else 3))) else (if x<3252 then (if x<3222 then 2 else (if x<3228 then 2 else 3)) else (if x<3288 then (if x<3282 then 1 else 0) else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3745 : Finset ℕ := ([80,144,222,246,3130,3158,3188,3222,3228,3252,3282,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3745 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3745 4 (fun x => (if x<3188 then (if x<246 then (if x<144 then 0 else (if x<222 then 1 else 0)) else (if x<3130 then 1 else (if x<3158 then 2 else 0))) else (if x<3252 then (if x<3222 then 2 else (if x<3228 then 1 else 2)) else (if x<3288 then (if x<3282 then 3 else 2) else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3746 : Finset ℕ := ([80,144,222,246,1590,1626,1650,1690,1714,1720,1748,2618,2646,2710,2740,2770,2776,2800,3130,3158,3188,3222,3228,3252,3282,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3746 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3746 2618 4
  · have he : independentCachedBranchMembers3746.erase 2618=independentCachedBranchMembers3744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3744
  · have he : independentCachedBranchMembers3746.filter (independentCachedEdge 2618)=independentCachedBranchMembers3745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3745
def independentCachedBranchMembers3747 : Finset ℕ := ([80,246,1590,1626,1714,2710,2740,2776,3130,3158,3188,3228,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3747 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3747 4 (fun x => (if x<2776 then (if x<1626 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<2710 then (if x<1714 then 1 else 2) else (if x<2740 then 2 else 1))) else (if x<3188 then (if x<3130 then 1 else (if x<3158 then 3 else 0)) else (if x<3282 then (if x<3228 then 3 else 3) else (if x<3312 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3748 : Finset ℕ := ([80,144,222,246,1590,1626,1650,1690,1714,1720,1748,2618,2646,2710,2716,2740,2770,2776,2800,3130,3158,3188,3222,3228,3252,3282,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3748 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3748 2716 4
  · have he : independentCachedBranchMembers3748.erase 2716=independentCachedBranchMembers3746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3746
  · have he : independentCachedBranchMembers3748.filter (independentCachedEdge 2716)=independentCachedBranchMembers3747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3747
def independentCachedBranchMembers3749 : Finset ℕ := ([144,246,1590,1650,1690,1720,2710,2740,2770,2800,3158,3188,3228,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3749 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3749 4 (fun x => (if x<2740 then (if x<1650 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1720 then (if x<1690 then 2 else 1) else (if x<2710 then 2 else 0))) else (if x<3158 then (if x<2770 then 3 else (if x<2800 then 3 else 0)) else (if x<3228 then (if x<3188 then 2 else 1) else (if x<3288 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3750 : Finset ℕ := ([144,246,3158,3188,3228,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3750 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3750 3 (fun x => (if x<3188 then (if x<246 then 0 else (if x<3158 then 0 else 1)) else (if x<3228 then 2 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3751 : Finset ℕ := ([144,246,1590,1650,1690,1720,2618,2710,2740,2770,2800,3158,3188,3228,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3751 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3751 2618 3
  · have he : independentCachedBranchMembers3751.erase 2618=independentCachedBranchMembers3749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3749
  · have he : independentCachedBranchMembers3751.filter (independentCachedEdge 2618)=independentCachedBranchMembers3750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3750
def independentCachedBranchMembers3752 : Finset ℕ := ([80,144,222,246,1590,1626,1650,1690,1714,1720,1748,2618,2646,2710,2716,2740,2770,2776,2800,3130,3158,3164,3188,3222,3228,3252,3282,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3752 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3752 3164 4
  · have he : independentCachedBranchMembers3752.erase 3164=independentCachedBranchMembers3748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3748
  · have he : independentCachedBranchMembers3752.filter (independentCachedEdge 3164)=independentCachedBranchMembers3751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3751
def independentCachedBranchMembers3753 : Finset ℕ := ([18,80,144,222,246,250,1590,1594,1626,1628,1650,1652,1686,1690,1692,1714,1720,1746,1748,1752,1776,2618,2620,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3753 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3753 1594 5
  · have he : independentCachedBranchMembers3753.erase 1594=independentCachedBranchMembers3743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3743
  · have he : independentCachedBranchMembers3753.filter (independentCachedEdge 1594)=independentCachedBranchMembers3752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3752
def independentCachedBranchMembers3754 : Finset ℕ := ([144,250,1590,1626,1628,1650,1652,1686,1720,1746,1748,2620,2646,2680,2714,2738,2740,2776,2800,3130,3158,3192,3228,3250,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3754 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3754 5 (fun x => (if x<2680 then (if x<1652 then (if x<1626 then (if x<250 then 0 else (if x<1590 then 0 else 1)) else (if x<1628 then 1 else (if x<1650 then 2 else 2))) else (if x<1746 then (if x<1686 then 3 else (if x<1720 then 2 else 0)) else (if x<2620 then (if x<1748 then 0 else 1) else (if x<2646 then 3 else 1)))) else (if x<3158 then (if x<2740 then (if x<2714 then 2 else (if x<2738 then 0 else 2)) else (if x<2800 then (if x<2776 then 1 else 1) else (if x<3130 then 0 else 4))) else (if x<3250 then (if x<3192 then 4 else (if x<3228 then 3 else 4)) else (if x<3288 then (if x<3252 then 0 else 3) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3755 : Finset ℕ := ([1590,1628,1650,1748,2646,2680,2714,2740,3130,3228,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3755 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3755 4 (fun x => (if x<2714 then (if x<1748 then (if x<1628 then 0 else (if x<1650 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 0 else 2))) else (if x<3228 then (if x<2740 then 2 else (if x<3130 then 2 else 1)) else (if x<3250 then 1 else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3756 : Finset ℕ := ([1590,1628,2680,2740,3130,3228] : List ℕ).toFinset
theorem independentCachedBranchBound3756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3756 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3756 3 (fun x => (if x<2740 then (if x<1628 then 0 else (if x<2680 then 0 else 1)) else (if x<3130 then 1 else (if x<3228 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3757 : Finset ℕ := ([1590,1628,1650,1748,2646,2680,2714,2740,2800,3130,3228,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3757 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3757 2800 3
  · have he : independentCachedBranchMembers3757.erase 2800=independentCachedBranchMembers3755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3755
  · have he : independentCachedBranchMembers3757.filter (independentCachedEdge 2800)=independentCachedBranchMembers3756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3756
def independentCachedBranchMembers3758 : Finset ℕ := ([1650,1748,2680,2740,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3758 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3758 3 (fun x => (if x<2740 then (if x<1748 then 0 else (if x<2680 then 0 else 1)) else (if x<3250 then 1 else (if x<3288 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3759 : Finset ℕ := ([1590,1628,1650,1748,2620,2646,2680,2714,2740,2800,3130,3228,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3759 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3759 2620 3
  · have he : independentCachedBranchMembers3759.erase 2620=independentCachedBranchMembers3757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3757
  · have he : independentCachedBranchMembers3759.filter (independentCachedEdge 2620)=independentCachedBranchMembers3758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3758
def independentCachedBranchMembers3760 : Finset ℕ := ([144,250,1590,1626,1628,1650,1652,1686,1720,1746,1748,2620,2646,2680,2714,2738,2740,2776,2800,3130,3158,3192,3226,3228,3250,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3760 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3760 3226 4
  · have he : independentCachedBranchMembers3760.erase 3226=independentCachedBranchMembers3754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3754
  · have he : independentCachedBranchMembers3760.filter (independentCachedEdge 3226)=independentCachedBranchMembers3759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3759
def independentCachedBranchMembers3761 : Finset ℕ := ([250,1590,1626,1652,1746,2620,2714,2740,2776,3130,3158,3192,3228,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3761 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3761 4 (fun x => (if x<2740 then (if x<1652 then (if x<1590 then 0 else (if x<1626 then 1 else 0)) else (if x<2620 then (if x<1746 then 2 else 1) else (if x<2714 then 1 else 0))) else (if x<3192 then (if x<3130 then (if x<2776 then 2 else 1) else (if x<3158 then 0 else 3)) else (if x<3250 then (if x<3228 then 3 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3762 : Finset ℕ := ([144,250,1590,1626,1628,1650,1652,1686,1720,1746,1748,2620,2646,2680,2714,2716,2738,2740,2776,2800,3130,3158,3192,3226,3228,3250,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3762 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3762 2716 4
  · have he : independentCachedBranchMembers3762.erase 2716=independentCachedBranchMembers3760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3760
  · have he : independentCachedBranchMembers3762.filter (independentCachedEdge 2716)=independentCachedBranchMembers3761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3761
def independentCachedBranchMembers3763 : Finset ℕ := ([144,1628,1652,1686,1746,2620,2680,2714,2738,3130,3158,3228,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3763 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3763 4 (fun x => (if x<2714 then (if x<1686 then (if x<1628 then 0 else (if x<1652 then 1 else 2)) else (if x<2620 then (if x<1746 then 0 else 1) else (if x<2680 then 1 else 2))) else (if x<3228 then (if x<3130 then (if x<2738 then 0 else 1) else (if x<3158 then 3 else 3)) else (if x<3288 then (if x<3252 then 0 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3764 : Finset ℕ := ([144,250,1590,1626,1628,1650,1652,1686,1720,1746,1748,2618,2620,2646,2680,2714,2716,2738,2740,2776,2800,3130,3158,3192,3226,3228,3250,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3764 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3764 2618 4
  · have he : independentCachedBranchMembers3764.erase 2618=independentCachedBranchMembers3762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3762
  · have he : independentCachedBranchMembers3764.filter (independentCachedEdge 2618)=independentCachedBranchMembers3763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3763
def independentCachedBranchMembers3765 : Finset ℕ := ([18,80,144,222,246,250,1590,1594,1622,1626,1628,1650,1652,1686,1690,1692,1714,1720,1746,1748,1752,1776,2618,2620,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3765 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3765 1622 5
  · have he : independentCachedBranchMembers3765.erase 1622=independentCachedBranchMembers3753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3753
  · have he : independentCachedBranchMembers3765.filter (independentCachedEdge 1622)=independentCachedBranchMembers3764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3764
def independentCachedBranchMembers3766 : Finset ℕ := ([18,144,246,250,1590,1628,1650,1686,1690,1720,1746,1776,2620,2646,2650,2680,2716,2738,2772,2776,3130,3164,3186,3222,3226,3252,3256,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3766 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3766 5 (fun x => (if x<2650 then (if x<1686 then (if x<250 then (if x<144 then 0 else (if x<246 then 1 else 0)) else (if x<1628 then (if x<1590 then 1 else 0) else (if x<1650 then 2 else 2))) else (if x<1746 then (if x<1690 then 2 else (if x<1720 then 1 else 2)) else (if x<2620 then (if x<1776 then 0 else 1) else (if x<2646 then 3 else 0)))) else (if x<3164 then (if x<2738 then (if x<2680 then 3 else (if x<2716 then 2 else 2)) else (if x<2776 then (if x<2772 then 0 else 3) else (if x<3130 then 1 else 3))) else (if x<3252 then (if x<3222 then (if x<3186 then 3 else 0) else (if x<3226 then 0 else 4)) else (if x<3282 then (if x<3256 then 3 else 1) else (if x<3312 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3767 : Finset ℕ := ([144,246,1590,1650,1690,1720,2646,2716,2776,3130,3164,3222,3252,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3767 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3767 4 (fun x => (if x<2716 then (if x<1650 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1720 then (if x<1690 then 2 else 1) else (if x<2646 then 2 else 2))) else (if x<3222 then (if x<3130 then (if x<2776 then 2 else 1) else (if x<3164 then 3 else 3)) else (if x<3282 then (if x<3252 then 0 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3768 : Finset ℕ := ([18,144,246,250,1590,1594,1628,1650,1686,1690,1720,1746,1776,2620,2646,2650,2680,2716,2738,2772,2776,3130,3164,3186,3222,3226,3252,3256,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3768 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3768 1594 4
  · have he : independentCachedBranchMembers3768.erase 1594=independentCachedBranchMembers3766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3766
  · have he : independentCachedBranchMembers3768.filter (independentCachedEdge 1594)=independentCachedBranchMembers3767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3767
def independentCachedBranchMembers3769 : Finset ℕ := ([144,250,1590,1628,1690,1720,1746,1776,2650,2680,2716,2772,3130,3186,3222,3252] : List ℕ).toFinset
theorem independentCachedBranchBound3769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3769 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3769 4 (fun x => (if x<2650 then (if x<1690 then (if x<1590 then (if x<250 then 0 else 0) else (if x<1628 then 1 else 1)) else (if x<1746 then (if x<1720 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3130 then (if x<2716 then (if x<2680 then 2 else 3) else (if x<2772 then 2 else 3)) else (if x<3222 then (if x<3186 then 3 else 2) else (if x<3252 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3770 : Finset ℕ := ([18,144,246,250,1590,1594,1628,1650,1686,1690,1720,1746,1776,2620,2646,2650,2680,2716,2738,2772,2776,3126,3130,3164,3186,3222,3226,3252,3256,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3770 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3770 3126 4
  · have he : independentCachedBranchMembers3770.erase 3126=independentCachedBranchMembers3768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3768
  · have he : independentCachedBranchMembers3770.filter (independentCachedEdge 3126)=independentCachedBranchMembers3769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3769
def independentCachedBranchMembers3771 : Finset ℕ := ([18,80,144,222,246,250,1590,1594,1622,1626,1628,1650,1652,1686,1690,1692,1714,1720,1746,1748,1752,1776,2618,2620,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3771 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3771 2652 5
  · have he : independentCachedBranchMembers3771.erase 2652=independentCachedBranchMembers3765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3765
  · have he : independentCachedBranchMembers3771.filter (independentCachedEdge 2652)=independentCachedBranchMembers3770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3770
def independentCachedBranchMembers3772 : Finset ℕ := ([80,144,222,250,1590,1626,1628,1690,1720,1746,1748,1776,2618,2620,2646,2674,2710,2738,2740,2776,3126,3162,3192,3226,3228,3256,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3772 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3772 5 (fun x => (if x<2646 then (if x<1690 then (if x<250 then (if x<144 then 0 else (if x<222 then 1 else 0)) else (if x<1626 then (if x<1590 then 1 else 2) else (if x<1628 then 0 else 2))) else (if x<1748 then (if x<1720 then 1 else (if x<1746 then 2 else 2)) else (if x<2618 then (if x<1776 then 0 else 1) else (if x<2620 then 3 else 2)))) else (if x<3162 then (if x<2738 then (if x<2674 then 0 else (if x<2710 then 4 else 3)) else (if x<2776 then (if x<2740 then 1 else 4) else (if x<3126 then 0 else 3))) else (if x<3256 then (if x<3226 then (if x<3192 then 4 else 3) else (if x<3228 then 3 else 4)) else (if x<3284 then (if x<3282 then 1 else 0) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3773 : Finset ℕ := ([80,250,1628,1690,1720,1748,2618,2646,2738,3126,3162,3192,3228,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3773 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3773 4 (fun x => (if x<2646 then (if x<1690 then (if x<250 then 0 else (if x<1628 then 0 else 1)) else (if x<1748 then (if x<1720 then 1 else 2) else (if x<2618 then 2 else 2))) else (if x<3192 then (if x<3126 then (if x<2738 then 2 else 1) else (if x<3162 then 3 else 0)) else (if x<3282 then (if x<3228 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3774 : Finset ℕ := ([80,144,222,250,1590,1626,1628,1690,1692,1720,1746,1748,1776,2618,2620,2646,2674,2710,2738,2740,2776,3126,3162,3192,3226,3228,3256,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3774 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3774 1692 4
  · have he : independentCachedBranchMembers3774.erase 1692=independentCachedBranchMembers3772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3772
  · have he : independentCachedBranchMembers3774.filter (independentCachedEdge 1692)=independentCachedBranchMembers3773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3773
def independentCachedBranchMembers3775 : Finset ℕ := ([144,250,1590,1628,1690,1720,1746,1776,2618,2674,2710,2740,3162,3192,3228,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3775 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3775 4 (fun x => (if x<2618 then (if x<1690 then (if x<1590 then (if x<250 then 0 else 0) else (if x<1628 then 1 else 1)) else (if x<1746 then (if x<1720 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3162 then (if x<2710 then (if x<2674 then 2 else 3) else (if x<2740 then 2 else 3)) else (if x<3228 then (if x<3192 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
