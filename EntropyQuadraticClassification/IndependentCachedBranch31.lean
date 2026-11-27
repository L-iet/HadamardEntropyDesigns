/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch30
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3776 : Finset ℕ := ([80,144,222,250,1590,1626,1628,1690,1692,1720,1746,1748,1776,2618,2620,2646,2674,2710,2738,2740,2776,3126,3162,3164,3192,3226,3228,3256,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3776 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3776 3164 4
  · have he : independentCachedBranchMembers3776.erase 3164=independentCachedBranchMembers3774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3774
  · have he : independentCachedBranchMembers3776.filter (independentCachedEdge 3164)=independentCachedBranchMembers3775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3775
def independentCachedBranchMembers3777 : Finset ℕ := ([18,80,144,222,246,250,1590,1594,1622,1626,1628,1650,1652,1686,1690,1692,1714,1720,1746,1748,1752,1776,2614,2618,2620,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3777 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3777 2614 5
  · have he : independentCachedBranchMembers3777.erase 2614=independentCachedBranchMembers3771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3771
  · have he : independentCachedBranchMembers3777.filter (independentCachedEdge 2614)=independentCachedBranchMembers3776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3776
def independentCachedBranchMembers3778 : Finset ℕ := ([80,144,246,250,1590,1594,1628,1652,1692,1720,1746,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3158,3186,3226,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3778 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3778 5 (fun x => (if x<2650 then (if x<1628 then (if x<250 then (if x<144 then 0 else (if x<246 then 1 else 0)) else (if x<1590 then 1 else (if x<1594 then 2 else 3))) else (if x<1720 then (if x<1652 then 2 else (if x<1692 then 0 else 3)) else (if x<2620 then (if x<1746 then 1 else 0) else (if x<2646 then 2 else 0)))) else (if x<2800 then (if x<2714 then (if x<2674 then 4 else (if x<2710 then 3 else 4)) else (if x<2772 then (if x<2738 then 1 else 2) else (if x<2776 then 3 else 2))) else (if x<3226 then (if x<3158 then 0 else (if x<3186 then 4 else 0)) else (if x<3284 then (if x<3250 then 4 else 1) else (if x<3288 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3779 : Finset ℕ := ([246,250,1590,1594,1652,1720,2620,2674,2738,2800,3186,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3779 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3779 4 (fun x => (if x<2620 then (if x<1594 then (if x<250 then 0 else (if x<1590 then 1 else 0)) else (if x<1652 then 1 else (if x<1720 then 2 else 2))) else (if x<2800 then (if x<2674 then 2 else (if x<2738 then 0 else 1)) else (if x<3186 then 2 else (if x<3250 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3780 : Finset ℕ := ([80,144,222,246,250,1590,1594,1628,1652,1692,1720,1746,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3158,3186,3226,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3780 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3780 222 4
  · have he : independentCachedBranchMembers3780.erase 222=independentCachedBranchMembers3778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3778
  · have he : independentCachedBranchMembers3780.filter (independentCachedEdge 222)=independentCachedBranchMembers3779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3779
def independentCachedBranchMembers3781 : Finset ℕ := ([80,144,1628,1652,1692,1720,2620,2772,2776,2800,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3781 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3781 4 (fun x => (if x<2620 then (if x<1652 then (if x<144 then 0 else (if x<1628 then 1 else 0)) else (if x<1692 then 2 else (if x<1720 then 1 else 2))) else (if x<2800 then (if x<2772 then 2 else (if x<2776 then 0 else 1)) else (if x<3284 then 2 else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3782 : Finset ℕ := ([18,80,144,222,246,250,1590,1594,1628,1652,1692,1720,1746,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3158,3186,3226,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3782 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3782 18 4
  · have he : independentCachedBranchMembers3782.erase 18=independentCachedBranchMembers3780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3780
  · have he : independentCachedBranchMembers3782.filter (independentCachedEdge 18)=independentCachedBranchMembers3781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3781
def independentCachedBranchMembers3783 : Finset ℕ := ([222,1590,1594,1628,1692,2620,2646,2650,2710,2714,2800,3186,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3783 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3783 4 (fun x => (if x<2650 then (if x<1628 then (if x<1590 then 0 else (if x<1594 then 1 else 2)) else (if x<2620 then (if x<1692 then 0 else 1) else (if x<2646 then 1 else 0))) else (if x<3186 then (if x<2714 then (if x<2710 then 2 else 1) else (if x<2800 then 3 else 3)) else (if x<3284 then (if x<3250 then 2 else 3) else (if x<3288 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3784 : Finset ℕ := ([1628,1692,2620,2800,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3784 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3784 3 (fun x => (if x<2800 then (if x<1692 then 0 else (if x<2620 then 1 else 0)) else (if x<3284 then 2 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3785 : Finset ℕ := ([18,222,1590,1594,1628,1692,2620,2646,2650,2710,2714,2800,3186,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3785 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3785 18 3
  · have he : independentCachedBranchMembers3785.erase 18=independentCachedBranchMembers3783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3783
  · have he : independentCachedBranchMembers3785.filter (independentCachedEdge 18)=independentCachedBranchMembers3784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3784
def independentCachedBranchMembers3786 : Finset ℕ := ([18,80,144,222,246,250,1590,1594,1628,1652,1692,1720,1746,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3158,3186,3226,3250,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3786 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3786 3312 4
  · have he : independentCachedBranchMembers3786.erase 3312=independentCachedBranchMembers3782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3782
  · have he : independentCachedBranchMembers3786.filter (independentCachedEdge 3312)=independentCachedBranchMembers3785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3785
def independentCachedBranchMembers3787 : Finset ℕ := ([250,1594,1628,1652,1720,2620,2650,2674,2710,2776,2800,3158,3226,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3787 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3787 4 (fun x => (if x<2674 then (if x<1652 then (if x<1594 then 0 else (if x<1628 then 0 else 1)) else (if x<2620 then (if x<1720 then 2 else 1) else (if x<2650 then 1 else 0))) else (if x<3158 then (if x<2776 then (if x<2710 then 2 else 3) else (if x<2800 then 1 else 3)) else (if x<3250 then (if x<3226 then 2 else 0) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3788 : Finset ℕ := ([1594,1720,2620,2710,3226,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3788 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3788 3 (fun x => (if x<2710 then (if x<1720 then 0 else (if x<2620 then 1 else 0)) else (if x<3226 then 2 else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3789 : Finset ℕ := ([80,250,1594,1628,1652,1720,2620,2650,2674,2710,2776,2800,3158,3226,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3789 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3789 80 3
  · have he : independentCachedBranchMembers3789.erase 80=independentCachedBranchMembers3787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3787
  · have he : independentCachedBranchMembers3789.filter (independentCachedEdge 80)=independentCachedBranchMembers3788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3788
def independentCachedBranchMembers3790 : Finset ℕ := ([18,80,144,222,246,250,1590,1594,1628,1652,1692,1720,1746,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3158,3186,3222,3226,3250,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3790 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3790 3222 4
  · have he : independentCachedBranchMembers3790.erase 3222=independentCachedBranchMembers3786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3786
  · have he : independentCachedBranchMembers3790.filter (independentCachedEdge 3222)=independentCachedBranchMembers3789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3789
def independentCachedBranchMembers3791 : Finset ℕ := ([246,1590,1652,1692,1720,2620,2650,2710,2738,2772,2800,3158,3186,3226,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3791 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3791 4 (fun x => (if x<2710 then (if x<1692 then (if x<1590 then 0 else (if x<1652 then 0 else 1)) else (if x<2620 then (if x<1720 then 1 else 2) else (if x<2650 then 1 else 3))) else (if x<3158 then (if x<2772 then (if x<2738 then 0 else 2) else (if x<2800 then 1 else 3)) else (if x<3226 then (if x<3186 then 0 else 3) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3792 : Finset ℕ := ([1590,1652,2620,2650,3158,3186] : List ℕ).toFinset
theorem independentCachedBranchBound3792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3792 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3792 3 (fun x => (if x<2650 then (if x<1652 then 0 else (if x<2620 then 1 else 0)) else (if x<3158 then 2 else (if x<3186 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3793 : Finset ℕ := ([144,246,1590,1652,1692,1720,2620,2650,2710,2738,2772,2800,3158,3186,3226,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3793 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3793 144 3
  · have he : independentCachedBranchMembers3793.erase 144=independentCachedBranchMembers3791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3791
  · have he : independentCachedBranchMembers3793.filter (independentCachedEdge 144)=independentCachedBranchMembers3792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3792
def independentCachedBranchMembers3794 : Finset ℕ := ([18,80,144,222,246,250,1590,1594,1628,1652,1692,1720,1746,2620,2646,2650,2674,2710,2714,2738,2772,2776,2800,3158,3162,3186,3222,3226,3250,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3794 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3794 3162 4
  · have he : independentCachedBranchMembers3794.erase 3162=independentCachedBranchMembers3790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3790
  · have he : independentCachedBranchMembers3794.filter (independentCachedEdge 3162)=independentCachedBranchMembers3793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3793
def independentCachedBranchMembers3795 : Finset ℕ := ([18,80,144,222,246,250,1590,1594,1596,1622,1626,1628,1650,1652,1686,1690,1692,1714,1720,1746,1748,1752,1776,2614,2618,2620,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3795 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3795 1596 5
  · have he : independentCachedBranchMembers3795.erase 1596=independentCachedBranchMembers3777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3777
  · have he : independentCachedBranchMembers3795.filter (independentCachedEdge 1596)=independentCachedBranchMembers3794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3794
def independentCachedBranchMembers3796 : Finset ℕ := ([18,222,246,250,1590,1622,1626,1650,1686,1690,1714,1746,2614,2618,2646,2650,2674,2710,2714,2738,2770,3102,3130,3158,3186,3222,3226,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3796 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3796 5 (fun x => (if x<2646 then (if x<1650 then (if x<250 then (if x<222 then 0 else (if x<246 then 0 else 1)) else (if x<1622 then (if x<1590 then 2 else 1) else (if x<1626 then 0 else 2))) else (if x<1714 then (if x<1686 then 3 else (if x<1690 then 3 else 0)) else (if x<2614 then (if x<1746 then 2 else 1) else (if x<2618 then 3 else 2)))) else (if x<3102 then (if x<2710 then (if x<2650 then 1 else (if x<2674 then 0 else 4)) else (if x<2738 then (if x<2714 then 0 else 4) else (if x<2770 then 1 else 2))) else (if x<3222 then (if x<3158 then (if x<3130 then 0 else 4) else (if x<3186 then 3 else 1)) else (if x<3250 then (if x<3226 then 1 else 2) else (if x<3282 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3797 : Finset ℕ := ([246,1590,1626,1686,1714,2614,2650,2710,2738,3102,3130,3158,3186,3226,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3797 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3797 4 (fun x => (if x<2710 then (if x<1686 then (if x<1590 then 0 else (if x<1626 then 0 else 1)) else (if x<2614 then (if x<1714 then 1 else 2) else (if x<2650 then 2 else 3))) else (if x<3158 then (if x<3102 then (if x<2738 then 0 else 3) else (if x<3130 then 1 else 2)) else (if x<3226 then (if x<3186 then 0 else 3) else (if x<3282 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3798 : Finset ℕ := ([18,222,246,250,1590,1622,1626,1650,1686,1690,1714,1746,2614,2618,2646,2650,2674,2710,2714,2738,2770,3102,3130,3158,3162,3186,3222,3226,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3798 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3798 3162 4
  · have he : independentCachedBranchMembers3798.erase 3162=independentCachedBranchMembers3796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3796
  · have he : independentCachedBranchMembers3798.filter (independentCachedEdge 3162)=independentCachedBranchMembers3797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3797
def independentCachedBranchMembers3799 : Finset ℕ := ([222,246,1590,1626,1650,1690,1714,2618,2646,2710,2770,3130,3158,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3799 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3799 4 (fun x => (if x<2618 then (if x<1626 then (if x<246 then 0 else (if x<1590 then 1 else 1)) else (if x<1690 then (if x<1650 then 0 else 2) else (if x<1714 then 2 else 3))) else (if x<3130 then (if x<2710 then (if x<2646 then 2 else 0) else (if x<2770 then 1 else 2)) else (if x<3222 then (if x<3158 then 3 else 1) else (if x<3282 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3800 : Finset ℕ := ([18,222,246,250,1590,1594,1622,1626,1650,1686,1690,1714,1746,2614,2618,2646,2650,2674,2710,2714,2738,2770,3102,3130,3158,3162,3186,3222,3226,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3800 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3800 1594 4
  · have he : independentCachedBranchMembers3800.erase 1594=independentCachedBranchMembers3798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3798
  · have he : independentCachedBranchMembers3800.filter (independentCachedEdge 1594)=independentCachedBranchMembers3799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3799
def independentCachedBranchMembers3801 : Finset ℕ := ([222,250,1590,1626,1690,1746,2614,2650,2714,2770,3102,3130,3158,3186,3222,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3801 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3801 4 (fun x => (if x<2714 then (if x<1690 then (if x<1590 then (if x<250 then 0 else 1) else (if x<1626 then 2 else 0)) else (if x<2614 then (if x<1746 then 1 else 2) else (if x<2650 then 3 else 1))) else (if x<3158 then (if x<3102 then (if x<2770 then 0 else 3) else (if x<3130 then 0 else 1)) else (if x<3222 then (if x<3186 then 2 else 3) else (if x<3250 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3802 : Finset ℕ := ([18,222,246,250,1590,1594,1622,1626,1650,1686,1690,1714,1746,2614,2618,2646,2650,2674,2710,2714,2738,2770,3102,3126,3130,3158,3162,3186,3222,3226,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3802 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3802 3126 4
  · have he : independentCachedBranchMembers3802.erase 3126=independentCachedBranchMembers3800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3800
  · have he : independentCachedBranchMembers3802.filter (independentCachedEdge 3126)=independentCachedBranchMembers3801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3801
def independentCachedBranchMembers3803 : Finset ℕ := ([18,80,144,222,246,250,252,1590,1594,1596,1622,1626,1628,1650,1652,1686,1690,1692,1714,1720,1746,1748,1752,1776,2614,2618,2620,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3126,3130,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3803 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3803 252 5
  · have he : independentCachedBranchMembers3803.erase 252=independentCachedBranchMembers3795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3795
  · have he : independentCachedBranchMembers3803.filter (independentCachedEdge 252)=independentCachedBranchMembers3802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3802
def independentCachedBranchMembers3804 : Finset ℕ := ([18,80,144,222,1626,1628,1686,1690,1746,1748,1752,2646,2650,2652,2710,2714,2716,2770,2772,2776,3102,3158,3162,3226,3228,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3804 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3804 5 (fun x => (if x<2710 then (if x<1690 then (if x<222 then (if x<80 then 0 else (if x<144 then 1 else 2)) else (if x<1628 then (if x<1626 then 0 else 0) else (if x<1686 then 1 else 0))) else (if x<1752 then (if x<1746 then 2 else (if x<1748 then 1 else 2)) else (if x<2650 then (if x<2646 then 3 else 0) else (if x<2652 then 1 else 3)))) else (if x<3158 then (if x<2770 then (if x<2714 then 2 else (if x<2716 then 0 else 4)) else (if x<2776 then (if x<2772 then 3 else 1) else (if x<3102 then 2 else 0))) else (if x<3228 then (if x<3162 then 1 else (if x<3226 then 3 else 4)) else (if x<3284 then (if x<3282 then 2 else 0) else (if x<3288 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3805 : Finset ℕ := ([144,1626,1628,1686,1746,1748,2646,2714,2716,2776,3158,3226,3228,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3805 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3805 4 (fun x => (if x<2714 then (if x<1686 then (if x<1626 then 0 else (if x<1628 then 1 else 2)) else (if x<1748 then (if x<1746 then 0 else 2) else (if x<2646 then 1 else 1))) else (if x<3158 then (if x<2716 then 0 else (if x<2776 then 3 else 1)) else (if x<3228 then (if x<3226 then 2 else 3) else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3806 : Finset ℕ := ([18,80,144,222,1622,1626,1628,1686,1690,1746,1748,1752,2646,2650,2652,2710,2714,2716,2770,2772,2776,3102,3158,3162,3226,3228,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3806 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3806 1622 4
  · have he : independentCachedBranchMembers3806.erase 1622=independentCachedBranchMembers3804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3804
  · have he : independentCachedBranchMembers3806.filter (independentCachedEdge 1622)=independentCachedBranchMembers3805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3805
def independentCachedBranchMembers3807 : Finset ℕ := ([80,1626,1628,1686,1752,2650,2652,2710,2776,3102,3158,3226,3228,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3807 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3807 4 (fun x => (if x<2710 then (if x<1686 then (if x<1626 then 0 else (if x<1628 then 0 else 1)) else (if x<2650 then (if x<1752 then 1 else 2) else (if x<2652 then 2 else 0))) else (if x<3226 then (if x<3102 then (if x<2776 then 3 else 3) else (if x<3158 then 1 else 0)) else (if x<3282 then (if x<3228 then 2 else 3) else (if x<3284 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
