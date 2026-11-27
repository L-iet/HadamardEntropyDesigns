/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch6
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers896 : Finset ℕ := ([72,1626,1642,1652,1678,1692,1708,1714,2638,2652,2668,2674,2710,2730,2740,3150,3164,3180,3186,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers896 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers896 1678 4
  · have he : independentCachedBranchMembers896.erase 1678=independentCachedBranchMembers894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound894
  · have he : independentCachedBranchMembers896.filter (independentCachedEdge 1678)=independentCachedBranchMembers895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound895
def independentCachedBranchMembers897 : Finset ℕ := ([72,132,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers897 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers897 1650 5
  · have he : independentCachedBranchMembers897.erase 1650=independentCachedBranchMembers893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound893
  · have he : independentCachedBranchMembers897.filter (independentCachedEdge 1650)=independentCachedBranchMembers896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound896
def independentCachedBranchMembers898 : Finset ℕ := ([132,1626,1628,1642,1644,1678,1714,1720,2638,2674,2680,2710,2716,2730,2732,3150,3186,3192,3226,3228,3238,3244] : List ℕ).toFinset
theorem independentCachedBranchBound898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers898 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers898 5 (fun x => (if x<2710 then (if x<1678 then (if x<1628 then (if x<1626 then 0 else 0) else (if x<1642 then 1 else (if x<1644 then 1 else 2))) else (if x<2638 then (if x<1714 then 0 else (if x<1720 then 3 else 1)) else (if x<2674 then 1 else (if x<2680 then 0 else 1)))) else (if x<3186 then (if x<2730 then (if x<2716 then 2 else 1) else (if x<2732 then 1 else (if x<3150 then 2 else 3))) else (if x<3228 then (if x<3192 then 3 else (if x<3226 then 0 else 3)) else (if x<3238 then 4 else (if x<3244 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers899 : Finset ℕ := ([72,132,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers899 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers899 1614 5
  · have he : independentCachedBranchMembers899.erase 1614=independentCachedBranchMembers897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound897
  · have he : independentCachedBranchMembers899.filter (independentCachedEdge 1614)=independentCachedBranchMembers898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound898
def independentCachedBranchMembers900 : Finset ℕ := ([72,132,1626,1642,1644,1652,1678,1686,1702,1720,2650,2652,2668,2674,2702,2710,3150,3158,3192,3226,3228,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers900 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers900 5 (fun x => (if x<2668 then (if x<1678 then (if x<1642 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1644 then 1 else (if x<1652 then 2 else 1))) else (if x<1720 then (if x<1686 then 2 else (if x<1702 then 0 else 1)) else (if x<2650 then 1 else (if x<2652 then 3 else 4)))) else (if x<3192 then (if x<2710 then (if x<2674 then 3 else (if x<2702 then 4 else 3)) else (if x<3150 then 2 else (if x<3158 then 3 else 4))) else (if x<3244 then (if x<3226 then 0 else (if x<3228 then 2 else 4)) else (if x<3250 then 3 else (if x<3252 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers901 : Finset ℕ := ([72,1626,1642,1652,1678,2652,2668,2674,2710,3150,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers901 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers901 4 (fun x => (if x<2668 then (if x<1652 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1678 then 1 else (if x<2652 then 2 else 0))) else (if x<3150 then (if x<2674 then 1 else (if x<2710 then 1 else 2)) else (if x<3226 then 0 else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers902 : Finset ℕ := ([72,132,1626,1642,1644,1650,1652,1678,1686,1702,1720,2650,2652,2668,2674,2702,2710,3150,3158,3192,3226,3228,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers902 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers902 1650 4
  · have he : independentCachedBranchMembers902.erase 1650=independentCachedBranchMembers900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound900
  · have he : independentCachedBranchMembers902.filter (independentCachedEdge 1650)=independentCachedBranchMembers901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound901
def independentCachedBranchMembers903 : Finset ℕ := ([132,1626,1644,1652,1702,2652,2674,2702,2710,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers903 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers903 4 (fun x => (if x<2674 then (if x<1652 then (if x<1626 then 0 else (if x<1644 then 0 else 1)) else (if x<1702 then 2 else (if x<2652 then 1 else 1))) else (if x<3226 then (if x<2702 then 0 else (if x<2710 then 2 else 1)) else (if x<3244 then 2 else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers904 : Finset ℕ := ([72,132,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,2650,2652,2668,2674,2702,2710,3150,3158,3192,3226,3228,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers904 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers904 1628 4
  · have he : independentCachedBranchMembers904.erase 1628=independentCachedBranchMembers902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound902
  · have he : independentCachedBranchMembers904.filter (independentCachedEdge 1628)=independentCachedBranchMembers903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound903
def independentCachedBranchMembers905 : Finset ℕ := ([72,132,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,3150,3158,3164,3178,3180,3186,3192,3214,3226,3228,3238,3244,3250,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers905 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers905 3256 5
  · have he : independentCachedBranchMembers905.erase 3256=independentCachedBranchMembers899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound899
  · have he : independentCachedBranchMembers905.filter (independentCachedEdge 3256)=independentCachedBranchMembers904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound904
def independentCachedBranchMembers906 : Finset ℕ := ([72,132,1626,1642,1652,1686,1702,1708,1714,1720,2638,2650,2710,2716,2732,2738,3158,3164,3180,3186,3192,3214,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers906 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers906 5 (fun x => (if x<2710 then (if x<1702 then (if x<1642 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1652 then 1 else (if x<1686 then 1 else 0))) else (if x<1720 then (if x<1708 then 1 else (if x<1714 then 2 else 2)) else (if x<2638 then 1 else (if x<2650 then 3 else 4)))) else (if x<3180 then (if x<2738 then (if x<2716 then 3 else (if x<2732 then 4 else 3)) else (if x<3158 then 4 else (if x<3164 then 3 else 4))) else (if x<3214 then (if x<3186 then 2 else (if x<3192 then 2 else 0)) else (if x<3226 then 3 else (if x<3252 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers907 : Finset ℕ := ([72,1642,1686,1708,1720,2638,2650,2716,2738,3158,3180,3192] : List ℕ).toFinset
theorem independentCachedBranchBound907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers907 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers907 4 (fun x => (if x<2650 then (if x<1708 then (if x<1642 then 0 else (if x<1686 then 0 else 1)) else (if x<1720 then 1 else (if x<2638 then 2 else 0))) else (if x<3158 then (if x<2716 then 3 else (if x<2738 then 1 else 2)) else (if x<3180 then 3 else (if x<3192 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers908 : Finset ℕ := ([72,132,1626,1642,1652,1686,1692,1702,1708,1714,1720,2638,2650,2710,2716,2732,2738,3158,3164,3180,3186,3192,3214,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers908 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers908 1692 4
  · have he : independentCachedBranchMembers908.erase 1692=independentCachedBranchMembers906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound906
  · have he : independentCachedBranchMembers908.filter (independentCachedEdge 1692)=independentCachedBranchMembers907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound907
def independentCachedBranchMembers909 : Finset ℕ := ([132,1626,1642,1714,1720,2638,2710,2716,2732,3186,3192,3226] : List ℕ).toFinset
theorem independentCachedBranchBound909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers909 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers909 4 (fun x => (if x<2710 then (if x<1714 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then 1 else (if x<2638 then 2 else 1))) else (if x<3186 then (if x<2716 then 1 else (if x<2732 then 2 else 0)) else (if x<3192 then 0 else (if x<3226 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers910 : Finset ℕ := ([72,132,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,2638,2650,2710,2716,2732,2738,3158,3164,3180,3186,3192,3214,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers910 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers910 1614 4
  · have he : independentCachedBranchMembers910.erase 1614=independentCachedBranchMembers908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound908
  · have he : independentCachedBranchMembers910.filter (independentCachedEdge 1614)=independentCachedBranchMembers909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound909
def independentCachedBranchMembers911 : Finset ℕ := ([72,132,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers911 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers911 3188 5
  · have he : independentCachedBranchMembers911.erase 3188=independentCachedBranchMembers905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound905
  · have he : independentCachedBranchMembers911.filter (independentCachedEdge 3188)=independentCachedBranchMembers910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound910
def independentCachedBranchMembers912 : Finset ℕ := ([72,132,1628,1642,1702,1708,2650,2662,2668,2702,2710,2716,2730,2738,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers912 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers912 5 (fun x => (if x<2730 then (if x<2650 then (if x<1642 then (if x<132 then 0 else (if x<1628 then 0 else 1)) else (if x<1702 then 0 else (if x<1708 then 0 else 1))) else (if x<2702 then (if x<2662 then 0 else (if x<2668 then 2 else 1)) else (if x<2710 then 2 else (if x<2716 then 0 else 1)))) else (if x<3186 then (if x<3158 then (if x<2738 then 1 else (if x<3150 then 2 else 2)) else (if x<3164 then 3 else (if x<3178 then 4 else 3))) else (if x<3238 then (if x<3192 then 2 else (if x<3226 then 0 else 2)) else (if x<3244 then 2 else (if x<3252 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers913 : Finset ℕ := ([72,1642,1708,2668,2710,2730,3150,3164,3186,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers913 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers913 4 (fun x => (if x<3150 then (if x<2668 then (if x<1642 then 0 else (if x<1708 then 0 else 1)) else (if x<2710 then 0 else (if x<2730 then 2 else 1))) else (if x<3226 then (if x<3164 then 0 else (if x<3186 then 3 else 3)) else (if x<3238 then 2 else (if x<3252 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers914 : Finset ℕ := ([72,132,1628,1642,1650,1702,1708,2650,2662,2668,2702,2710,2716,2730,2738,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers914 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers914 1650 4
  · have he : independentCachedBranchMembers914.erase 1650=independentCachedBranchMembers912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound912
  · have he : independentCachedBranchMembers914.filter (independentCachedEdge 1650)=independentCachedBranchMembers913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound913
def independentCachedBranchMembers915 : Finset ℕ := ([132,1628,1642,2710,2716,2730,3150,3186,3192,3226,3238,3244] : List ℕ).toFinset
theorem independentCachedBranchBound915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers915 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers915 4 (fun x => (if x<3150 then (if x<2710 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<2716 then 0 else (if x<2730 then 1 else 1))) else (if x<3226 then (if x<3186 then 2 else (if x<3192 then 2 else 0)) else (if x<3238 then 2 else (if x<3244 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers916 : Finset ℕ := ([72,132,1614,1628,1642,1650,1702,1708,2650,2662,2668,2702,2710,2716,2730,2738,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers916 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers916 1614 4
  · have he : independentCachedBranchMembers916.erase 1614=independentCachedBranchMembers914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound914
  · have he : independentCachedBranchMembers916.filter (independentCachedEdge 1614)=independentCachedBranchMembers915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound915
def independentCachedBranchMembers917 : Finset ℕ := ([72,132,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,2638,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers917 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers917 2714 5
  · have he : independentCachedBranchMembers917.erase 2714=independentCachedBranchMembers911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound911
  · have he : independentCachedBranchMembers917.filter (independentCachedEdge 2714)=independentCachedBranchMembers916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound916
def independentCachedBranchMembers918 : Finset ℕ := ([72,132,1642,1692,1702,1714,2638,2650,2652,2662,2674,2710,2730,2732,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers918 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers918 5 (fun x => (if x<2730 then (if x<2638 then (if x<1692 then (if x<132 then 0 else (if x<1642 then 0 else 0)) else (if x<1702 then 1 else (if x<1714 then 0 else 1))) else (if x<2662 then (if x<2650 then 2 else (if x<2652 then 0 else 1)) else (if x<2674 then 3 else (if x<2710 then 1 else 0)))) else (if x<3214 then (if x<3178 then (if x<2732 then 2 else (if x<3158 then 3 else 2)) else (if x<3180 then 2 else (if x<3192 then 3 else 0))) else (if x<3238 then (if x<3226 then 2 else (if x<3228 then 4 else 3)) else (if x<3250 then 3 else (if x<3252 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers919 : Finset ℕ := ([72,1692,1702,2650,2652,2662,3158,3178,3180,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers919 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers919 4 (fun x => (if x<3158 then (if x<2650 then (if x<1692 then 0 else (if x<1702 then 1 else 0)) else (if x<2652 then 0 else (if x<2662 then 1 else 1))) else (if x<3214 then (if x<3178 then 2 else (if x<3180 then 2 else 3)) else (if x<3250 then 2 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers920 : Finset ℕ := ([72,132,1642,1678,1692,1702,1714,2638,2650,2652,2662,2674,2710,2730,2732,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers920 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers920 1678 4
  · have he : independentCachedBranchMembers920.erase 1678=independentCachedBranchMembers918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound918
  · have he : independentCachedBranchMembers920.filter (independentCachedEdge 1678)=independentCachedBranchMembers919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound919
def independentCachedBranchMembers921 : Finset ℕ := ([132,1642,1714,2650,2674,2730,3158,3180,3214,3228,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers921 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers921 4 (fun x => (if x<3158 then (if x<2650 then (if x<1642 then 0 else (if x<1714 then 0 else 1)) else (if x<2674 then 0 else (if x<2730 then 1 else 1))) else (if x<3228 then (if x<3180 then 2 else (if x<3214 then 2 else 2)) else (if x<3238 then 3 else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers922 : Finset ℕ := ([72,132,1642,1644,1678,1692,1702,1714,2638,2650,2652,2662,2674,2710,2730,2732,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers922 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers922 1644 4
  · have he : independentCachedBranchMembers922.erase 1644=independentCachedBranchMembers920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound920
  · have he : independentCachedBranchMembers922.filter (independentCachedEdge 1644)=independentCachedBranchMembers921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound921
def independentCachedBranchMembers923 : Finset ℕ := ([72,132,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers923 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers923 2646 5
  · have he : independentCachedBranchMembers923.erase 2646=independentCachedBranchMembers917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound917
  · have he : independentCachedBranchMembers923.filter (independentCachedEdge 2646)=independentCachedBranchMembers922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound922
def independentCachedBranchMembers924 : Finset ℕ := ([48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers924 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers924 192 6
  · have he : independentCachedBranchMembers924.erase 192=independentCachedBranchMembers862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound862
  · have he : independentCachedBranchMembers924.filter (independentCachedEdge 192)=independentCachedBranchMembers923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound923
def independentCachedBranchMembers925 : Finset ℕ := ([48,252,1596,1628,1642,1678,1702,1720,1738,1748,1776,2620,2638,2680,2716,2730,2740,2758,2776,2800,3118,3164,3188,3192,3214,3252,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers925 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers925 6 (fun x => (if x<2730 then (if x<1720 then (if x<1628 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1678 then (if x<1642 then 1 else 1) else (if x<1702 then 1 else 2))) else (if x<2620 then (if x<1748 then (if x<1738 then 1 else 2) else (if x<1776 then 2 else 0)) else (if x<2680 then (if x<2638 then 3 else 1) else (if x<2716 then 0 else 1)))) else (if x<3188 then (if x<2776 then (if x<2740 then 1 else (if x<2758 then 0 else 2)) else (if x<3118 then (if x<2800 then 2 else 3) else (if x<3164 then 3 else 4))) else (if x<3256 then (if x<3214 then (if x<3192 then 0 else 3) else (if x<3252 then 4 else 3)) else (if x<3284 then (if x<3274 then 0 else 5) else (if x<3298 then 5 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers926 : Finset ℕ := ([48,1596,1642,1678,2620,2638,2730,2740,2758,2776,3118,3164,3192,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers926 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers926 5 (fun x => (if x<2758 then (if x<2620 then (if x<1642 then (if x<1596 then 0 else 0) else (if x<1678 then 1 else 0)) else (if x<2730 then (if x<2638 then 2 else 1) else (if x<2740 then 1 else 3))) else (if x<3192 then (if x<3118 then (if x<2776 then 0 else 2) else (if x<3164 then 1 else 2)) else (if x<3274 then (if x<3256 then 0 else 2) else (if x<3284 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers927 : Finset ℕ := ([48,252,1596,1628,1642,1678,1702,1720,1738,1748,1776,2620,2638,2680,2716,2730,2740,2758,2776,2800,3118,3164,3188,3192,3214,3252,3256,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers927 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers927 3288 5
  · have he : independentCachedBranchMembers927.erase 3288=independentCachedBranchMembers925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound925
  · have he : independentCachedBranchMembers927.filter (independentCachedEdge 3288)=independentCachedBranchMembers926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound926
def independentCachedBranchMembers928 : Finset ℕ := ([252,1628,1642,1776,2716,2730,2740,2758,2776,2800,3192,3214,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers928 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers928 5 (fun x => (if x<2776 then (if x<2716 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1776 then 1 else 0)) else (if x<2740 then (if x<2730 then 1 else 1) else (if x<2758 then 2 else 2))) else (if x<3256 then (if x<3192 then (if x<2800 then 0 else 3) else (if x<3214 then 0 else 3)) else (if x<3284 then (if x<3274 then 2 else 2) else (if x<3298 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers929 : Finset ℕ := ([48,252,1596,1628,1642,1678,1702,1720,1738,1748,1776,2620,2638,2680,2716,2730,2740,2758,2776,2800,3118,3164,3188,3192,3214,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers929 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers929 3270 5
  · have he : independentCachedBranchMembers929.erase 3270=independentCachedBranchMembers927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound927
  · have he : independentCachedBranchMembers929.filter (independentCachedEdge 3270)=independentCachedBranchMembers928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound928
def independentCachedBranchMembers930 : Finset ℕ := ([48,1702,1738,1776,2638,2680,2716,2730,2758,2800,3164,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers930 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers930 5 (fun x => (if x<2758 then (if x<2638 then (if x<1738 then (if x<1702 then 0 else 1) else (if x<1776 then 0 else 0)) else (if x<2716 then (if x<2680 then 0 else 1) else (if x<2730 then 2 else 1))) else (if x<3252 then (if x<3164 then (if x<2800 then 2 else 2) else (if x<3214 then 1 else 0)) else (if x<3284 then (if x<3256 then 0 else 2) else (if x<3288 then 2 else (if x<3298 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers931 : Finset ℕ := ([48,252,1596,1628,1642,1678,1702,1720,1738,1748,1776,2620,2638,2680,2716,2730,2740,2758,2776,2800,3118,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers931 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers931 3228 5
  · have he : independentCachedBranchMembers931.erase 3228=independentCachedBranchMembers929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound929
  · have he : independentCachedBranchMembers931.filter (independentCachedEdge 3228)=independentCachedBranchMembers930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound930
def independentCachedBranchMembers932 : Finset ℕ := ([252,1596,1702,1748,2620,2638,2680,2716,2730,2776,3118,3164,3214,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers932 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers932 5 (fun x => (if x<2730 then (if x<2620 then (if x<1702 then (if x<1596 then 0 else 0) else (if x<1748 then 1 else 0)) else (if x<2680 then (if x<2638 then 2 else 2) else (if x<2716 then 1 else 0))) else (if x<3214 then (if x<3118 then (if x<2776 then 1 else 2) else (if x<3164 then 2 else 0)) else (if x<3256 then (if x<3252 then 1 else 0) else (if x<3270 then 2 else (if x<3274 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers933 : Finset ℕ := ([48,252,1596,1628,1642,1678,1702,1720,1738,1748,1776,2620,2638,2680,2716,2730,2740,2758,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers933 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers933 3150 5
  · have he : independentCachedBranchMembers933.erase 3150=independentCachedBranchMembers931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound931
  · have he : independentCachedBranchMembers933.filter (independentCachedEdge 3150)=independentCachedBranchMembers932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound932
def independentCachedBranchMembers934 : Finset ℕ := ([48,252,1596,1628,1678,1738,1748,1776,2638,2716,2758,2776,3164,3192,3214,3252,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers934 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers934 5 (fun x => (if x<2716 then (if x<1678 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1628 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 2) else (if x<1776 then 2 else (if x<2638 then 0 else 1)))) else (if x<3192 then (if x<2776 then (if x<2758 then 1 else 2) else (if x<3164 then 2 else 3)) else (if x<3252 then (if x<3214 then 0 else 3) else (if x<3274 then 0 else (if x<3284 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers935 : Finset ℕ := ([48,252,1596,1628,1642,1678,1702,1720,1738,1748,1776,2620,2638,2662,2680,2716,2730,2740,2758,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers935 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers935 2662 5
  · have he : independentCachedBranchMembers935.erase 2662=independentCachedBranchMembers933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound933
  · have he : independentCachedBranchMembers935.filter (independentCachedEdge 2662)=independentCachedBranchMembers934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound934
def independentCachedBranchMembers936 : Finset ℕ := ([1596,1628,1678,1738,1748,1776,2638,2716,2758,2776,3118,3150,3188,3228,3256,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers936 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers936 5 (fun x => (if x<2776 then (if x<1748 then (if x<1678 then (if x<1628 then 0 else 1) else (if x<1738 then 0 else 1)) else (if x<2638 then (if x<1776 then 0 else 1) else (if x<2716 then 1 else (if x<2758 then 0 else 0)))) else (if x<3228 then (if x<3150 then (if x<3118 then 1 else 2) else (if x<3188 then 3 else 2)) else (if x<3270 then (if x<3256 then 2 else 4) else (if x<3288 then 2 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers937 : Finset ℕ := ([48,252,1596,1628,1642,1652,1678,1702,1720,1738,1748,1776,2620,2638,2662,2680,2716,2730,2740,2758,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers937 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers937 1652 5
  · have he : independentCachedBranchMembers937.erase 1652=independentCachedBranchMembers935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound935
  · have he : independentCachedBranchMembers937.filter (independentCachedEdge 1652)=independentCachedBranchMembers936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound936
def independentCachedBranchMembers938 : Finset ℕ := ([48,1596,1678,1702,1720,1738,1748,2716,2730,2740,2758,2776,2800,3150,3192,3214,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers938 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers938 5 (fun x => (if x<2758 then (if x<1738 then (if x<1678 then (if x<1596 then 0 else 0) else (if x<1702 then 0 else (if x<1720 then 1 else 1))) else (if x<2716 then (if x<1748 then 1 else 1) else (if x<2730 then 2 else (if x<2740 then 1 else 1)))) else (if x<3214 then (if x<2800 then (if x<2776 then 0 else 1) else (if x<3150 then 2 else (if x<3192 then 3 else 0))) else (if x<3274 then (if x<3256 then 2 else 2) else (if x<3284 then 0 else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers939 : Finset ℕ := ([48,252,1596,1628,1642,1652,1678,1702,1720,1738,1748,1776,2620,2638,2662,2680,2716,2730,2740,2758,2772,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers939 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers939 2772 5
  · have he : independentCachedBranchMembers939.erase 2772=independentCachedBranchMembers937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound937
  · have he : independentCachedBranchMembers939.filter (independentCachedEdge 2772)=independentCachedBranchMembers938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound938
def independentCachedBranchMembers940 : Finset ℕ := ([252,1628,1702,1720,1738,1748,1776,2620,2638,2730,2740,2758,2776,3118,3164,3192,3228,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers940 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers940 5 (fun x => (if x<2740 then (if x<1748 then (if x<1702 then (if x<1628 then 0 else 0) else (if x<1720 then 1 else (if x<1738 then 0 else 1))) else (if x<2620 then (if x<1776 then 1 else 2) else (if x<2638 then 0 else (if x<2730 then 2 else 1)))) else (if x<3192 then (if x<2776 then (if x<2758 then 1 else 1) else (if x<3118 then 0 else (if x<3164 then 2 else 3))) else (if x<3256 then (if x<3228 then 0 else 0) else (if x<3274 then 2 else (if x<3284 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers941 : Finset ℕ := ([48,252,1596,1628,1642,1652,1678,1702,1720,1738,1748,1776,2620,2638,2662,2680,2716,2730,2740,2758,2762,2772,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers941 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers941 2762 5
  · have he : independentCachedBranchMembers941.erase 2762=independentCachedBranchMembers939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound939
  · have he : independentCachedBranchMembers941.filter (independentCachedEdge 2762)=independentCachedBranchMembers940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound940
def independentCachedBranchMembers942 : Finset ℕ := ([48,1628,1702,1720,1738,1748,1776,2620,2638,2730,2740,2758,2776,3150,3188,3214,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers942 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers942 5 (fun x => (if x<2740 then (if x<1748 then (if x<1702 then (if x<1628 then 0 else 1) else (if x<1720 then 2 else (if x<1738 then 0 else 0))) else (if x<2620 then (if x<1776 then 2 else 1) else (if x<2638 then 0 else (if x<2730 then 0 else 2)))) else (if x<3214 then (if x<2776 then (if x<2758 then 2 else 2) else (if x<3150 then 1 else (if x<3188 then 3 else 3))) else (if x<3270 then (if x<3252 then 4 else 0) else (if x<3288 then 0 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers943 : Finset ℕ := ([48,252,1596,1628,1642,1652,1678,1702,1720,1738,1748,1752,1776,2620,2638,2662,2680,2716,2730,2740,2758,2762,2772,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers943 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers943 1752 5
  · have he : independentCachedBranchMembers943.erase 1752=independentCachedBranchMembers941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound941
  · have he : independentCachedBranchMembers943.filter (independentCachedEdge 1752)=independentCachedBranchMembers942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound942
def independentCachedBranchMembers944 : Finset ℕ := ([252,1596,1678,1702,1720,1738,1748,2716,2730,2740,2758,2776,2800,3118,3164,3188,3228,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers944 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers944 5 (fun x => (if x<2758 then (if x<1738 then (if x<1678 then (if x<1596 then 0 else 0) else (if x<1702 then 1 else (if x<1720 then 2 else 1))) else (if x<2716 then (if x<1748 then 2 else 0) else (if x<2730 then 0 else (if x<2740 then 1 else 2)))) else (if x<3188 then (if x<2800 then (if x<2776 then 1 else 2) else (if x<3118 then 1 else (if x<3164 then 3 else 0))) else (if x<3252 then (if x<3228 then 3 else 3) else (if x<3270 then 0 else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers945 : Finset ℕ := ([48,252,1596,1628,1642,1652,1678,1702,1720,1734,1738,1748,1752,1776,2620,2638,2662,2680,2716,2730,2740,2758,2762,2772,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers945 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers945 1734 5
  · have he : independentCachedBranchMembers945.erase 1734=independentCachedBranchMembers943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound943
  · have he : independentCachedBranchMembers945.filter (independentCachedEdge 1734)=independentCachedBranchMembers944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound944
def independentCachedBranchMembers946 : Finset ℕ := ([252,1596,1628,1642,1678,1720,1748,1752,2638,2680,2716,2730,2758,2762,2800,3164,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers946 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers946 5 (fun x => (if x<2730 then (if x<1720 then (if x<1628 then (if x<1596 then 0 else 0) else (if x<1642 then 1 else (if x<1678 then 1 else 1))) else (if x<2638 then (if x<1748 then 1 else (if x<1752 then 0 else 2)) else (if x<2680 then 1 else (if x<2716 then 1 else 0)))) else (if x<3214 then (if x<2762 then (if x<2758 then 1 else 3) else (if x<2800 then 2 else (if x<3164 then 2 else 0))) else (if x<3284 then (if x<3252 then 3 else (if x<3256 then 0 else 3)) else (if x<3288 then 3 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers947 : Finset ℕ := ([48,252,1596,1628,1642,1652,1678,1702,1720,1734,1738,1748,1752,1776,2620,2638,2662,2680,2702,2716,2730,2740,2758,2762,2772,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers947 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers947 2702 5
  · have he : independentCachedBranchMembers947.erase 2702=independentCachedBranchMembers945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound945
  · have he : independentCachedBranchMembers947.filter (independentCachedEdge 2702)=independentCachedBranchMembers946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound946
def independentCachedBranchMembers948 : Finset ℕ := ([48,1628,1642,1678,1720,1734,1738,1776,2620,2638,2680,2716,2730,2772,2776,3118,3164,3214,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers948 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers948 5 (fun x => (if x<2716 then (if x<1734 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1678 then 1 else (if x<1720 then 0 else 0))) else (if x<2620 then (if x<1738 then 1 else (if x<1776 then 2 else 1)) else (if x<2638 then 2 else (if x<2680 then 0 else 0)))) else (if x<3164 then (if x<2772 then (if x<2730 then 3 else 2) else (if x<2776 then 1 else (if x<3118 then 2 else 4))) else (if x<3256 then (if x<3214 then 3 else (if x<3252 then 3 else 3)) else (if x<3270 then 4 else (if x<3274 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers949 : Finset ℕ := ([48,252,1596,1628,1642,1652,1678,1702,1720,1734,1738,1748,1752,1776,2620,2638,2652,2662,2680,2702,2716,2730,2740,2758,2762,2772,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers949 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers949 2652 5
  · have he : independentCachedBranchMembers949.erase 2652=independentCachedBranchMembers947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound947
  · have he : independentCachedBranchMembers949.filter (independentCachedEdge 2652)=independentCachedBranchMembers948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound948
def independentCachedBranchMembers950 : Finset ℕ := ([48,1596,1628,1642,1678,1720,1748,1752,2638,2680,2716,2730,2758,2762,2800,3118,3150,3188,3192,3228,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers950 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers950 5 (fun x => (if x<2730 then (if x<1720 then (if x<1628 then (if x<1596 then 0 else 0) else (if x<1642 then 1 else (if x<1678 then 1 else 0))) else (if x<2638 then (if x<1748 then 1 else (if x<1752 then 2 else 3)) else (if x<2680 then 1 else (if x<2716 then 0 else 1)))) else (if x<3150 then (if x<2762 then (if x<2758 then 1 else 2) else (if x<2800 then 0 else (if x<3118 then 2 else 3))) else (if x<3228 then (if x<3188 then 4 else (if x<3192 then 0 else 3)) else (if x<3270 then 3 else (if x<3274 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers951 : Finset ℕ := ([48,252,1596,1628,1642,1652,1678,1692,1702,1720,1734,1738,1748,1752,1776,2620,2638,2652,2662,2680,2702,2716,2730,2740,2758,2762,2772,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers951 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers951 1692 5
  · have he : independentCachedBranchMembers951.erase 1692=independentCachedBranchMembers949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound949
  · have he : independentCachedBranchMembers951.filter (independentCachedEdge 1692)=independentCachedBranchMembers950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound950
def independentCachedBranchMembers952 : Finset ℕ := ([252,1628,1642,1678,1720,1734,1738,1776,2620,2638,2680,2716,2730,2772,2776,3150,3188,3192,3228,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers952 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers952 5 (fun x => (if x<2716 then (if x<1734 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 1 else (if x<1720 then 1 else 0))) else (if x<2620 then (if x<1738 then 2 else (if x<1776 then 3 else 2)) else (if x<2638 then 0 else (if x<2680 then 1 else 1)))) else (if x<3188 then (if x<2772 then (if x<2730 then 1 else 1) else (if x<2776 then 2 else (if x<3150 then 0 else 3))) else (if x<3284 then (if x<3192 then 3 else (if x<3228 then 0 else 0)) else (if x<3288 then 4 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers953 : Finset ℕ := ([48,252,1596,1614,1628,1642,1652,1678,1692,1702,1720,1734,1738,1748,1752,1776,2620,2638,2652,2662,2680,2702,2716,2730,2740,2758,2762,2772,2776,2800,3118,3150,3164,3188,3192,3214,3228,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers953 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers953 1614 5
  · have he : independentCachedBranchMembers953.erase 1614=independentCachedBranchMembers951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound951
  · have he : independentCachedBranchMembers953.filter (independentCachedEdge 1614)=independentCachedBranchMembers952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound952
def independentCachedBranchMembers954 : Finset ℕ := ([48,252,1596,1642,1652,1702,1720,1738,1748,1776,2620,2638,2716,2762,2772,2800,3118,3164,3192,3214,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers954 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers954 5 (fun x => (if x<2716 then (if x<1720 then (if x<1642 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1652 then 1 else (if x<1702 then 1 else 1))) else (if x<1776 then (if x<1738 then 1 else (if x<1748 then 2 else 2)) else (if x<2620 then 0 else (if x<2638 then 3 else 3)))) else (if x<3192 then (if x<2800 then (if x<2762 then 4 else (if x<2772 then 4 else 3)) else (if x<3118 then 4 else (if x<3164 then 3 else 3))) else (if x<3270 then (if x<3214 then 0 else (if x<3252 then 4 else 0)) else (if x<3288 then 2 else (if x<3298 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers955 : Finset ℕ := ([48,1596,1642,1720,1748,2638,2716,2762,2800,3118,3192,3270] : List ℕ).toFinset
theorem independentCachedBranchBound955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers955 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers955 4 (fun x => (if x<2716 then (if x<1720 then (if x<1596 then 0 else (if x<1642 then 0 else 1)) else (if x<1748 then 1 else (if x<2638 then 2 else 1))) else (if x<3118 then (if x<2762 then 1 else (if x<2800 then 0 else 2)) else (if x<3192 then 2 else (if x<3270 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers956 : Finset ℕ := ([48,252,1596,1642,1652,1692,1702,1720,1738,1748,1776,2620,2638,2716,2762,2772,2800,3118,3164,3192,3214,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers956 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers956 1692 4
  · have he : independentCachedBranchMembers956.erase 1692=independentCachedBranchMembers954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound954
  · have he : independentCachedBranchMembers956.filter (independentCachedEdge 1692)=independentCachedBranchMembers955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound955
def independentCachedBranchMembers957 : Finset ℕ := ([252,1642,1720,1738,1776,2620,2638,2716,2772,3192,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers957 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers957 4 (fun x => (if x<2638 then (if x<1738 then (if x<1642 then 0 else (if x<1720 then 1 else 0)) else (if x<1776 then 2 else (if x<2620 then 1 else 0))) else (if x<3192 then (if x<2716 then 1 else (if x<2772 then 3 else 1)) else (if x<3288 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers958 : Finset ℕ := ([48,252,1596,1614,1642,1652,1692,1702,1720,1738,1748,1776,2620,2638,2716,2762,2772,2800,3118,3164,3192,3214,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers958 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers958 1614 4
  · have he : independentCachedBranchMembers958.erase 1614=independentCachedBranchMembers956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound956
  · have he : independentCachedBranchMembers958.filter (independentCachedEdge 1614)=independentCachedBranchMembers957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound957
def independentCachedBranchMembers959 : Finset ℕ := ([48,252,1596,1614,1628,1642,1652,1678,1692,1702,1720,1734,1738,1748,1752,1776,2620,2638,2652,2662,2680,2702,2716,2730,2740,2758,2762,2772,2776,2800,3118,3150,3164,3188,3192,3214,3228,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers959 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers959 3238 5
  · have he : independentCachedBranchMembers959.erase 3238=independentCachedBranchMembers953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound953
  · have he : independentCachedBranchMembers959.filter (independentCachedEdge 3238)=independentCachedBranchMembers958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound958
def independentCachedBranchMembers960 : Finset ℕ := ([48,252,1596,1642,1652,1702,1720,1734,1752,1776,2620,2652,2702,2758,2776,2800,3118,3150,3192,3228,3252,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers960 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers960 5 (fun x => (if x<2702 then (if x<1720 then (if x<1642 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1652 then 1 else (if x<1702 then 1 else 1))) else (if x<1776 then (if x<1734 then 1 else (if x<1752 then 2 else 2)) else (if x<2620 then 0 else (if x<2652 then 3 else 4)))) else (if x<3192 then (if x<2800 then (if x<2758 then 3 else (if x<2776 then 4 else 3)) else (if x<3118 then 4 else (if x<3150 then 3 else 4))) else (if x<3274 then (if x<3228 then 0 else (if x<3252 then 3 else 0)) else (if x<3284 then 2 else (if x<3298 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers961 : Finset ℕ := ([252,1652,1702,1734,1776,2620,2652,2702,2776,3252,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers961 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers961 4 (fun x => (if x<2652 then (if x<1734 then (if x<1652 then 0 else (if x<1702 then 0 else 1)) else (if x<1776 then 2 else (if x<2620 then 1 else 0))) else (if x<3252 then (if x<2702 then 3 else (if x<2776 then 1 else 1)) else (if x<3284 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers962 : Finset ℕ := ([48,252,1596,1642,1652,1678,1702,1720,1734,1752,1776,2620,2652,2702,2758,2776,2800,3118,3150,3192,3228,3252,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers962 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers962 1678 4
  · have he : independentCachedBranchMembers962.erase 1678=independentCachedBranchMembers960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound960
  · have he : independentCachedBranchMembers962.filter (independentCachedEdge 1678)=independentCachedBranchMembers961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound961
def independentCachedBranchMembers963 : Finset ℕ := ([48,1596,1652,1702,1752,2652,2702,2758,2800,3118,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers963 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers963 4 (fun x => (if x<2702 then (if x<1702 then (if x<1596 then 0 else (if x<1652 then 0 else 1)) else (if x<1752 then 1 else (if x<2652 then 2 else 1))) else (if x<3118 then (if x<2758 then 1 else (if x<2800 then 0 else 2)) else (if x<3252 then 2 else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers964 : Finset ℕ := ([48,252,1596,1628,1642,1652,1678,1702,1720,1734,1752,1776,2620,2652,2702,2758,2776,2800,3118,3150,3192,3228,3252,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers964 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers964 1628 4
  · have he : independentCachedBranchMembers964.erase 1628=independentCachedBranchMembers962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound962
  · have he : independentCachedBranchMembers964.filter (independentCachedEdge 1628)=independentCachedBranchMembers963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound963
def independentCachedBranchMembers965 : Finset ℕ := ([48,252,1596,1614,1628,1642,1652,1678,1692,1702,1720,1734,1738,1748,1752,1776,2620,2638,2652,2662,2680,2702,2716,2730,2740,2758,2762,2772,2776,2800,3118,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers965 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers965 3178 5
  · have he : independentCachedBranchMembers965.erase 3178=independentCachedBranchMembers959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound959
  · have he : independentCachedBranchMembers965.filter (independentCachedEdge 3178)=independentCachedBranchMembers964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound964
def independentCachedBranchMembers966 : Finset ℕ := ([48,252,1652,1678,1720,1752,2620,2652,2662,2716,2730,2758,2762,2800,3118,3150,3188,3192,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers966 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers966 5 (fun x => (if x<2762 then (if x<2620 then (if x<1678 then (if x<252 then 0 else (if x<1652 then 0 else 0)) else (if x<1720 then 1 else (if x<1752 then 0 else 1))) else (if x<2716 then (if x<2652 then 0 else (if x<2662 then 2 else 2)) else (if x<2730 then 1 else (if x<2758 then 3 else 3)))) else (if x<3214 then (if x<3150 then (if x<2800 then 1 else (if x<3118 then 0 else 4)) else (if x<3188 then 2 else (if x<3192 then 2 else 0))) else (if x<3284 then (if x<3252 then 3 else (if x<3256 then 0 else 3)) else (if x<3288 then 3 else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers967 : Finset ℕ := ([48,1652,1752,2620,2662,2762,3150,3192,3214,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers967 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers967 4 (fun x => (if x<3150 then (if x<2620 then (if x<1652 then 0 else (if x<1752 then 0 else 1)) else (if x<2662 then 0 else (if x<2762 then 1 else 1))) else (if x<3256 then (if x<3192 then 2 else (if x<3214 then 0 else 3)) else (if x<3284 then 3 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers968 : Finset ℕ := ([48,252,1652,1678,1720,1748,1752,2620,2652,2662,2716,2730,2758,2762,2800,3118,3150,3188,3192,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers968 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers968 1748 4
  · have he : independentCachedBranchMembers968.erase 1748=independentCachedBranchMembers966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound966
  · have he : independentCachedBranchMembers968.filter (independentCachedEdge 1748)=independentCachedBranchMembers967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound967
def independentCachedBranchMembers969 : Finset ℕ := ([252,1678,1720,2620,2716,2730,3150,3188,3192,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers969 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers969 4 (fun x => (if x<3150 then (if x<2620 then (if x<1678 then 0 else (if x<1720 then 1 else 0)) else (if x<2716 then 0 else (if x<2730 then 1 else 1))) else (if x<3284 then (if x<3188 then 2 else (if x<3192 then 2 else 0)) else (if x<3288 then 3 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers970 : Finset ℕ := ([48,252,1614,1652,1678,1720,1748,1752,2620,2652,2662,2716,2730,2758,2762,2800,3118,3150,3188,3192,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers970 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers970 1614 4
  · have he : independentCachedBranchMembers970.erase 1614=independentCachedBranchMembers968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound968
  · have he : independentCachedBranchMembers970.filter (independentCachedEdge 1614)=independentCachedBranchMembers969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound969
def independentCachedBranchMembers971 : Finset ℕ := ([48,252,1596,1614,1628,1642,1652,1678,1692,1702,1720,1734,1738,1748,1752,1776,2620,2638,2652,2662,2680,2702,2716,2730,2740,2758,2762,2772,2776,2786,2800,3118,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers971 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers971 2786 5
  · have he : independentCachedBranchMembers971.erase 2786=independentCachedBranchMembers965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound965
  · have he : independentCachedBranchMembers971.filter (independentCachedEdge 2786)=independentCachedBranchMembers970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound970
def independentCachedBranchMembers972 : Finset ℕ := ([48,252,1652,1692,1720,1738,2620,2638,2662,2702,2730,2772,2776,2800,3118,3164,3188,3192,3228,3252,3256,3270,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers972 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers972 5 (fun x => (if x<2776 then (if x<2620 then (if x<1692 then (if x<252 then 0 else (if x<1652 then 0 else 0)) else (if x<1720 then 1 else (if x<1738 then 0 else 1))) else (if x<2702 then (if x<2638 then 0 else (if x<2662 then 2 else 3)) else (if x<2730 then 1 else (if x<2772 then 2 else 3)))) else (if x<3228 then (if x<3164 then (if x<2800 then 1 else (if x<3118 then 0 else 2)) else (if x<3188 then 2 else (if x<3192 then 3 else 0))) else (if x<3270 then (if x<3252 then 3 else (if x<3256 then 0 else 2)) else (if x<3274 then 3 else (if x<3298 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers973 : Finset ℕ := ([252,1720,1738,2730,2776,2800,3118,3164,3188,3228,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers973 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers973 4 (fun x => (if x<3118 then (if x<2730 then (if x<1720 then 0 else (if x<1738 then 0 else 1)) else (if x<2776 then 1 else (if x<2800 then 0 else 2))) else (if x<3228 then (if x<3164 then 2 else (if x<3188 then 3 else 1)) else (if x<3252 then 0 else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers974 : Finset ℕ := ([48,252,1652,1692,1720,1734,1738,2620,2638,2662,2702,2730,2772,2776,2800,3118,3164,3188,3192,3228,3252,3256,3270,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers974 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers974 1734 4
  · have he : independentCachedBranchMembers974.erase 1734=independentCachedBranchMembers972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound972
  · have he : independentCachedBranchMembers974.filter (independentCachedEdge 1734)=independentCachedBranchMembers973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound973
def independentCachedBranchMembers975 : Finset ℕ := ([48,1652,1692,2662,2702,2800,3118,3164,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers975 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers975 4 (fun x => (if x<3118 then (if x<2662 then (if x<1652 then 0 else (if x<1692 then 0 else 1)) else (if x<2702 then 1 else (if x<2800 then 0 else 2))) else (if x<3256 then (if x<3164 then 2 else (if x<3252 then 3 else 2)) else (if x<3270 then 1 else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers976 : Finset ℕ := ([48,252,1628,1652,1692,1720,1734,1738,2620,2638,2662,2702,2730,2772,2776,2800,3118,3164,3188,3192,3228,3252,3256,3270,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers976 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers976 1628 4
  · have he : independentCachedBranchMembers976.erase 1628=independentCachedBranchMembers974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound974
  · have he : independentCachedBranchMembers976.filter (independentCachedEdge 1628)=independentCachedBranchMembers975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound975
def independentCachedBranchMembers977 : Finset ℕ := ([48,252,1596,1614,1628,1642,1652,1678,1692,1702,1720,1734,1738,1748,1752,1776,2606,2620,2638,2652,2662,2680,2702,2716,2730,2740,2758,2762,2772,2776,2786,2800,3118,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers977 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers977 2606 5
  · have he : independentCachedBranchMembers977.erase 2606=independentCachedBranchMembers971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound971
  · have he : independentCachedBranchMembers977.filter (independentCachedEdge 2606)=independentCachedBranchMembers976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound976
def independentCachedBranchMembers978 : Finset ℕ := ([18,48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers978 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers978 18 6
  · have he : independentCachedBranchMembers978.erase 18=independentCachedBranchMembers924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound924
  · have he : independentCachedBranchMembers978.filter (independentCachedEdge 18)=independentCachedBranchMembers977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound977
def independentCachedBranchMembers979 : Finset ℕ := ([72,132,1594,1642,1652,1686,1702,1720,1738,1752,1764,2614,2650,2662,2680,2710,2730,2740,2758,2772,2792,3126,3158,3178,3192,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers979 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers979 6 (fun x => (if x<2710 then (if x<1720 then (if x<1642 then (if x<132 then 0 else (if x<1594 then 0 else 1)) else (if x<1686 then (if x<1652 then 0 else 1) else (if x<1702 then 1 else 0))) else (if x<2614 then (if x<1752 then (if x<1738 then 2 else 2) else (if x<1764 then 1 else 2)) else (if x<2662 then (if x<2650 then 1 else 0) else (if x<2680 then 3 else 1)))) else (if x<3178 then (if x<2772 then (if x<2740 then (if x<2730 then 0 else 3) else (if x<2758 then 2 else 2)) else (if x<3126 then (if x<2792 then 1 else 2) else (if x<3158 then 4 else 3))) else (if x<3252 then (if x<3226 then (if x<3192 then 3 else 0) else (if x<3238 then 3 else 3)) else (if x<3284 then (if x<3270 then 0 else 4) else (if x<3304 then 5 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers980 : Finset ℕ := ([72,1642,1686,1720,1738,1752,1764,2614,2680,2710,2730,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers980 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers980 5 (fun x => (if x<2680 then (if x<1738 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1720 then 1 else 1)) else (if x<1764 then (if x<1752 then 1 else 0) else (if x<2614 then 1 else 2))) else (if x<3238 then (if x<2730 then (if x<2710 then 0 else 3) else (if x<3226 then 2 else 1)) else (if x<3270 then (if x<3252 then 2 else 1) else (if x<3284 then 1 else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers981 : Finset ℕ := ([72,132,1594,1642,1652,1686,1702,1720,1738,1752,1764,2614,2650,2662,2680,2710,2730,2740,2758,2772,2792,3126,3158,3178,3192,3226,3238,3252,3270,3284,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers981 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers981 3300 5
  · have he : independentCachedBranchMembers981.erase 3300=independentCachedBranchMembers979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound979
  · have he : independentCachedBranchMembers981.filter (independentCachedEdge 3300)=independentCachedBranchMembers980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound980
def independentCachedBranchMembers982 : Finset ℕ := ([132,1594,1642,1652,1686,1752,1764,2710,2730,2740,2758,3126,3192,3226,3238,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers982 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers982 5 (fun x => (if x<2730 then (if x<1686 then (if x<1642 then (if x<1594 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1764 then (if x<1752 then 0 else 1) else (if x<2710 then 2 else 3))) else (if x<3192 then (if x<2758 then (if x<2740 then 3 else 2) else (if x<3126 then 0 else 4)) else (if x<3238 then (if x<3226 then 0 else 3) else (if x<3284 then 2 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers983 : Finset ℕ := ([72,132,1594,1642,1652,1686,1702,1720,1738,1752,1764,2614,2650,2662,2680,2710,2730,2740,2758,2772,2792,3126,3158,3178,3192,3226,3238,3252,3270,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers983 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers983 3288 5
  · have he : independentCachedBranchMembers983.erase 3288=independentCachedBranchMembers981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound981
  · have he : independentCachedBranchMembers983.filter (independentCachedEdge 3288)=independentCachedBranchMembers982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound982
def independentCachedBranchMembers984 : Finset ℕ := ([132,1594,1686,1702,1720,1738,1764,2662,2680,2710,2772,3126,3178,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers984 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers984 5 (fun x => (if x<2710 then (if x<1720 then (if x<1686 then (if x<1594 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1764 then (if x<1738 then 1 else 1) else (if x<2662 then 2 else (if x<2680 then 2 else 0)))) else (if x<3226 then (if x<3126 then (if x<2772 then 3 else 0) else (if x<3178 then 3 else 0)) else (if x<3270 then (if x<3252 then 2 else 1) else (if x<3288 then 0 else (if x<3304 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers985 : Finset ℕ := ([72,132,1594,1642,1652,1686,1702,1720,1738,1752,1764,2614,2650,2662,2680,2710,2730,2740,2758,2772,2792,3126,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers985 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers985 3274 5
  · have he : independentCachedBranchMembers985.erase 3274=independentCachedBranchMembers983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound983
  · have he : independentCachedBranchMembers985.filter (independentCachedEdge 3274)=independentCachedBranchMembers984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound984
def independentCachedBranchMembers986 : Finset ℕ := ([72,1594,1652,1686,1702,1738,1752,2662,2710,2740,2792,3126,3178,3192,3226,3270,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers986 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers986 5 (fun x => (if x<2740 then (if x<1702 then (if x<1652 then (if x<1594 then 0 else 1) else (if x<1686 then 1 else 0)) else (if x<1752 then (if x<1738 then 1 else 0) else (if x<2662 then 2 else (if x<2710 then 2 else 3)))) else (if x<3192 then (if x<3126 then (if x<2792 then 0 else 0) else (if x<3178 then 0 else 0)) else (if x<3270 then (if x<3226 then 1 else 2) else (if x<3284 then 3 else (if x<3300 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers987 : Finset ℕ := ([72,132,1594,1642,1652,1686,1702,1720,1738,1752,1764,2614,2650,2662,2680,2710,2730,2740,2758,2772,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers987 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers987 3130 5
  · have he : independentCachedBranchMembers987.erase 3130=independentCachedBranchMembers985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound985
  · have he : independentCachedBranchMembers987.filter (independentCachedEdge 3130)=independentCachedBranchMembers986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound986
def independentCachedBranchMembers988 : Finset ℕ := ([1594,1642,1702,1738,1752,1764,2614,2650,2662,2710,2730,2758,2772,2792,3126,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers988 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers988 5 (fun x => (if x<2710 then (if x<1752 then (if x<1702 then (if x<1642 then 0 else 1) else (if x<1738 then 0 else 0)) else (if x<2614 then (if x<1764 then 1 else 1) else (if x<2650 then 0 else (if x<2662 then 0 else 1)))) else (if x<2792 then (if x<2758 then (if x<2730 then 2 else 0) else (if x<2772 then 0 else 1)) else (if x<3270 then (if x<3126 then 1 else 2) else (if x<3284 then 2 else (if x<3304 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers989 : Finset ℕ := ([72,132,1594,1626,1642,1652,1686,1702,1720,1738,1752,1764,2614,2650,2662,2680,2710,2730,2740,2758,2772,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers989 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers989 1626 5
  · have he : independentCachedBranchMembers989.erase 1626=independentCachedBranchMembers987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound987
  · have he : independentCachedBranchMembers989.filter (independentCachedEdge 1626)=independentCachedBranchMembers988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound988
def independentCachedBranchMembers990 : Finset ℕ := ([72,1642,1686,1720,1738,1752,1764,2650,2662,2740,2758,2772,2792,3126,3158,3178,3192,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers990 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers990 5 (fun x => (if x<2758 then (if x<1752 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1720 then 1 else (if x<1738 then 1 else 1))) else (if x<2650 then (if x<1764 then 0 else 1) else (if x<2662 then 0 else (if x<2740 then 2 else 1)))) else (if x<3178 then (if x<2792 then (if x<2772 then 1 else 2) else (if x<3126 then 0 else (if x<3158 then 3 else 2))) else (if x<3274 then (if x<3192 then 2 else 0) else (if x<3288 then 0 else (if x<3300 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers991 : Finset ℕ := ([72,132,1594,1626,1642,1652,1686,1702,1720,1738,1752,1764,2614,2650,2662,2680,2710,2730,2740,2758,2772,2788,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers991 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers991 2788 5
  · have he : independentCachedBranchMembers991.erase 2788=independentCachedBranchMembers989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound989
  · have he : independentCachedBranchMembers991.filter (independentCachedEdge 2788)=independentCachedBranchMembers990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound990
def independentCachedBranchMembers992 : Finset ℕ := ([132,1594,1642,1652,1686,1752,1764,2614,2650,2662,2680,2772,2792,3130,3158,3178,3252,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers992 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers992 5 (fun x => (if x<2680 then (if x<1752 then (if x<1642 then (if x<1594 then 0 else 0) else (if x<1652 then 1 else (if x<1686 then 1 else 0))) else (if x<2614 then (if x<1764 then 1 else 2) else (if x<2650 then 3 else (if x<2662 then 2 else 1)))) else (if x<3178 then (if x<2792 then (if x<2772 then 0 else 0) else (if x<3130 then 2 else (if x<3158 then 3 else 3))) else (if x<3270 then (if x<3252 then 0 else 3) else (if x<3288 then 0 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers993 : Finset ℕ := ([72,132,1594,1626,1642,1652,1686,1702,1720,1738,1752,1764,2614,2650,2662,2680,2710,2730,2740,2758,2772,2776,2788,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers993 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers993 2776 5
  · have he : independentCachedBranchMembers993.erase 2776=independentCachedBranchMembers991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound991
  · have he : independentCachedBranchMembers993.filter (independentCachedEdge 2776)=independentCachedBranchMembers992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound992
def independentCachedBranchMembers994 : Finset ℕ := ([132,1642,1686,1720,1738,1752,1764,2650,2662,2740,2758,2772,2792,3130,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers994 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers994 5 (fun x => (if x<2758 then (if x<1752 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1720 then 1 else (if x<1738 then 1 else 1))) else (if x<2650 then (if x<1764 then 2 else 0) else (if x<2662 then 0 else (if x<2740 then 2 else 1)))) else (if x<3238 then (if x<2792 then (if x<2772 then 1 else 0) else (if x<3130 then 1 else (if x<3226 then 0 else 2))) else (if x<3270 then (if x<3252 then 2 else 0) else (if x<3284 then 3 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers995 : Finset ℕ := ([72,132,1594,1626,1642,1652,1686,1702,1720,1738,1752,1764,1768,2614,2650,2662,2680,2710,2730,2740,2758,2772,2776,2788,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers995 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers995 1768 5
  · have he : independentCachedBranchMembers995.erase 1768=independentCachedBranchMembers993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound993
  · have he : independentCachedBranchMembers995.filter (independentCachedEdge 1768)=independentCachedBranchMembers994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound994
def independentCachedBranchMembers996 : Finset ℕ := ([72,1594,1642,1652,1686,1752,1764,2614,2650,2662,2680,2772,2792,3126,3192,3226,3238,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers996 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers996 5 (fun x => (if x<2680 then (if x<1752 then (if x<1642 then (if x<1594 then 0 else 1) else (if x<1652 then 0 else (if x<1686 then 1 else 1))) else (if x<2614 then (if x<1764 then 0 else 2) else (if x<2650 then 1 else (if x<2662 then 0 else 2)))) else (if x<3226 then (if x<2792 then (if x<2772 then 1 else 1) else (if x<3126 then 0 else (if x<3192 then 3 else 0))) else (if x<3274 then (if x<3238 then 2 else 2) else (if x<3284 then 0 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers997 : Finset ℕ := ([72,132,1594,1626,1642,1652,1686,1702,1720,1738,1748,1752,1764,1768,2614,2650,2662,2680,2710,2730,2740,2758,2772,2776,2788,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers997 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers997 1748 5
  · have he : independentCachedBranchMembers997.erase 1748=independentCachedBranchMembers995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound995
  · have he : independentCachedBranchMembers997.filter (independentCachedEdge 1748)=independentCachedBranchMembers996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound996
def independentCachedBranchMembers998 : Finset ℕ := ([132,1594,1686,1702,1720,1738,1748,1764,2614,2650,2730,2740,2758,2776,2792,3130,3158,3192,3238,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers998 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers998 5 (fun x => (if x<2740 then (if x<1738 then (if x<1686 then (if x<1594 then 0 else 0) else (if x<1702 then 0 else (if x<1720 then 1 else 1))) else (if x<2614 then (if x<1748 then 1 else (if x<1764 then 1 else 2)) else (if x<2650 then 3 else (if x<2730 then 2 else 1)))) else (if x<3158 then (if x<2776 then (if x<2758 then 1 else 0) else (if x<2792 then 1 else (if x<3130 then 2 else 3))) else (if x<3274 then (if x<3192 then 3 else (if x<3238 then 0 else 3)) else (if x<3284 then 3 else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers999 : Finset ℕ := ([72,132,1594,1626,1642,1652,1686,1702,1720,1738,1748,1752,1764,1768,2614,2650,2662,2680,2710,2730,2740,2758,2762,2772,2776,2788,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers999 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers999 2762 5
  · have he : independentCachedBranchMembers999.erase 2762=independentCachedBranchMembers997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound997
  · have he : independentCachedBranchMembers999.filter (independentCachedEdge 2762)=independentCachedBranchMembers998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound998
def independentCachedBranchMembers1000 : Finset ℕ := ([72,1594,1652,1686,1702,1738,1752,1768,2614,2650,2680,2730,2758,2772,2788,3130,3158,3238,3252,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1000 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1000 5 (fun x => (if x<2730 then (if x<1738 then (if x<1652 then (if x<1594 then 0 else 1) else (if x<1686 then 1 else (if x<1702 then 0 else 1))) else (if x<2614 then (if x<1752 then 0 else (if x<1768 then 2 else 1)) else (if x<2650 then 0 else (if x<2680 then 2 else 1)))) else (if x<3158 then (if x<2772 then (if x<2758 then 1 else 3) else (if x<2788 then 2 else (if x<3130 then 1 else 3))) else (if x<3274 then (if x<3238 then 3 else (if x<3252 then 3 else 0)) else (if x<3288 then 3 else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1001 : Finset ℕ := ([72,132,1594,1626,1642,1652,1686,1702,1720,1738,1748,1752,1764,1768,2614,2618,2650,2662,2680,2710,2730,2740,2758,2762,2772,2776,2788,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1001 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1001 2618 5
  · have he : independentCachedBranchMembers1001.erase 2618=independentCachedBranchMembers999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound999
  · have he : independentCachedBranchMembers1001.filter (independentCachedEdge 2618)=independentCachedBranchMembers1000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1000
def independentCachedBranchMembers1002 : Finset ℕ := ([72,1686,1702,1720,1738,1748,1764,2614,2650,2730,2740,2758,2776,2792,3126,3178,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1002 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1002 5 (fun x => (if x<2740 then (if x<1748 then (if x<1702 then (if x<1686 then 0 else 0) else (if x<1720 then 1 else (if x<1738 then 1 else 0))) else (if x<2614 then (if x<1764 then 1 else 2) else (if x<2650 then 0 else (if x<2730 then 2 else 1)))) else (if x<3178 then (if x<2776 then (if x<2758 then 1 else 1) else (if x<2792 then 1 else (if x<3126 then 2 else 3))) else (if x<3270 then (if x<3226 then 3 else (if x<3252 then 3 else 0)) else (if x<3288 then 3 else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1003 : Finset ℕ := ([72,1720,1748,1764,2740,2776,2792,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1003 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1003 4 (fun x => (if x<2776 then (if x<1748 then (if x<1720 then 0 else 1) else (if x<1764 then 1 else (if x<2740 then 2 else 0))) else (if x<3252 then (if x<2792 then 0 else 2) else (if x<3288 then 1 else (if x<3304 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1004 : Finset ℕ := ([72,1594,1686,1702,1720,1738,1748,1764,2614,2650,2730,2740,2758,2776,2792,3126,3178,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1004 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1004 1594 4
  · have he : independentCachedBranchMembers1004.erase 1594=independentCachedBranchMembers1002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1002
  · have he : independentCachedBranchMembers1004.filter (independentCachedEdge 1594)=independentCachedBranchMembers1003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1003
def independentCachedBranchMembers1005 : Finset ℕ := ([72,132,1594,1626,1642,1652,1686,1702,1720,1734,1738,1748,1752,1764,1768,2614,2618,2650,2662,2680,2710,2730,2740,2758,2762,2772,2776,2788,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1005 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1005 1734 5
  · have he : independentCachedBranchMembers1005.erase 1734=independentCachedBranchMembers1001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1001
  · have he : independentCachedBranchMembers1005.filter (independentCachedEdge 1734)=independentCachedBranchMembers1004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1004
def independentCachedBranchMembers1006 : Finset ℕ := ([132,1594,1652,1686,1702,1738,1752,1768,2614,2650,2680,2730,2758,2772,2788,3126,3178,3192,3226,3270,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1006 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1006 5 (fun x => (if x<2730 then (if x<1738 then (if x<1652 then (if x<1594 then 0 else 0) else (if x<1686 then 1 else (if x<1702 then 0 else 1))) else (if x<2614 then (if x<1752 then 2 else (if x<1768 then 3 else 1)) else (if x<2650 then 1 else (if x<2680 then 2 else 0)))) else (if x<3178 then (if x<2772 then (if x<2758 then 1 else 2) else (if x<2788 then 0 else (if x<3126 then 1 else 3))) else (if x<3270 then (if x<3192 then 0 else (if x<3226 then 3 else 3)) else (if x<3284 then 0 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1007 : Finset ℕ := ([72,132,1590,1594,1626,1642,1652,1686,1702,1720,1734,1738,1748,1752,1764,1768,2614,2618,2650,2662,2680,2710,2730,2740,2758,2762,2772,2776,2788,2792,3126,3130,3158,3178,3192,3226,3238,3252,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1007 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1007 1590 5
  · have he : independentCachedBranchMembers1007.erase 1590=independentCachedBranchMembers1005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1005
  · have he : independentCachedBranchMembers1007.filter (independentCachedEdge 1590)=independentCachedBranchMembers1006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1006
def independentCachedBranchMembers1008 : Finset ℕ := ([72,132,1626,1642,1652,1686,1702,1720,1738,1764,2614,2650,2710,2762,2772,2788,3130,3158,3192,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1008 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1008 5 (fun x => (if x<2710 then (if x<1702 then (if x<1642 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1652 then 1 else (if x<1686 then 1 else 0))) else (if x<1764 then (if x<1720 then 1 else (if x<1738 then 1 else 2)) else (if x<2614 then 2 else (if x<2650 then 3 else 2)))) else (if x<3192 then (if x<2788 then (if x<2762 then 4 else (if x<2772 then 4 else 3)) else (if x<3130 then 4 else (if x<3158 then 3 else 3))) else (if x<3270 then (if x<3226 then 0 else (if x<3252 then 2 else 0)) else (if x<3288 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1009 : Finset ℕ := ([72,1642,1652,1686,1764,2614,2650,2762,2772,3192,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1009 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1009 4 (fun x => (if x<2650 then (if x<1686 then (if x<1642 then 0 else (if x<1652 then 0 else 1)) else (if x<1764 then 1 else (if x<2614 then 2 else 1))) else (if x<3192 then (if x<2762 then 0 else (if x<2772 then 3 else 1)) else (if x<3226 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1010 : Finset ℕ := ([72,132,1626,1642,1652,1686,1702,1720,1738,1748,1764,2614,2650,2710,2762,2772,2788,3130,3158,3192,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1010 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1010 1748 4
  · have he : independentCachedBranchMembers1010.erase 1748=independentCachedBranchMembers1008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1008
  · have he : independentCachedBranchMembers1010.filter (independentCachedEdge 1748)=independentCachedBranchMembers1009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1009
def independentCachedBranchMembers1011 : Finset ℕ := ([132,1652,1686,1702,1738,2614,2650,2772,2788,3192,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1011 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1011 4 (fun x => (if x<2650 then (if x<1702 then (if x<1652 then 0 else (if x<1686 then 1 else 0)) else (if x<1738 then 1 else (if x<2614 then 2 else 1))) else (if x<3192 then (if x<2772 then 2 else (if x<2788 then 0 else 1)) else (if x<3226 then 3 else (if x<3270 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1012 : Finset ℕ := ([72,132,1590,1626,1642,1652,1686,1702,1720,1738,1748,1764,2614,2650,2710,2762,2772,2788,3130,3158,3192,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1012 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1012 1590 4
  · have he : independentCachedBranchMembers1012.erase 1590=independentCachedBranchMembers1010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1010
  · have he : independentCachedBranchMembers1012.filter (independentCachedEdge 1590)=independentCachedBranchMembers1011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1011
def independentCachedBranchMembers1013 : Finset ℕ := ([72,132,1590,1594,1626,1642,1652,1686,1702,1720,1734,1738,1748,1752,1764,1768,2614,2618,2650,2662,2680,2710,2730,2740,2758,2762,2772,2776,2788,2792,3126,3130,3158,3178,3192,3226,3238,3252,3256,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1013 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1013 3256 5
  · have he : independentCachedBranchMembers1013.erase 3256=independentCachedBranchMembers1007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1007
  · have he : independentCachedBranchMembers1013.filter (independentCachedEdge 3256)=independentCachedBranchMembers1012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1012
def independentCachedBranchMembers1014 : Finset ℕ := ([72,132,1626,1642,1652,1686,1702,1720,1734,1768,2618,2650,2710,2758,2776,2792,3126,3158,3192,3226,3252,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1014 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1014 5 (fun x => (if x<2710 then (if x<1702 then (if x<1642 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1652 then 1 else (if x<1686 then 1 else 0))) else (if x<1768 then (if x<1720 then 1 else (if x<1734 then 1 else 2)) else (if x<2618 then 2 else (if x<2650 then 3 else 4)))) else (if x<3192 then (if x<2792 then (if x<2758 then 2 else (if x<2776 then 4 else 3)) else (if x<3126 then 4 else (if x<3158 then 3 else 2))) else (if x<3274 then (if x<3226 then 0 else (if x<3252 then 3 else 0)) else (if x<3284 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1015 : Finset ℕ := ([132,1626,1702,1720,1768,2618,2710,2758,2776,3158,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1015 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1015 4 (fun x => (if x<2710 then (if x<1720 then (if x<1626 then 0 else (if x<1702 then 0 else 1)) else (if x<1768 then 1 else (if x<2618 then 2 else 0))) else (if x<3158 then (if x<2758 then 2 else (if x<2776 then 1 else 1)) else (if x<3252 then 2 else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1016 : Finset ℕ := ([72,132,1626,1642,1652,1686,1702,1720,1734,1752,1768,2618,2650,2710,2758,2776,2792,3126,3158,3192,3226,3252,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1016 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1016 1752 4
  · have he : independentCachedBranchMembers1016.erase 1752=independentCachedBranchMembers1014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1014
  · have he : independentCachedBranchMembers1016.filter (independentCachedEdge 1752)=independentCachedBranchMembers1015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1015
def independentCachedBranchMembers1017 : Finset ℕ := ([72,1626,1642,1720,1734,2618,2710,2776,2792,3158,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1017 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1017 4 (fun x => (if x<2710 then (if x<1720 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1734 then 1 else (if x<2618 then 2 else 1))) else (if x<3158 then (if x<2776 then 2 else (if x<2792 then 0 else 1)) else (if x<3252 then 2 else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1018 : Finset ℕ := ([72,132,1594,1626,1642,1652,1686,1702,1720,1734,1752,1768,2618,2650,2710,2758,2776,2792,3126,3158,3192,3226,3252,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1018 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1018 1594 4
  · have he : independentCachedBranchMembers1018.erase 1594=independentCachedBranchMembers1016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1016
  · have he : independentCachedBranchMembers1018.filter (independentCachedEdge 1594)=independentCachedBranchMembers1017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1017
def independentCachedBranchMembers1019 : Finset ℕ := ([72,132,1590,1594,1626,1642,1652,1686,1702,1720,1734,1738,1748,1752,1764,1768,2614,2618,2650,2662,2680,2710,2730,2740,2758,2762,2772,2776,2788,2792,3126,3130,3158,3178,3188,3192,3226,3238,3252,3256,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1019 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1019 3188 5
  · have he : independentCachedBranchMembers1019.erase 3188=independentCachedBranchMembers1013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1013
  · have he : independentCachedBranchMembers1019.filter (independentCachedEdge 3188)=independentCachedBranchMembers1018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1018
def independentCachedBranchMembers1020 : Finset ℕ := ([72,132,1642,1702,1748,1768,2618,2650,2662,2710,2730,2762,2776,2788,3126,3158,3178,3192,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1020 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1020 5 (fun x => (if x<2776 then (if x<2618 then (if x<1702 then (if x<132 then 0 else (if x<1642 then 0 else 0)) else (if x<1748 then 0 else (if x<1768 then 1 else 1))) else (if x<2710 then (if x<2650 then 2 else (if x<2662 then 0 else 2)) else (if x<2730 then 0 else (if x<2762 then 1 else 2)))) else (if x<3226 then (if x<3158 then (if x<2788 then 1 else (if x<3126 then 1 else 2)) else (if x<3178 then 3 else (if x<3192 then 2 else 0))) else (if x<3270 then (if x<3238 then 2 else (if x<3252 then 3 else 0)) else (if x<3284 then 2 else (if x<3304 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1021 : Finset ℕ := ([72,1702,1748,2650,2730,2776,3126,3178,3226,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1021 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1021 4 (fun x => (if x<3126 then (if x<2650 then (if x<1702 then 0 else (if x<1748 then 0 else 1)) else (if x<2730 then 0 else (if x<2776 then 1 else 1))) else (if x<3252 then (if x<3178 then 2 else (if x<3226 then 2 else 2)) else (if x<3270 then 0 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1022 : Finset ℕ := ([72,132,1642,1702,1734,1748,1768,2618,2650,2662,2710,2730,2762,2776,2788,3126,3158,3178,3192,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1022 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1022 1734 4
  · have he : independentCachedBranchMembers1022.erase 1734=independentCachedBranchMembers1020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1020
  · have he : independentCachedBranchMembers1022.filter (independentCachedEdge 1734)=independentCachedBranchMembers1021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1021
def independentCachedBranchMembers1023 : Finset ℕ := ([132,1702,1768,2650,2730,2788,3126,3178,3192,3226,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1023 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1023 4 (fun x => (if x<3126 then (if x<2650 then (if x<1702 then 0 else (if x<1768 then 0 else 1)) else (if x<2730 then 0 else (if x<2788 then 1 else 1))) else (if x<3226 then (if x<3178 then 2 else (if x<3192 then 2 else 0)) else (if x<3270 then 2 else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
