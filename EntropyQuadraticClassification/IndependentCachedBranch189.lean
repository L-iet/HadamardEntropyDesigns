/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch188
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8832 : Finset ℕ := ([1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8832 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8832 1622 4
  · have he : independentCachedBranchMembers8832.erase 1622=independentCachedBranchMembers8830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8830
  · have he : independentCachedBranchMembers8832.filter (independentCachedEdge 1622)=independentCachedBranchMembers8831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8831
def independentCachedBranchMembers8833 : Finset ℕ := ([1590,1594,1596,1614,1678,1776,3072,3186,3188,3192,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8833 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8833 4 (fun x => (if x<3188 then (if x<1678 then (if x<1596 then (if x<1594 then 0 else 1) else (if x<1614 then 2 else 0)) else (if x<3072 then (if x<1776 then 1 else 2) else (if x<3186 then 3 else 1))) else (if x<3256 then (if x<3250 then (if x<3192 then 2 else 3) else (if x<3252 then 0 else 3)) else (if x<3274 then (if x<3270 then 2 else 1) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8834 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8834 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8834 1582 4
  · have he : independentCachedBranchMembers8834.erase 1582=independentCachedBranchMembers8832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8832
  · have he : independentCachedBranchMembers8834.filter (independentCachedEdge 1582)=independentCachedBranchMembers8833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8833
def independentCachedBranchMembers8835 : Finset ℕ := ([36,40,48,66,72,80,130,132,144,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2560,2590,2662,2666,2668,2674,2676,2680,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8835 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8835 2560 5
  · have he : independentCachedBranchMembers8835.erase 2560=independentCachedBranchMembers8817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8817
  · have he : independentCachedBranchMembers8835.filter (independentCachedEdge 2560)=independentCachedBranchMembers8834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8834
def independentCachedBranchMembers8836 : Finset ℕ := ([144,252,1594,1596,1622,1628,1686,1690,1692,1776,2590,2676,2738,2744,2772,2776,3102,3186,3192,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8836 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8836 5 (fun x => (if x<2738 then (if x<1686 then (if x<1596 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1622 then 2 else (if x<1628 then 1 else 3))) else (if x<1776 then (if x<1690 then 2 else (if x<1692 then 3 else 0)) else (if x<2590 then 0 else (if x<2676 then 1 else 3)))) else (if x<3192 then (if x<2776 then (if x<2744 then 3 else (if x<2772 then 0 else 0)) else (if x<3102 then 3 else (if x<3186 then 2 else 4))) else (if x<3282 then (if x<3252 then 2 else (if x<3256 then 0 else 4)) else (if x<3284 then 2 else (if x<3288 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8837 : Finset ℕ := ([252,1594,1628,1692,2738,2772,2776,3102,3192,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8837 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8837 4 (fun x => (if x<2776 then (if x<1692 then (if x<1594 then 0 else (if x<1628 then 1 else 0)) else (if x<2738 then 1 else (if x<2772 then 2 else 0))) else (if x<3252 then (if x<3102 then 2 else (if x<3192 then 1 else 3)) else (if x<3256 then 3 else (if x<3282 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8838 : Finset ℕ := ([144,252,1594,1596,1622,1628,1686,1690,1692,1776,2590,2676,2738,2744,2770,2772,2776,3102,3186,3192,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8838 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8838 2770 4
  · have he : independentCachedBranchMembers8838.erase 2770=independentCachedBranchMembers8836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8836
  · have he : independentCachedBranchMembers8838.filter (independentCachedEdge 2770)=independentCachedBranchMembers8837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8837
def independentCachedBranchMembers8839 : Finset ℕ := ([144,1622,1690,1692,2676,2744,2776,3102,3192,3252,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8839 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8839 4 (fun x => (if x<2776 then (if x<1692 then (if x<1622 then 0 else (if x<1690 then 1 else 0)) else (if x<2676 then 1 else (if x<2744 then 2 else 0))) else (if x<3252 then (if x<3102 then 2 else (if x<3192 then 1 else 2)) else (if x<3282 then 3 else (if x<3284 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8840 : Finset ℕ := ([144,252,1594,1596,1622,1628,1686,1690,1692,1776,2590,2676,2680,2738,2744,2770,2772,2776,3102,3186,3192,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8840 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8840 2680 4
  · have he : independentCachedBranchMembers8840.erase 2680=independentCachedBranchMembers8838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8838
  · have he : independentCachedBranchMembers8840.filter (independentCachedEdge 2680)=independentCachedBranchMembers8839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8839
def independentCachedBranchMembers8841 : Finset ℕ := ([144,252,1594,1622,1628,1690,2676,2738,2744,2772,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8841 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8841 4 (fun x => (if x<2676 then (if x<1622 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1628 then 1 else (if x<1690 then 2 else 2))) else (if x<2772 then (if x<2738 then 2 else (if x<2744 then 2 else 0)) else (if x<3256 then 0 else (if x<3284 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8842 : Finset ℕ := ([144,252,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2676,2680,2738,2744,2770,2772,2776,3102,3186,3192,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8842 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8842 1626 4
  · have he : independentCachedBranchMembers8842.erase 1626=independentCachedBranchMembers8840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8840
  · have he : independentCachedBranchMembers8842.filter (independentCachedEdge 1626)=independentCachedBranchMembers8841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8841
def independentCachedBranchMembers8843 : Finset ℕ := ([252,1596,1622,1628,1686,1692,2590,2676,2772,3102,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8843 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8843 4 (fun x => (if x<2590 then (if x<1628 then (if x<1596 then 0 else (if x<1622 then 0 else 1)) else (if x<1686 then 2 else (if x<1692 then 2 else 1))) else (if x<3102 then (if x<2676 then 1 else (if x<2772 then 0 else 1)) else (if x<3252 then 2 else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8844 : Finset ℕ := ([144,250,252,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2676,2680,2738,2744,2770,2772,2776,3102,3186,3192,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8844 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8844 250 4
  · have he : independentCachedBranchMembers8844.erase 250=independentCachedBranchMembers8842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8842
  · have he : independentCachedBranchMembers8844.filter (independentCachedEdge 250)=independentCachedBranchMembers8843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8843
def independentCachedBranchMembers8845 : Finset ℕ := ([144,1594,1596,1686,1690,1692,2590,2738,2744,3102,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8845 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8845 4 (fun x => (if x<2590 then (if x<1686 then (if x<1594 then 0 else (if x<1596 then 1 else 2)) else (if x<1690 then 0 else (if x<1692 then 2 else 1))) else (if x<3102 then (if x<2738 then 1 else (if x<2744 then 0 else 1)) else (if x<3252 then 2 else (if x<3256 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8846 : Finset ℕ := ([80,144,250,252,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2676,2680,2738,2744,2770,2772,2776,3102,3186,3192,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8846 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8846 80 4
  · have he : independentCachedBranchMembers8846.erase 80=independentCachedBranchMembers8844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8844
  · have he : independentCachedBranchMembers8846.filter (independentCachedEdge 80)=independentCachedBranchMembers8845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8845
def independentCachedBranchMembers8847 : Finset ℕ := ([252,1596,1622,1626,1692,2590,2676,2680,2738,2772,2776,3186,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8847 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8847 4 (fun x => (if x<2680 then (if x<1626 then (if x<1596 then 0 else (if x<1622 then 0 else 1)) else (if x<2590 then (if x<1692 then 2 else 1) else (if x<2676 then 1 else 0))) else (if x<3186 then (if x<2772 then (if x<2738 then 2 else 3) else (if x<2776 then 1 else 3)) else (if x<3256 then (if x<3252 then 2 else 0) else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8848 : Finset ℕ := ([1596,1692,2590,2738,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8848 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8848 3 (fun x => (if x<2738 then (if x<1692 then 0 else (if x<2590 then 1 else 0)) else (if x<3252 then 2 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8849 : Finset ℕ := ([80,252,1596,1622,1626,1692,2590,2676,2680,2738,2772,2776,3186,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8849 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8849 80 3
  · have he : independentCachedBranchMembers8849.erase 80=independentCachedBranchMembers8847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8847
  · have he : independentCachedBranchMembers8849.filter (independentCachedEdge 80)=independentCachedBranchMembers8848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8848
def independentCachedBranchMembers8850 : Finset ℕ := ([80,144,250,252,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2676,2680,2738,2744,2770,2772,2776,3102,3186,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8850 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8850 3250 4
  · have he : independentCachedBranchMembers8850.erase 3250=independentCachedBranchMembers8846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8846
  · have he : independentCachedBranchMembers8850.filter (independentCachedEdge 3250)=independentCachedBranchMembers8849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8849
def independentCachedBranchMembers8851 : Finset ℕ := ([250,1594,1626,1686,1692,2590,2676,2738,2744,2770,2776,3186,3192,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8851 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8851 4 (fun x => (if x<2738 then (if x<1686 then (if x<1594 then 0 else (if x<1626 then 0 else 1)) else (if x<2590 then (if x<1692 then 1 else 2) else (if x<2676 then 1 else 3))) else (if x<3186 then (if x<2770 then (if x<2744 then 0 else 2) else (if x<2776 then 1 else 3)) else (if x<3252 then (if x<3192 then 0 else 3) else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8852 : Finset ℕ := ([1594,1626,2590,2676,3186,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8852 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8852 3 (fun x => (if x<2676 then (if x<1626 then 0 else (if x<2590 then 1 else 0)) else (if x<3186 then 2 else (if x<3192 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8853 : Finset ℕ := ([144,250,1594,1626,1686,1692,2590,2676,2738,2744,2770,2776,3186,3192,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8853 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8853 144 3
  · have he : independentCachedBranchMembers8853.erase 144=independentCachedBranchMembers8851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8851
  · have he : independentCachedBranchMembers8853.filter (independentCachedEdge 144)=independentCachedBranchMembers8852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8852
def independentCachedBranchMembers8854 : Finset ℕ := ([80,144,250,252,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2676,2680,2738,2744,2770,2772,2776,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8854 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8854 3188 4
  · have he : independentCachedBranchMembers8854.erase 3188=independentCachedBranchMembers8850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8850
  · have he : independentCachedBranchMembers8854.filter (independentCachedEdge 3188)=independentCachedBranchMembers8853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8853
def independentCachedBranchMembers8855 : Finset ℕ := ([80,250,1594,1622,1628,1690,2676,2738,2744,2772,3102,3186,3192,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8855 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8855 4 (fun x => (if x<2744 then (if x<1628 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1622 then 1 else 1)) else (if x<2676 then (if x<1690 then 2 else 2) else (if x<2738 then 2 else 2))) else (if x<3192 then (if x<3102 then (if x<2772 then 1 else 1) else (if x<3186 then 3 else 0)) else (if x<3282 then (if x<3252 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8856 : Finset ℕ := ([80,144,250,252,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2676,2680,2738,2740,2744,2770,2772,2776,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8856 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8856 2740 4
  · have he : independentCachedBranchMembers8856.erase 2740=independentCachedBranchMembers8854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8854
  · have he : independentCachedBranchMembers8856.filter (independentCachedEdge 2740)=independentCachedBranchMembers8855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8855
def independentCachedBranchMembers8857 : Finset ℕ := ([144,252,1596,1628,1686,1690,2676,2680,2738,2770,3102,3186,3252,3256,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8857 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8857 4 (fun x => (if x<2738 then (if x<1686 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1628 then 1 else 2)) else (if x<2676 then (if x<1690 then 1 else 2) else (if x<2680 then 2 else 1))) else (if x<3252 then (if x<3102 then (if x<2770 then 2 else 1) else (if x<3186 then 3 else 3)) else (if x<3284 then (if x<3256 then 0 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8858 : Finset ℕ := ([80,144,250,252,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2674,2676,2680,2738,2740,2744,2770,2772,2776,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8858 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8858 2674 4
  · have he : independentCachedBranchMembers8858.erase 2674=independentCachedBranchMembers8856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8856
  · have he : independentCachedBranchMembers8858.filter (independentCachedEdge 2674)=independentCachedBranchMembers8857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8857
def independentCachedBranchMembers8859 : Finset ℕ := ([80,144,250,252,1594,1596,1622,1686,2680,2744,2770,2772,3192,3256,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8859 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8859 4 (fun x => (if x<2680 then (if x<1594 then (if x<250 then (if x<144 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1622 then (if x<1596 then 2 else 3) else (if x<1686 then 2 else 3))) else (if x<3192 then (if x<2770 then (if x<2744 then 0 else 1) else (if x<2772 then 0 else 1)) else (if x<3282 then (if x<3256 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8860 : Finset ℕ := ([80,144,250,252,1590,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2674,2676,2680,2738,2740,2744,2770,2772,2776,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8860 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8860 1590 4
  · have he : independentCachedBranchMembers8860.erase 1590=independentCachedBranchMembers8858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8858
  · have he : independentCachedBranchMembers8860.filter (independentCachedEdge 1590)=independentCachedBranchMembers8859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8859
def independentCachedBranchMembers8861 : Finset ℕ := ([250,252,1594,1596,1626,1628,1690,1692,2590,2680,2744,2776,3102,3192,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8861 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8861 4 (fun x => (if x<2590 then (if x<1626 then (if x<1594 then (if x<252 then 0 else 1) else (if x<1596 then 0 else 1)) else (if x<1690 then (if x<1628 then 2 else 3) else (if x<1692 then 3 else 2))) else (if x<3102 then (if x<2744 then (if x<2680 then 2 else 0) else (if x<2776 then 1 else 2)) else (if x<3256 then (if x<3192 then 3 else 1) else (if x<3288 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8862 : Finset ℕ := ([80,144,246,250,252,1590,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2674,2676,2680,2738,2740,2744,2770,2772,2776,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8862 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8862 246 4
  · have he : independentCachedBranchMembers8862.erase 246=independentCachedBranchMembers8860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8860
  · have he : independentCachedBranchMembers8862.filter (independentCachedEdge 246)=independentCachedBranchMembers8861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8861
def independentCachedBranchMembers8863 : Finset ℕ := ([80,144,1622,1626,1628,1686,1690,1692,2590,2770,2772,2776,3102,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8863 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8863 4 (fun x => (if x<2590 then (if x<1628 then (if x<1622 then (if x<144 then 0 else 1) else (if x<1626 then 0 else 2)) else (if x<1690 then (if x<1686 then 3 else 1) else (if x<1692 then 3 else 2))) else (if x<3102 then (if x<2772 then (if x<2770 then 2 else 0) else (if x<2776 then 1 else 2)) else (if x<3284 then (if x<3282 then 3 else 1) else (if x<3288 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
