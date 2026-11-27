/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch190
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8896 : Finset ℕ := ([1678,1692,2590,2770,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound8896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8896 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8896 3 (fun x => (if x<2770 then (if x<1692 then 0 else (if x<2590 then 1 else 0)) else (if x<3186 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8897 : Finset ℕ := ([72,132,1590,1678,1692,1768,2590,2666,2680,2726,2740,2770,3186,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8897 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8897 72 3
  · have he : independentCachedBranchMembers8897.erase 72=independentCachedBranchMembers8895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8895
  · have he : independentCachedBranchMembers8897.filter (independentCachedEdge 72)=independentCachedBranchMembers8896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8896
def independentCachedBranchMembers8898 : Finset ℕ := ([72,80,132,250,1582,1590,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2740,2770,2776,3102,3178,3186,3192,3238,3244,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8898 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8898 3282 4
  · have he : independentCachedBranchMembers8898.erase 3282=independentCachedBranchMembers8894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8894
  · have he : independentCachedBranchMembers8898.filter (independentCachedEdge 3282)=independentCachedBranchMembers8897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8897
def independentCachedBranchMembers8899 : Finset ℕ := ([250,1582,1678,1762,1768,2590,2674,2680,2740,2770,2776,3178,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8899 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8899 4 (fun x => (if x<2680 then (if x<1762 then (if x<1582 then 0 else (if x<1678 then 1 else 2)) else (if x<2590 then (if x<1768 then 0 else 1) else (if x<2674 then 1 else 0))) else (if x<3178 then (if x<2770 then (if x<2740 then 2 else 3) else (if x<2776 then 3 else 1)) else (if x<3244 then (if x<3238 then 0 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8900 : Finset ℕ := ([1762,1768,2590,2740,3178,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8900 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8900 3 (fun x => (if x<2740 then (if x<1768 then 0 else (if x<2590 then 1 else 0)) else (if x<3178 then 2 else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8901 : Finset ℕ := ([80,250,1582,1678,1762,1768,2590,2674,2680,2740,2770,2776,3178,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8901 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8901 80 3
  · have he : independentCachedBranchMembers8901.erase 80=independentCachedBranchMembers8899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8899
  · have he : independentCachedBranchMembers8901.filter (independentCachedEdge 80)=independentCachedBranchMembers8900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8900
def independentCachedBranchMembers8902 : Finset ℕ := ([72,80,132,250,1582,1590,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2740,2770,2776,3102,3178,3186,3192,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8902 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8902 3252 4
  · have he : independentCachedBranchMembers8902.erase 3252=independentCachedBranchMembers8898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8898
  · have he : independentCachedBranchMembers8902.filter (independentCachedEdge 3252)=independentCachedBranchMembers8901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8901
def independentCachedBranchMembers8903 : Finset ℕ := ([80,132,1582,1686,1692,1776,2666,2740,2770,2776,3102,3186,3192,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8903 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8903 4 (fun x => (if x<2770 then (if x<1692 then (if x<1582 then (if x<132 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2666 then (if x<1776 then 2 else 2) else (if x<2740 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2776 then 1 else 2) else (if x<3186 then 3 else 0)) else (if x<3244 then (if x<3238 then 3 else 0) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8904 : Finset ℕ := ([72,80,132,250,1582,1590,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2740,2762,2770,2776,3102,3178,3186,3192,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8904 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8904 2762 4
  · have he : independentCachedBranchMembers8904.erase 2762=independentCachedBranchMembers8902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8902
  · have he : independentCachedBranchMembers8904.filter (independentCachedEdge 2762)=independentCachedBranchMembers8903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8903
def independentCachedBranchMembers8905 : Finset ℕ := ([72,250,1590,1686,1762,1776,2674,2726,2740,2770,3102,3178,3192,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8905 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8905 4 (fun x => (if x<2740 then (if x<1762 then (if x<1590 then (if x<250 then 0 else 0) else (if x<1686 then 1 else 2)) else (if x<2674 then (if x<1776 then 1 else 2) else (if x<2726 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2770 then 2 else 2) else (if x<3178 then 3 else 0)) else (if x<3274 then (if x<3244 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8906 : Finset ℕ := ([72,80,132,250,1582,1590,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2732,2740,2762,2770,2776,3102,3178,3186,3192,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8906 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8906 2732 4
  · have he : independentCachedBranchMembers8906.erase 2732=independentCachedBranchMembers8904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8904
  · have he : independentCachedBranchMembers8906.filter (independentCachedEdge 2732)=independentCachedBranchMembers8905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8905
def independentCachedBranchMembers8907 : Finset ℕ := ([72,80,132,250,1582,1590,1692,1762,2666,2674,2726,2776,3178,3186,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8907 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8907 4 (fun x => (if x<2666 then (if x<1582 then (if x<132 then (if x<80 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1692 then (if x<1590 then 2 else 3) else (if x<1762 then 2 else 3))) else (if x<3178 then (if x<2726 then (if x<2674 then 0 else 1) else (if x<2776 then 0 else 1)) else (if x<3238 then (if x<3186 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8908 : Finset ℕ := ([72,80,132,250,1582,1590,1596,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2732,2740,2762,2770,2776,3102,3178,3186,3192,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8908 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8908 1596 4
  · have he : independentCachedBranchMembers8908.erase 1596=independentCachedBranchMembers8906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8906
  · have he : independentCachedBranchMembers8908.filter (independentCachedEdge 1596)=independentCachedBranchMembers8907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8907
def independentCachedBranchMembers8909 : Finset ℕ := ([72,80,1582,1590,1678,1686,1768,1776,2590,2680,2726,2776,3102,3192,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8909 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8909 4 (fun x => (if x<2590 then (if x<1678 then (if x<1582 then (if x<80 then 0 else 1) else (if x<1590 then 1 else 0)) else (if x<1768 then (if x<1686 then 2 else 3) else (if x<1776 then 2 else 3))) else (if x<3102 then (if x<2726 then (if x<2680 then 2 else 2) else (if x<2776 then 0 else 1)) else (if x<3238 then (if x<3192 then 3 else 3) else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8910 : Finset ℕ := ([66,72,80,132,250,1582,1590,1596,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2732,2740,2762,2770,2776,3102,3178,3186,3192,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8910 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8910 66 4
  · have he : independentCachedBranchMembers8910.erase 66=independentCachedBranchMembers8908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8908
  · have he : independentCachedBranchMembers8910.filter (independentCachedEdge 66)=independentCachedBranchMembers8909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8909
def independentCachedBranchMembers8911 : Finset ℕ := ([132,250,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,3102,3178,3186,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8911 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8911 4 (fun x => (if x<2590 then (if x<1692 then (if x<1678 then (if x<250 then 0 else 1) else (if x<1686 then 0 else 2)) else (if x<1768 then (if x<1762 then 3 else 1) else (if x<1776 then 3 else 2))) else (if x<3102 then (if x<2674 then (if x<2666 then 2 else 1) else (if x<2680 then 0 else 2)) else (if x<3186 then (if x<3178 then 3 else 3) else (if x<3192 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8912 : Finset ℕ := ([36,66,72,80,132,250,1582,1590,1596,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2732,2740,2762,2770,2776,3102,3178,3186,3192,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8912 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8912 36 4
  · have he : independentCachedBranchMembers8912.erase 36=independentCachedBranchMembers8910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8910
  · have he : independentCachedBranchMembers8912.filter (independentCachedEdge 36)=independentCachedBranchMembers8911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8911
def independentCachedBranchMembers8913 : Finset ℕ := ([36,40,48,66,68,72,80,130,132,136,144,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2560,2590,2662,2666,2668,2674,2676,2680,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8913 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8913 68 5
  · have he : independentCachedBranchMembers8913.erase 68=independentCachedBranchMembers8889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8889
  · have he : independentCachedBranchMembers8913.filter (independentCachedEdge 68)=independentCachedBranchMembers8912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8912
def independentCachedBranchMembers8914 : Finset ℕ := ([48,252,1596,1614,1622,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2740,2744,2758,2770,3102,3180,3188,3192,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8914 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8914 5 (fun x => (if x<2676 then (if x<1686 then (if x<1614 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1622 then 1 else (if x<1678 then 2 else 2))) else (if x<1768 then (if x<1690 then 1 else (if x<1764 then 3 else 1)) else (if x<2590 then (if x<1776 then 3 else 0) else (if x<2668 then 1 else 1)))) else (if x<3180 then (if x<2744 then (if x<2680 then 0 else (if x<2740 then 4 else 1)) else (if x<2770 then (if x<2758 then 0 else 1) else (if x<3102 then 4 else 2))) else (if x<3244 then (if x<3188 then 3 else (if x<3192 then 2 else 0)) else (if x<3270 then (if x<3256 then 2 else 3) else (if x<3274 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8915 : Finset ℕ := ([252,1614,1622,1764,1768,1776,2590,2740,2744,3102,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8915 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8915 4 (fun x => (if x<2590 then (if x<1764 then (if x<1614 then 0 else (if x<1622 then 1 else 2)) else (if x<1768 then 0 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2740 then 1 else (if x<2744 then 0 else 1)) else (if x<3244 then 2 else (if x<3256 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8916 : Finset ℕ := ([48,130,252,1596,1614,1622,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2740,2744,2758,2770,3102,3180,3188,3192,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8916 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8916 130 4
  · have he : independentCachedBranchMembers8916.erase 130=independentCachedBranchMembers8914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8914
  · have he : independentCachedBranchMembers8916.filter (independentCachedEdge 130)=independentCachedBranchMembers8915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8915
def independentCachedBranchMembers8917 : Finset ℕ := ([48,1614,1678,1690,1764,1776,2590,2676,2740,3102,3188,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8917 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8917 4 (fun x => (if x<2590 then (if x<1690 then (if x<1614 then 0 else (if x<1678 then 0 else 1)) else (if x<1764 then 2 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2676 then 1 else (if x<2740 then 1 else 0)) else (if x<3188 then 2 else (if x<3274 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8918 : Finset ℕ := ([40,48,130,252,1596,1614,1622,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2740,2744,2758,2770,3102,3180,3188,3192,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8918 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8918 40 4
  · have he : independentCachedBranchMembers8918.erase 40=independentCachedBranchMembers8916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8916
  · have he : independentCachedBranchMembers8918.filter (independentCachedEdge 40)=independentCachedBranchMembers8917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8917
def independentCachedBranchMembers8919 : Finset ℕ := ([252,1614,1678,1764,1768,2590,2676,2680,2740,2744,2770,3180,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8919 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8919 4 (fun x => (if x<2680 then (if x<1764 then (if x<1614 then 0 else (if x<1678 then 1 else 2)) else (if x<2590 then (if x<1768 then 0 else 1) else (if x<2676 then 1 else 0))) else (if x<3180 then (if x<2744 then (if x<2740 then 2 else 3) else (if x<2770 then 1 else 3)) else (if x<3270 then (if x<3244 then 0 else 3) else (if x<3274 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8920 : Finset ℕ := ([1764,1768,2590,2770,3180,3244] : List ℕ).toFinset
theorem independentCachedBranchBound8920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8920 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8920 3 (fun x => (if x<2770 then (if x<1768 then 0 else (if x<2590 then 1 else 0)) else (if x<3180 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8921 : Finset ℕ := ([48,252,1614,1678,1764,1768,2590,2676,2680,2740,2744,2770,3180,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8921 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8921 48 3
  · have he : independentCachedBranchMembers8921.erase 48=independentCachedBranchMembers8919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8919
  · have he : independentCachedBranchMembers8921.filter (independentCachedEdge 48)=independentCachedBranchMembers8920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8920
def independentCachedBranchMembers8922 : Finset ℕ := ([40,48,130,252,1596,1614,1622,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2740,2744,2758,2770,3102,3180,3188,3192,3244,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8922 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8922 3282 4
  · have he : independentCachedBranchMembers8922.erase 3282=independentCachedBranchMembers8918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8918
  · have he : independentCachedBranchMembers8922.filter (independentCachedEdge 3282)=independentCachedBranchMembers8921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8921
def independentCachedBranchMembers8923 : Finset ℕ := ([130,1622,1678,1690,1768,2590,2668,2680,2740,2758,2770,3188,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8923 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8923 4 (fun x => (if x<2680 then (if x<1690 then (if x<1622 then 0 else (if x<1678 then 1 else 0)) else (if x<2590 then (if x<1768 then 1 else 2) else (if x<2668 then 1 else 2))) else (if x<3188 then (if x<2758 then (if x<2740 then 0 else 3) else (if x<2770 then 3 else 1)) else (if x<3256 then (if x<3244 then 0 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8924 : Finset ℕ := ([1678,1690,2590,2740,3188,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8924 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8924 3 (fun x => (if x<2740 then (if x<1690 then 0 else (if x<2590 then 1 else 0)) else (if x<3188 then 2 else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8925 : Finset ℕ := ([40,130,1622,1678,1690,1768,2590,2668,2680,2740,2758,2770,3188,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8925 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8925 40 3
  · have he : independentCachedBranchMembers8925.erase 40=independentCachedBranchMembers8923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8923
  · have he : independentCachedBranchMembers8925.filter (independentCachedEdge 40)=independentCachedBranchMembers8924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8924
def independentCachedBranchMembers8926 : Finset ℕ := ([40,48,130,252,1596,1614,1622,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2740,2744,2758,2770,3102,3180,3188,3192,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8926 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8926 3252 4
  · have he : independentCachedBranchMembers8926.erase 3252=independentCachedBranchMembers8922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8922
  · have he : independentCachedBranchMembers8926.filter (independentCachedEdge 3252)=independentCachedBranchMembers8925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8925
def independentCachedBranchMembers8927 : Finset ℕ := ([40,252,1622,1686,1764,1776,2676,2740,2758,2770,3102,3180,3192,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8927 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8927 4 (fun x => (if x<2758 then (if x<1764 then (if x<1622 then (if x<252 then 0 else 0) else (if x<1686 then 1 else 2)) else (if x<2676 then (if x<1776 then 1 else 2) else (if x<2740 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2770 then 1 else 2) else (if x<3180 then 3 else 0)) else (if x<3256 then (if x<3244 then 3 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
