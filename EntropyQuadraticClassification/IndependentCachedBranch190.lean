/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch189
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8864 : Finset ℕ := ([48,80,144,246,250,252,1590,1594,1596,1622,1626,1628,1686,1690,1692,1776,2590,2674,2676,2680,2738,2740,2744,2770,2772,2776,3102,3186,3188,3192,3250,3252,3256,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8864 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8864 48 4
  · have he : independentCachedBranchMembers8864.erase 48=independentCachedBranchMembers8862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8862
  · have he : independentCachedBranchMembers8864.filter (independentCachedEdge 48)=independentCachedBranchMembers8863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8863
def independentCachedBranchMembers8865 : Finset ℕ := ([36,40,48,66,72,80,130,132,144,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2560,2590,2662,2666,2668,2674,2676,2680,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8865 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8865 238 5
  · have he : independentCachedBranchMembers8865.erase 238=independentCachedBranchMembers8835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8835
  · have he : independentCachedBranchMembers8865.filter (independentCachedEdge 238)=independentCachedBranchMembers8864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8864
def independentCachedBranchMembers8866 : Finset ℕ := ([144,246,1582,1594,1614,1626,1628,1686,1762,1764,1776,2590,2666,2680,2726,2738,2740,2770,2772,3102,3178,3180,3238,3250,3252,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8866 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8866 5 (fun x => (if x<2680 then (if x<1628 then (if x<1594 then (if x<246 then 0 else (if x<1582 then 0 else 1)) else (if x<1614 then 2 else (if x<1626 then 2 else 1))) else (if x<1764 then (if x<1686 then 3 else (if x<1762 then 0 else 1)) else (if x<2590 then (if x<1776 then 3 else 0) else (if x<2666 then 1 else 1)))) else (if x<3178 then (if x<2740 then (if x<2726 then 4 else (if x<2738 then 1 else 0)) else (if x<2772 then (if x<2770 then 4 else 1) else (if x<3102 then 0 else 2))) else (if x<3250 then (if x<3180 then 2 else (if x<3238 then 3 else 3)) else (if x<3270 then (if x<3252 then 2 else 0) else (if x<3284 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8867 : Finset ℕ := ([144,1582,1614,1628,1762,1776,2590,2738,2770,3102,3180,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8867 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8867 4 (fun x => (if x<2590 then (if x<1628 then (if x<1582 then 0 else (if x<1614 then 0 else 1)) else (if x<1762 then 2 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2738 then 1 else (if x<2770 then 1 else 0)) else (if x<3180 then 2 else (if x<3250 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8868 : Finset ℕ := ([132,144,246,1582,1594,1614,1626,1628,1686,1762,1764,1776,2590,2666,2680,2726,2738,2740,2770,2772,3102,3178,3180,3238,3250,3252,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8868 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8868 132 4
  · have he : independentCachedBranchMembers8868.erase 132=independentCachedBranchMembers8866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8866
  · have he : independentCachedBranchMembers8868.filter (independentCachedEdge 132)=independentCachedBranchMembers8867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8867
def independentCachedBranchMembers8869 : Finset ℕ := ([246,1582,1594,1762,1764,1776,2590,2770,2772,3102,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8869 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8869 4 (fun x => (if x<2590 then (if x<1762 then (if x<1582 then 0 else (if x<1594 then 1 else 2)) else (if x<1764 then 0 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2770 then 1 else (if x<2772 then 0 else 1)) else (if x<3270 then 2 else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8870 : Finset ℕ := ([72,132,144,246,1582,1594,1614,1626,1628,1686,1762,1764,1776,2590,2666,2680,2726,2738,2740,2770,2772,3102,3178,3180,3238,3250,3252,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8870 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8870 72 4
  · have he : independentCachedBranchMembers8870.erase 72=independentCachedBranchMembers8868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8868
  · have he : independentCachedBranchMembers8870.filter (independentCachedEdge 72)=independentCachedBranchMembers8869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8869
def independentCachedBranchMembers8871 : Finset ℕ := ([132,1594,1614,1628,1764,2590,2666,2680,2726,2740,2770,3180,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8871 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8871 4 (fun x => (if x<2680 then (if x<1628 then (if x<1594 then 0 else (if x<1614 then 0 else 1)) else (if x<2590 then (if x<1764 then 2 else 1) else (if x<2666 then 1 else 0))) else (if x<3180 then (if x<2740 then (if x<2726 then 2 else 3) else (if x<2770 then 1 else 3)) else (if x<3270 then (if x<3250 then 2 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8872 : Finset ℕ := ([1594,1764,2590,2770,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8872 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8872 3 (fun x => (if x<2770 then (if x<1764 then 0 else (if x<2590 then 1 else 0)) else (if x<3270 then 2 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8873 : Finset ℕ := ([72,132,1594,1614,1628,1764,2590,2666,2680,2726,2740,2770,3180,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8873 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8873 72 3
  · have he : independentCachedBranchMembers8873.erase 72=independentCachedBranchMembers8871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8871
  · have he : independentCachedBranchMembers8873.filter (independentCachedEdge 72)=independentCachedBranchMembers8872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8872
def independentCachedBranchMembers8874 : Finset ℕ := ([72,132,144,246,1582,1594,1614,1626,1628,1686,1762,1764,1776,2590,2666,2680,2726,2738,2740,2770,2772,3102,3178,3180,3238,3250,3252,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8874 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8874 3282 4
  · have he : independentCachedBranchMembers8874.erase 3282=independentCachedBranchMembers8870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8870
  · have he : independentCachedBranchMembers8874.filter (independentCachedEdge 3282)=independentCachedBranchMembers8873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8873
def independentCachedBranchMembers8875 : Finset ℕ := ([246,1582,1614,1762,1764,2590,2680,2738,2740,2770,2772,3178,3180,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8875 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8875 4 (fun x => (if x<2738 then (if x<1762 then (if x<1582 then 0 else (if x<1614 then 1 else 2)) else (if x<2590 then (if x<1764 then 0 else 1) else (if x<2680 then 1 else 3))) else (if x<3178 then (if x<2770 then (if x<2740 then 0 else 2) else (if x<2772 then 3 else 1)) else (if x<3238 then (if x<3180 then 2 else 3) else (if x<3270 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8876 : Finset ℕ := ([1762,1764,2590,2680,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8876 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8876 3 (fun x => (if x<2680 then (if x<1764 then 0 else (if x<2590 then 1 else 0)) else (if x<3238 then 2 else (if x<3270 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8877 : Finset ℕ := ([144,246,1582,1614,1762,1764,2590,2680,2738,2740,2770,2772,3178,3180,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8877 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8877 144 3
  · have he : independentCachedBranchMembers8877.erase 144=independentCachedBranchMembers8875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8875
  · have he : independentCachedBranchMembers8877.filter (independentCachedEdge 144)=independentCachedBranchMembers8876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8876
def independentCachedBranchMembers8878 : Finset ℕ := ([72,132,144,246,1582,1594,1614,1626,1628,1686,1762,1764,1776,2590,2666,2680,2726,2738,2740,2770,2772,3102,3178,3180,3192,3238,3250,3252,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8878 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8878 3192 4
  · have he : independentCachedBranchMembers8878.erase 3192=independentCachedBranchMembers8874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8874
  · have he : independentCachedBranchMembers8878.filter (independentCachedEdge 3192)=independentCachedBranchMembers8877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8877
def independentCachedBranchMembers8879 : Finset ℕ := ([72,144,1582,1626,1628,1776,2680,2726,2770,2772,3102,3178,3180,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8879 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8879 4 (fun x => (if x<2770 then (if x<1628 then (if x<1582 then (if x<144 then 0 else 0) else (if x<1626 then 1 else 1)) else (if x<2680 then (if x<1776 then 2 else 2) else (if x<2726 then 2 else 1))) else (if x<3180 then (if x<3102 then (if x<2772 then 1 else 2) else (if x<3178 then 3 else 0)) else (if x<3252 then (if x<3250 then 3 else 0) else (if x<3270 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8880 : Finset ℕ := ([72,132,144,246,1582,1594,1614,1626,1628,1686,1762,1764,1776,2590,2666,2680,2726,2738,2740,2758,2770,2772,3102,3178,3180,3192,3238,3250,3252,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8880 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8880 2758 4
  · have he : independentCachedBranchMembers8880.erase 2758=independentCachedBranchMembers8878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8878
  · have he : independentCachedBranchMembers8880.filter (independentCachedEdge 2758)=independentCachedBranchMembers8879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8879
def independentCachedBranchMembers8881 : Finset ℕ := ([132,246,1594,1626,1762,1776,2666,2680,2738,2770,3102,3180,3238,3252,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8881 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8881 4 (fun x => (if x<2738 then (if x<1762 then (if x<1594 then (if x<246 then 0 else 0) else (if x<1626 then 1 else 2)) else (if x<2666 then (if x<1776 then 1 else 2) else (if x<2680 then 1 else 2))) else (if x<3238 then (if x<3102 then (if x<2770 then 1 else 2) else (if x<3180 then 3 else 3)) else (if x<3270 then (if x<3252 then 0 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8882 : Finset ℕ := ([72,132,144,246,1582,1594,1614,1626,1628,1686,1762,1764,1776,2590,2666,2668,2680,2726,2738,2740,2758,2770,2772,3102,3178,3180,3192,3238,3250,3252,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8882 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8882 2668 4
  · have he : independentCachedBranchMembers8882.erase 2668=independentCachedBranchMembers8880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8880
  · have he : independentCachedBranchMembers8882.filter (independentCachedEdge 2668)=independentCachedBranchMembers8881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8881
def independentCachedBranchMembers8883 : Finset ℕ := ([72,132,144,246,1582,1594,1628,1762,2666,2726,2738,2772,3178,3238,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8883 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8883 4 (fun x => (if x<2666 then (if x<1582 then (if x<144 then (if x<132 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1628 then (if x<1594 then 2 else 3) else (if x<1762 then 2 else 3))) else (if x<3178 then (if x<2738 then (if x<2726 then 0 else 0) else (if x<2772 then 1 else 1)) else (if x<3250 then (if x<3238 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8884 : Finset ℕ := ([72,132,144,246,1582,1594,1596,1614,1626,1628,1686,1762,1764,1776,2590,2666,2668,2680,2726,2738,2740,2758,2770,2772,3102,3178,3180,3192,3238,3250,3252,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8884 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8884 1596 4
  · have he : independentCachedBranchMembers8884.erase 1596=independentCachedBranchMembers8882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8882
  · have he : independentCachedBranchMembers8884.filter (independentCachedEdge 1596)=independentCachedBranchMembers8883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8883
def independentCachedBranchMembers8885 : Finset ℕ := ([132,144,1582,1594,1614,1626,1764,1776,2590,2666,2740,2772,3102,3178,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8885 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8885 4 (fun x => (if x<2590 then (if x<1614 then (if x<1582 then (if x<144 then 0 else 1) else (if x<1594 then 1 else 0)) else (if x<1764 then (if x<1626 then 2 else 3) else (if x<1776 then 2 else 3))) else (if x<3102 then (if x<2740 then (if x<2666 then 2 else 0) else (if x<2772 then 2 else 1)) else (if x<3252 then (if x<3178 then 3 else 1) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8886 : Finset ℕ := ([72,130,132,144,246,1582,1594,1596,1614,1626,1628,1686,1762,1764,1776,2590,2666,2668,2680,2726,2738,2740,2758,2770,2772,3102,3178,3180,3192,3238,3250,3252,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8886 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8886 130 4
  · have he : independentCachedBranchMembers8886.erase 130=independentCachedBranchMembers8884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8884
  · have he : independentCachedBranchMembers8886.filter (independentCachedEdge 130)=independentCachedBranchMembers8885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8885
def independentCachedBranchMembers8887 : Finset ℕ := ([72,246,1614,1626,1628,1762,1764,1776,2590,2726,2738,2740,3102,3238,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8887 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8887 4 (fun x => (if x<2590 then (if x<1628 then (if x<1614 then (if x<246 then 0 else 1) else (if x<1626 then 0 else 2)) else (if x<1764 then (if x<1762 then 3 else 1) else (if x<1776 then 3 else 2))) else (if x<3102 then (if x<2738 then (if x<2726 then 2 else 1) else (if x<2740 then 0 else 2)) else (if x<3250 then (if x<3238 then 3 else 3) else (if x<3252 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8888 : Finset ℕ := ([40,72,130,132,144,246,1582,1594,1596,1614,1626,1628,1686,1762,1764,1776,2590,2666,2668,2680,2726,2738,2740,2758,2770,2772,3102,3178,3180,3192,3238,3250,3252,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8888 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8888 40 4
  · have he : independentCachedBranchMembers8888.erase 40=independentCachedBranchMembers8886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8886
  · have he : independentCachedBranchMembers8888.filter (independentCachedEdge 40)=independentCachedBranchMembers8887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8887
def independentCachedBranchMembers8889 : Finset ℕ := ([36,40,48,66,72,80,130,132,136,144,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2560,2590,2662,2666,2668,2674,2676,2680,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8889 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8889 136 5
  · have he : independentCachedBranchMembers8889.erase 136=independentCachedBranchMembers8865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8865
  · have he : independentCachedBranchMembers8889.filter (independentCachedEdge 136)=independentCachedBranchMembers8888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8888
def independentCachedBranchMembers8890 : Finset ℕ := ([80,250,1582,1590,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2740,2770,2776,3102,3178,3186,3192,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8890 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8890 5 (fun x => (if x<2674 then (if x<1686 then (if x<1590 then (if x<250 then 0 else (if x<1582 then 0 else 1)) else (if x<1626 then 2 else (if x<1678 then 0 else 2))) else (if x<1768 then (if x<1692 then 1 else (if x<1762 then 3 else 1)) else (if x<2590 then (if x<1776 then 3 else 0) else (if x<2666 then 1 else 1)))) else (if x<3178 then (if x<2740 then (if x<2680 then 0 else (if x<2726 then 4 else 1)) else (if x<2776 then (if x<2770 then 4 else 1) else (if x<3102 then 0 else 2))) else (if x<3238 then (if x<3186 then 3 else (if x<3192 then 2 else 0)) else (if x<3274 then (if x<3244 then 2 else 3) else (if x<3288 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8891 : Finset ℕ := ([250,1582,1590,1762,1768,1776,2590,2770,2776,3102,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8891 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8891 4 (fun x => (if x<2590 then (if x<1762 then (if x<1582 then 0 else (if x<1590 then 1 else 2)) else (if x<1768 then 0 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2770 then 1 else (if x<2776 then 0 else 1)) else (if x<3274 then 2 else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8892 : Finset ℕ := ([80,132,250,1582,1590,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2740,2770,2776,3102,3178,3186,3192,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8892 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8892 132 4
  · have he : independentCachedBranchMembers8892.erase 132=independentCachedBranchMembers8890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8890
  · have he : independentCachedBranchMembers8892.filter (independentCachedEdge 132)=independentCachedBranchMembers8891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8891
def independentCachedBranchMembers8893 : Finset ℕ := ([80,1582,1678,1692,1762,1776,2590,2674,2770,3102,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound8893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8893 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8893 4 (fun x => (if x<2590 then (if x<1692 then (if x<1582 then 0 else (if x<1678 then 0 else 1)) else (if x<1762 then 2 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2674 then 1 else (if x<2770 then 1 else 0)) else (if x<3186 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8894 : Finset ℕ := ([72,80,132,250,1582,1590,1626,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2726,2740,2770,2776,3102,3178,3186,3192,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8894 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8894 72 4
  · have he : independentCachedBranchMembers8894.erase 72=independentCachedBranchMembers8892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8892
  · have he : independentCachedBranchMembers8894.filter (independentCachedEdge 72)=independentCachedBranchMembers8893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8893
def independentCachedBranchMembers8895 : Finset ℕ := ([132,1590,1678,1692,1768,2590,2666,2680,2726,2740,2770,3186,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8895 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8895 4 (fun x => (if x<2680 then (if x<1692 then (if x<1590 then 0 else (if x<1678 then 1 else 0)) else (if x<2590 then (if x<1768 then 1 else 2) else (if x<2666 then 1 else 2))) else (if x<3186 then (if x<2740 then (if x<2726 then 0 else 3) else (if x<2770 then 1 else 3)) else (if x<3274 then (if x<3244 then 0 else 3) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
