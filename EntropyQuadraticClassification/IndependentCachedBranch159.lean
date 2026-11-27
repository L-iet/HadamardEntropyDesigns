/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch158
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7872 : Finset ℕ := ([18,36,66,144,192,222,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7872 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7872 18 4
  · have he : independentCachedBranchMembers7872.erase 18=independentCachedBranchMembers7870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7870
  · have he : independentCachedBranchMembers7872.filter (independentCachedEdge 18)=independentCachedBranchMembers7871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7871
def independentCachedBranchMembers7873 : Finset ℕ := ([36,246,1626,1686,1734,1752,2646,2714,2762,2772,3126,3174,3192,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7873 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7873 4 (fun x => (if x<2762 then (if x<1734 then (if x<1626 then (if x<246 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1752 then 2 else 2) else (if x<2714 then 1 else 1))) else (if x<3192 then (if x<3126 then (if x<2772 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7874 : Finset ℕ := ([12,18,36,66,144,192,222,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7874 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7874 12 4
  · have he : independentCachedBranchMembers7874.erase 12=independentCachedBranchMembers7872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7872
  · have he : independentCachedBranchMembers7874.filter (independentCachedEdge 12)=independentCachedBranchMembers7873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7873
def independentCachedBranchMembers7875 : Finset ℕ := ([12,18,34,36,66,68,136,144,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7875 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7875 2730 5
  · have he : independentCachedBranchMembers7875.erase 2730=independentCachedBranchMembers7855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7855
  · have he : independentCachedBranchMembers7875.filter (independentCachedEdge 2730)=independentCachedBranchMembers7874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7874
def independentCachedBranchMembers7876 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3102,3174,3192,3244,3250,3252,3274,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7876 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7876 5 (fun x => (if x<2714 then (if x<1734 then (if x<1652 then (if x<1644 then 0 else (if x<1650 then 1 else 1)) else (if x<1702 then 0 else (if x<1720 then 0 else 0))) else (if x<2614 then (if x<1752 then 1 else (if x<2606 then 1 else 2)) else (if x<2638 then 3 else (if x<2646 then 3 else 2)))) else (if x<3192 then (if x<2788 then (if x<2716 then 2 else (if x<2786 then 3 else 2)) else (if x<3102 then 3 else (if x<3174 then 2 else 0))) else (if x<3252 then (if x<3244 then 0 else (if x<3250 then 4 else 4)) else (if x<3282 then (if x<3274 then 0 else 4) else (if x<3284 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7877 : Finset ℕ := ([1642,1644,1720,1752,2606,2638,2714,2716,3102,3192,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound7877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7877 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7877 4 (fun x => (if x<2714 then (if x<1752 then (if x<1644 then 0 else (if x<1720 then 1 else 0)) else (if x<2606 then 1 else (if x<2638 then 1 else 0))) else (if x<3192 then (if x<2716 then 1 else (if x<3102 then 0 else 2)) else (if x<3244 then 2 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7878 : Finset ℕ := ([246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3102,3174,3192,3244,3250,3252,3274,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7878 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7878 246 4
  · have he : independentCachedBranchMembers7878.erase 246=independentCachedBranchMembers7876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7876
  · have he : independentCachedBranchMembers7878.filter (independentCachedEdge 246)=independentCachedBranchMembers7877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7877
def independentCachedBranchMembers7879 : Finset ℕ := ([1650,1652,1702,1734,2614,2646,2786,2788,3102,3192,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound7879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7879 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7879 4 (fun x => (if x<2786 then (if x<1734 then (if x<1652 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then 1 else (if x<2646 then 0 else 1))) else (if x<3192 then (if x<2788 then 0 else (if x<3102 then 1 else 2)) else (if x<3244 then 2 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7880 : Finset ℕ := ([144,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3102,3174,3192,3244,3250,3252,3274,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7880 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7880 144 4
  · have he : independentCachedBranchMembers7880.erase 144=independentCachedBranchMembers7878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7878
  · have he : independentCachedBranchMembers7880.filter (independentCachedEdge 144)=independentCachedBranchMembers7879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7879
def independentCachedBranchMembers7881 : Finset ℕ := ([1644,1652,1702,1752,2606,2614,2714,2788,3102,3192,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7881 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7881 4 (fun x => (if x<2714 then (if x<1752 then (if x<1652 then 0 else (if x<1702 then 1 else 0)) else (if x<2606 then 1 else (if x<2614 then 0 else 1))) else (if x<3192 then (if x<2788 then 1 else (if x<3102 then 0 else 2)) else (if x<3250 then 2 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7882 : Finset ℕ := ([66,144,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3102,3174,3192,3244,3250,3252,3274,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7882 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7882 66 4
  · have he : independentCachedBranchMembers7882.erase 66=independentCachedBranchMembers7880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7880
  · have he : independentCachedBranchMembers7882.filter (independentCachedEdge 66)=independentCachedBranchMembers7881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7881
def independentCachedBranchMembers7883 : Finset ℕ := ([1642,1650,1720,1734,2638,2646,2716,2786,3102,3192,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7883 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7883 4 (fun x => (if x<2716 then (if x<1734 then (if x<1650 then 0 else (if x<1720 then 1 else 0)) else (if x<2638 then 1 else (if x<2646 then 0 else 1))) else (if x<3192 then (if x<2786 then 0 else (if x<3102 then 1 else 2)) else (if x<3250 then 2 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7884 : Finset ℕ := ([36,66,144,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3102,3174,3192,3244,3250,3252,3274,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7884 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7884 36 4
  · have he : independentCachedBranchMembers7884.erase 36=independentCachedBranchMembers7882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7882
  · have he : independentCachedBranchMembers7884.filter (independentCachedEdge 36)=independentCachedBranchMembers7883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7883
def independentCachedBranchMembers7885 : Finset ℕ := ([36,66,144,246,1642,1652,1702,1720,2606,2646,2714,2786,3244,3250,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7885 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7885 4 (fun x => (if x<2606 then (if x<1642 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3244 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3274 then (if x<3250 then 3 else 3) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7886 : Finset ℕ := ([36,66,144,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3102,3174,3192,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7886 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7886 3276 4
  · have he : independentCachedBranchMembers7886.erase 3276=independentCachedBranchMembers7884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7884
  · have he : independentCachedBranchMembers7886.filter (independentCachedEdge 3276)=independentCachedBranchMembers7885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7885
def independentCachedBranchMembers7887 : Finset ℕ := ([36,66,144,246,1644,1650,1734,1752,2614,2638,2716,2788,3244,3250,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7887 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7887 4 (fun x => (if x<2614 then (if x<1644 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3244 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3274 then (if x<3250 then 3 else 3) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7888 : Finset ℕ := ([36,66,144,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7888 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7888 3242 4
  · have he : independentCachedBranchMembers7888.erase 3242=independentCachedBranchMembers7886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7886
  · have he : independentCachedBranchMembers7888.filter (independentCachedEdge 3242)=independentCachedBranchMembers7887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7887
def independentCachedBranchMembers7889 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7889 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7889 4 (fun x => (if x<2606 then (if x<1702 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else 0)) else (if x<1734 then (if x<1720 then 0 else 0) else (if x<1752 then 1 else 1))) else (if x<2714 then (if x<2638 then (if x<2614 then 2 else 3) else (if x<2646 then 3 else 2)) else (if x<2786 then (if x<2716 then 2 else 3) else (if x<2788 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7890 : Finset ℕ := ([36,66,144,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7890 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7890 3072 4
  · have he : independentCachedBranchMembers7890.erase 3072=independentCachedBranchMembers7888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7888
  · have he : independentCachedBranchMembers7890.filter (independentCachedEdge 3072)=independentCachedBranchMembers7889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7889
def independentCachedBranchMembers7891 : Finset ℕ := ([144,246,1650,1652,1720,1752,2614,2646,2714,2716,3102,3192,3250,3252,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7891 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7891 4 (fun x => (if x<2714 then (if x<1720 then (if x<1650 then (if x<246 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<2614 then (if x<1752 then 1 else 2) else (if x<2646 then 2 else 1))) else (if x<3250 then (if x<3102 then (if x<2716 then 2 else 1) else (if x<3192 then 3 else 3)) else (if x<3282 then (if x<3252 then 0 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7892 : Finset ℕ := ([36,66,144,238,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7892 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7892 238 4
  · have he : independentCachedBranchMembers7892.erase 238=independentCachedBranchMembers7890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7890
  · have he : independentCachedBranchMembers7892.filter (independentCachedEdge 238)=independentCachedBranchMembers7891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7891
def independentCachedBranchMembers7893 : Finset ℕ := ([144,246,1642,1644,1702,1734,2606,2638,2786,2788,3102,3192,3250,3252,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7893 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7893 4 (fun x => (if x<2786 then (if x<1702 then (if x<1642 then (if x<246 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2606 then (if x<1734 then 1 else 2) else (if x<2638 then 1 else 2))) else (if x<3250 then (if x<3102 then (if x<2788 then 1 else 2) else (if x<3192 then 3 else 3)) else (if x<3282 then (if x<3252 then 0 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7894 : Finset ℕ := ([36,66,136,144,238,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7894 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7894 136 4
  · have he : independentCachedBranchMembers7894.erase 136=independentCachedBranchMembers7892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7892
  · have he : independentCachedBranchMembers7894.filter (independentCachedEdge 136)=independentCachedBranchMembers7893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7893
def independentCachedBranchMembers7895 : Finset ℕ := ([36,66,1642,1650,1702,1752,2606,2614,2716,2786,3102,3192,3244,3252,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7895 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7895 4 (fun x => (if x<2716 then (if x<1702 then (if x<1642 then (if x<66 then 0 else 0) else (if x<1650 then 1 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2614 then 1 else 2))) else (if x<3244 then (if x<3102 then (if x<2786 then 2 else 1) else (if x<3192 then 3 else 3)) else (if x<3274 then (if x<3252 then 0 else 3) else (if x<3282 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7896 : Finset ℕ := ([36,66,68,136,144,238,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7896 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7896 68 4
  · have he : independentCachedBranchMembers7896.erase 68=independentCachedBranchMembers7894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7894
  · have he : independentCachedBranchMembers7896.filter (independentCachedEdge 68)=independentCachedBranchMembers7895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7895
def independentCachedBranchMembers7897 : Finset ℕ := ([36,66,1644,1652,1720,1734,2638,2646,2714,2788,3102,3192,3244,3252,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7897 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7897 4 (fun x => (if x<2714 then (if x<1720 then (if x<1644 then (if x<66 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<2638 then (if x<1734 then 1 else 2) else (if x<2646 then 1 else 2))) else (if x<3244 then (if x<3102 then (if x<2788 then 1 else 2) else (if x<3192 then 3 else 3)) else (if x<3274 then (if x<3252 then 0 else 3) else (if x<3282 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7898 : Finset ℕ := ([34,36,66,68,136,144,238,246,1642,1644,1650,1652,1702,1720,1734,1752,2606,2614,2638,2646,2714,2716,2786,2788,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7898 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7898 34 4
  · have he : independentCachedBranchMembers7898.erase 34=independentCachedBranchMembers7896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7896
  · have he : independentCachedBranchMembers7898.filter (independentCachedEdge 34)=independentCachedBranchMembers7897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7897
def independentCachedBranchMembers7899 : Finset ℕ := ([12,18,34,36,66,68,136,144,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2590,2606,2614,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7899 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7899 2590 5
  · have he : independentCachedBranchMembers7899.erase 2590=independentCachedBranchMembers7875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7875
  · have he : independentCachedBranchMembers7899.filter (independentCachedEdge 2590)=independentCachedBranchMembers7898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7898
def independentCachedBranchMembers7900 : Finset ℕ := ([1626,1642,1644,1650,1652,1686,1702,1720,1734,1752,1776,3072,3118,3126,3150,3158,3174,3192,3226,3228,3244,3250,3252,3274,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7900 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7900 5 (fun x => (if x<3150 then (if x<1720 then (if x<1650 then (if x<1642 then 0 else (if x<1644 then 1 else 0)) else (if x<1686 then (if x<1652 then 2 else 1) else (if x<1702 then 2 else 1))) else (if x<1776 then (if x<1734 then 0 else (if x<1752 then 3 else 2)) else (if x<3118 then (if x<3072 then 3 else 4) else (if x<3126 then 4 else 2)))) else (if x<3250 then (if x<3192 then (if x<3158 then 0 else (if x<3174 then 4 else 1)) else (if x<3228 then (if x<3226 then 0 else 0) else (if x<3244 then 2 else 0))) else (if x<3282 then (if x<3252 then 4 else (if x<3274 then 1 else 4)) else (if x<3298 then (if x<3284 then 2 else 3) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7901 : Finset ℕ := ([1644,1652,1720,1734,3072,3150,3158,3174,3226,3250,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7901 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7901 4 (fun x => (if x<3158 then (if x<1734 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3250 then (if x<3174 then 1 else (if x<3226 then 2 else 0)) else (if x<3284 then 2 else (if x<3300 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7902 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1720,1734,1752,1776,3072,3118,3126,3150,3158,3174,3192,3226,3228,3244,3250,3252,3274,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7902 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7902 1596 4
  · have he : independentCachedBranchMembers7902.erase 1596=independentCachedBranchMembers7900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7900
  · have he : independentCachedBranchMembers7902.filter (independentCachedEdge 1596)=independentCachedBranchMembers7901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7901
def independentCachedBranchMembers7903 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1776,3126,3150,3228,3244,3250,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7903 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7903 4 (fun x => (if x<3126 then (if x<1686 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3250 then (if x<3228 then (if x<3150 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
