/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch157
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7840 : Finset ℕ := ([34,68,136,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3118,3158,3174,3192,3226,3242,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7840 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7840 34 4
  · have he : independentCachedBranchMembers7840.erase 34=independentCachedBranchMembers7838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7838
  · have he : independentCachedBranchMembers7840.filter (independentCachedEdge 34)=independentCachedBranchMembers7839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7839
def independentCachedBranchMembers7841 : Finset ℕ := ([34,68,136,238,1594,1628,1678,1768,2614,2638,2716,2788,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7841 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7841 4 (fun x => (if x<2614 then (if x<1594 then (if x<136 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3118 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7842 : Finset ℕ := ([34,68,136,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7842 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7842 3282 4
  · have he : independentCachedBranchMembers7842.erase 3282=independentCachedBranchMembers7840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7840
  · have he : independentCachedBranchMembers7842.filter (independentCachedEdge 3282)=independentCachedBranchMembers7841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7841
def independentCachedBranchMembers7843 : Finset ℕ := ([34,68,136,238,1644,1650,1734,1752,2732,2738,2762,2772,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7843 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7843 4 (fun x => (if x<2732 then (if x<1644 then (if x<136 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3118 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7844 : Finset ℕ := ([34,68,136,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7844 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7844 3102 4
  · have he : independentCachedBranchMembers7844.erase 3102=independentCachedBranchMembers7842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7842
  · have he : independentCachedBranchMembers7844.filter (independentCachedEdge 3102)=independentCachedBranchMembers7843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7843
def independentCachedBranchMembers7845 : Finset ℕ := ([1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7845 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7845 4 (fun x => (if x<2614 then (if x<1678 then (if x<1644 then (if x<1628 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<2738 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2772 then (if x<2762 then 3 else 3) else (if x<2788 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7846 : Finset ℕ := ([34,68,136,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7846 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7846 3072 4
  · have he : independentCachedBranchMembers7846.erase 3072=independentCachedBranchMembers7844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7844
  · have he : independentCachedBranchMembers7846.filter (independentCachedEdge 3072)=independentCachedBranchMembers7845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7845
def independentCachedBranchMembers7847 : Finset ℕ := ([34,238,1594,1644,1650,1768,2614,2732,2738,2788,3118,3174,3192,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7847 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7847 4 (fun x => (if x<2738 then (if x<1650 then (if x<1594 then (if x<238 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2732 then 2 else 2))) else (if x<3192 then (if x<3118 then (if x<2788 then 1 else 1) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7848 : Finset ℕ := ([34,68,136,222,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7848 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7848 222 4
  · have he : independentCachedBranchMembers7848.erase 222=independentCachedBranchMembers7846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7846
  · have he : independentCachedBranchMembers7848.filter (independentCachedEdge 222)=independentCachedBranchMembers7847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7847
def independentCachedBranchMembers7849 : Finset ℕ := ([68,136,1628,1644,1650,1678,2638,2716,2732,2738,3158,3174,3192,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7849 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7849 4 (fun x => (if x<2732 then (if x<1650 then (if x<1628 then (if x<136 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2638 then (if x<1678 then 1 else 2) else (if x<2716 then 2 else 1))) else (if x<3192 then (if x<3158 then (if x<2738 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3226 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7850 : Finset ℕ := ([34,68,136,192,222,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7850 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7850 192 4
  · have he : independentCachedBranchMembers7850.erase 192=independentCachedBranchMembers7848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7848
  · have he : independentCachedBranchMembers7850.filter (independentCachedEdge 192)=independentCachedBranchMembers7849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7849
def independentCachedBranchMembers7851 : Finset ℕ := ([34,238,1628,1678,1734,1752,2638,2716,2762,2772,3118,3174,3192,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7851 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7851 4 (fun x => (if x<2762 then (if x<1734 then (if x<1628 then (if x<238 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1752 then 2 else 2) else (if x<2716 then 1 else 1))) else (if x<3192 then (if x<3118 then (if x<2772 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7852 : Finset ℕ := ([18,34,68,136,192,222,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7852 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7852 18 4
  · have he : independentCachedBranchMembers7852.erase 18=independentCachedBranchMembers7850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7850
  · have he : independentCachedBranchMembers7852.filter (independentCachedEdge 18)=independentCachedBranchMembers7851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7851
def independentCachedBranchMembers7853 : Finset ℕ := ([68,136,1594,1734,1752,1768,2614,2762,2772,2788,3158,3174,3192,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7853 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7853 4 (fun x => (if x<2772 then (if x<1752 then (if x<1594 then (if x<136 then 0 else 0) else (if x<1734 then 1 else 2)) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2762 then 1 else 2))) else (if x<3192 then (if x<3158 then (if x<2788 then 1 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3226 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7854 : Finset ℕ := ([12,18,34,68,136,192,222,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7854 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7854 12 4
  · have he : independentCachedBranchMembers7854.erase 12=independentCachedBranchMembers7852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7852
  · have he : independentCachedBranchMembers7854.filter (independentCachedEdge 12)=independentCachedBranchMembers7853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7853
def independentCachedBranchMembers7855 : Finset ℕ := ([12,18,34,36,66,68,136,144,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2740,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7855 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7855 2740 5
  · have he : independentCachedBranchMembers7855.erase 2740=independentCachedBranchMembers7835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7835
  · have he : independentCachedBranchMembers7855.filter (independentCachedEdge 2740)=independentCachedBranchMembers7854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7854
def independentCachedBranchMembers7856 : Finset ℕ := ([144,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3126,3150,3174,3192,3228,3242,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7856 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7856 5 (fun x => (if x<2732 then (if x<1686 then (if x<1626 then (if x<246 then 0 else (if x<1596 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1776 then (if x<1734 then 0 else (if x<1752 then 2 else 2)) else (if x<2646 then (if x<2606 then 0 else 3) else (if x<2714 then 3 else 3)))) else (if x<3174 then (if x<2772 then (if x<2738 then 1 else (if x<2762 then 0 else 1)) else (if x<3126 then (if x<2786 then 0 else 3) else (if x<3150 then 4 else 4))) else (if x<3242 then (if x<3192 then 2 else (if x<3228 then 2 else 4)) else (if x<3282 then (if x<3252 then 3 else 0) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7857 : Finset ℕ := ([1644,1686,1752,1776,2606,2714,2738,2772,3126,3192,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7857 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7857 4 (fun x => (if x<2738 then (if x<1776 then (if x<1686 then 0 else (if x<1752 then 1 else 0)) else (if x<2606 then 1 else (if x<2714 then 0 else 0))) else (if x<3192 then (if x<2772 then 1 else (if x<3126 then 1 else 2)) else (if x<3242 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7858 : Finset ℕ := ([66,144,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3126,3150,3174,3192,3228,3242,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7858 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7858 66 4
  · have he : independentCachedBranchMembers7858.erase 66=independentCachedBranchMembers7856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7856
  · have he : independentCachedBranchMembers7858.filter (independentCachedEdge 66)=independentCachedBranchMembers7857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7857
def independentCachedBranchMembers7859 : Finset ℕ := ([1650,1686,1734,1776,2646,2738,2772,2786,3150,3192,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound7859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7859 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7859 4 (fun x => (if x<2772 then (if x<1776 then (if x<1686 then 0 else (if x<1734 then 0 else 1)) else (if x<2646 then 1 else (if x<2738 then 0 else 0))) else (if x<3192 then (if x<2786 then 1 else (if x<3150 then 1 else 2)) else (if x<3228 then 2 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7860 : Finset ℕ := ([36,66,144,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3126,3150,3174,3192,3228,3242,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7860 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7860 36 4
  · have he : independentCachedBranchMembers7860.erase 36=independentCachedBranchMembers7858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7858
  · have he : independentCachedBranchMembers7860.filter (independentCachedEdge 36)=independentCachedBranchMembers7859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7859
def independentCachedBranchMembers7861 : Finset ℕ := ([36,66,144,246,1596,1626,1686,1776,2606,2646,2714,2786,3126,3150,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7861 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7861 4 (fun x => (if x<2606 then (if x<1596 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3126 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7862 : Finset ℕ := ([36,66,144,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7862 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7862 3276 4
  · have he : independentCachedBranchMembers7862.erase 3276=independentCachedBranchMembers7860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7860
  · have he : independentCachedBranchMembers7862.filter (independentCachedEdge 3276)=independentCachedBranchMembers7861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7861
def independentCachedBranchMembers7863 : Finset ℕ := ([36,66,144,246,1644,1650,1734,1752,2732,2738,2762,2772,3126,3150,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7863 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7863 4 (fun x => (if x<2732 then (if x<1644 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3126 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7864 : Finset ℕ := ([36,66,144,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7864 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7864 3102 4
  · have he : independentCachedBranchMembers7864.erase 3102=independentCachedBranchMembers7862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7862
  · have he : independentCachedBranchMembers7864.filter (independentCachedEdge 3102)=independentCachedBranchMembers7863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7863
def independentCachedBranchMembers7865 : Finset ℕ := ([1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786] : List ℕ).toFinset
theorem independentCachedBranchBound7865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7865 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7865 4 (fun x => (if x<2606 then (if x<1686 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<2738 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2772 then (if x<2762 then 3 else 3) else (if x<2786 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7866 : Finset ℕ := ([36,66,144,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7866 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7866 3072 4
  · have he : independentCachedBranchMembers7866.erase 3072=independentCachedBranchMembers7864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7864
  · have he : independentCachedBranchMembers7866.filter (independentCachedEdge 3072)=independentCachedBranchMembers7865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7865
def independentCachedBranchMembers7867 : Finset ℕ := ([36,246,1596,1644,1650,1776,2606,2732,2738,2786,3126,3174,3192,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7867 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7867 4 (fun x => (if x<2738 then (if x<1650 then (if x<1596 then (if x<246 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2732 then 2 else 1))) else (if x<3192 then (if x<3126 then (if x<2786 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7868 : Finset ℕ := ([36,66,144,222,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7868 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7868 222 4
  · have he : independentCachedBranchMembers7868.erase 222=independentCachedBranchMembers7866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7866
  · have he : independentCachedBranchMembers7868.filter (independentCachedEdge 222)=independentCachedBranchMembers7867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7867
def independentCachedBranchMembers7869 : Finset ℕ := ([66,144,1626,1644,1650,1686,2646,2714,2732,2738,3150,3174,3192,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7869 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7869 4 (fun x => (if x<2732 then (if x<1650 then (if x<1626 then (if x<144 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<2646 then (if x<1686 then 2 else 2) else (if x<2714 then 2 else 1))) else (if x<3192 then (if x<3150 then (if x<2738 then 1 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3228 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7870 : Finset ℕ := ([36,66,144,192,222,246,1596,1626,1644,1650,1686,1734,1752,1776,2606,2646,2714,2732,2738,2762,2772,2786,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7870 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7870 192 4
  · have he : independentCachedBranchMembers7870.erase 192=independentCachedBranchMembers7868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7868
  · have he : independentCachedBranchMembers7870.filter (independentCachedEdge 192)=independentCachedBranchMembers7869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7869
def independentCachedBranchMembers7871 : Finset ℕ := ([66,144,1596,1734,1752,1776,2606,2762,2772,2786,3150,3174,3192,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7871 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7871 4 (fun x => (if x<2772 then (if x<1752 then (if x<1596 then (if x<144 then 0 else 0) else (if x<1734 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2762 then 1 else 1))) else (if x<3192 then (if x<3150 then (if x<2786 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3228 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
