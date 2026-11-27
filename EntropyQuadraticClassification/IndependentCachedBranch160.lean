/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch159
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7904 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1720,1734,1752,1776,3072,3118,3126,3150,3158,3174,3192,3226,3228,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7904 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7904 3276 4
  · have he : independentCachedBranchMembers7904.erase 3276=independentCachedBranchMembers7902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7902
  · have he : independentCachedBranchMembers7904.filter (independentCachedEdge 3276)=independentCachedBranchMembers7903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7903
def independentCachedBranchMembers7905 : Finset ℕ := ([1596,1626,1644,1650,1686,1734,1752,1776,3118,3158,3226,3244,3250,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7905 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7905 4 (fun x => (if x<3118 then (if x<1686 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3250 then (if x<3226 then (if x<3158 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7906 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1720,1734,1752,1776,3072,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7906 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7906 3242 4
  · have he : independentCachedBranchMembers7906.erase 3242=independentCachedBranchMembers7904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7904
  · have he : independentCachedBranchMembers7906.filter (independentCachedEdge 3242)=independentCachedBranchMembers7905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7905
def independentCachedBranchMembers7907 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1734,1752,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7907 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7907 4 (fun x => (if x<3118 then (if x<1702 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else 0)) else (if x<1734 then (if x<1720 then 0 else 0) else (if x<1752 then 1 else 1))) else (if x<3226 then (if x<3150 then (if x<3126 then 2 else 3) else (if x<3158 then 3 else 2)) else (if x<3298 then (if x<3228 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7908 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1720,1734,1752,1776,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7908 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7908 3102 4
  · have he : independentCachedBranchMembers7908.erase 3102=independentCachedBranchMembers7906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7906
  · have he : independentCachedBranchMembers7908.filter (independentCachedEdge 3102)=independentCachedBranchMembers7907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7907
def independentCachedBranchMembers7909 : Finset ℕ := ([1642,1644,1686,1720,1752,1776,3072,3118,3150,3174,3226,3228,3250,3252,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7909 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7909 4 (fun x => (if x<3150 then (if x<1752 then (if x<1686 then (if x<1644 then 0 else 1) else (if x<1720 then 2 else 0)) else (if x<3072 then (if x<1776 then 1 else 2) else (if x<3118 then 3 else 1))) else (if x<3250 then (if x<3226 then (if x<3174 then 0 else 3) else (if x<3228 then 1 else 0)) else (if x<3282 then (if x<3252 then 2 else 3) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7910 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1720,1734,1752,1768,1776,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7910 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7910 1768 4
  · have he : independentCachedBranchMembers7910.erase 1768=independentCachedBranchMembers7908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7908
  · have he : independentCachedBranchMembers7910.filter (independentCachedEdge 1768)=independentCachedBranchMembers7909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7909
def independentCachedBranchMembers7911 : Finset ℕ := ([1650,1652,1686,1702,1734,1776,3072,3126,3158,3174,3250,3252,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7911 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7911 4 (fun x => (if x<3158 then (if x<1734 then (if x<1686 then (if x<1652 then 0 else 1) else (if x<1702 then 0 else 1)) else (if x<3072 then (if x<1776 then 2 else 2) else (if x<3126 then 3 else 0))) else (if x<3282 then (if x<3250 then (if x<3174 then 3 else 1) else (if x<3252 then 3 else 1)) else (if x<3298 then (if x<3284 then 0 else 2) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7912 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7912 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7912 1678 4
  · have he : independentCachedBranchMembers7912.erase 1678=independentCachedBranchMembers7910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7910
  · have he : independentCachedBranchMembers7912.filter (independentCachedEdge 1678)=independentCachedBranchMembers7911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7911
def independentCachedBranchMembers7913 : Finset ℕ := ([1596,1626,1644,1652,1702,1752,3072,3118,3126,3174,3226,3244,3252,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7913 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7913 4 (fun x => (if x<3126 then (if x<1702 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<3072 then (if x<1752 then 1 else 2) else (if x<3118 then 3 else 1))) else (if x<3252 then (if x<3226 then (if x<3174 then 2 else 3) else (if x<3244 then 2 else 0)) else (if x<3282 then (if x<3274 then 3 else 0) else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7914 : Finset ℕ := ([1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7914 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7914 1628 4
  · have he : independentCachedBranchMembers7914.erase 1628=independentCachedBranchMembers7912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7912
  · have he : independentCachedBranchMembers7914.filter (independentCachedEdge 1628)=independentCachedBranchMembers7913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7913
def independentCachedBranchMembers7915 : Finset ℕ := ([1596,1626,1642,1650,1720,1734,3072,3150,3158,3174,3228,3244,3252,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7915 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7915 4 (fun x => (if x<3158 then (if x<1720 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1650 then 1 else 2)) else (if x<3072 then (if x<1734 then 1 else 2) else (if x<3150 then 3 else 1))) else (if x<3252 then (if x<3228 then (if x<3174 then 2 else 3) else (if x<3244 then 1 else 0)) else (if x<3282 then (if x<3274 then 3 else 0) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7916 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7916 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7916 1594 4
  · have he : independentCachedBranchMembers7916.erase 1594=independentCachedBranchMembers7914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7914
  · have he : independentCachedBranchMembers7916.filter (independentCachedEdge 1594)=independentCachedBranchMembers7915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7915
def independentCachedBranchMembers7917 : Finset ℕ := ([12,18,34,36,66,68,136,144,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2560,2590,2606,2614,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7917 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7917 2560 5
  · have he : independentCachedBranchMembers7917.erase 2560=independentCachedBranchMembers7899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7899
  · have he : independentCachedBranchMembers7917.filter (independentCachedEdge 2560)=independentCachedBranchMembers7916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7916
def independentCachedBranchMembers7918 : Finset ℕ := ([192,246,1628,1642,1650,1652,1734,1752,1768,1776,2646,2680,2762,2772,2786,2788,3150,3174,3192,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7918 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7918 5 (fun x => (if x<2762 then (if x<1734 then (if x<1642 then (if x<246 then 0 else (if x<1628 then 0 else 1)) else (if x<1650 then 1 else (if x<1652 then 2 else 3))) else (if x<1776 then (if x<1752 then 0 else (if x<1768 then 2 else 3)) else (if x<2646 then 0 else (if x<2680 then 3 else 1)))) else (if x<3192 then (if x<2788 then (if x<2772 then 3 else (if x<2786 then 0 else 0)) else (if x<3150 then 3 else (if x<3174 then 4 else 2))) else (if x<3284 then (if x<3276 then 2 else (if x<3282 then 2 else 0)) else (if x<3298 then 4 else (if x<3300 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7919 : Finset ℕ := ([246,1642,1652,1776,2762,2772,2788,3174,3192,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7919 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7919 4 (fun x => (if x<2788 then (if x<1776 then (if x<1642 then 0 else (if x<1652 then 1 else 0)) else (if x<2762 then 1 else (if x<2772 then 2 else 0))) else (if x<3276 then (if x<3174 then 2 else (if x<3192 then 3 else 1)) else (if x<3282 then 2 else (if x<3298 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7920 : Finset ℕ := ([192,246,1628,1642,1650,1652,1734,1752,1768,1776,2646,2680,2762,2764,2772,2786,2788,3150,3174,3192,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7920 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7920 2764 4
  · have he : independentCachedBranchMembers7920.erase 2764=independentCachedBranchMembers7918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7918
  · have he : independentCachedBranchMembers7920.filter (independentCachedEdge 2764)=independentCachedBranchMembers7919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7919
def independentCachedBranchMembers7921 : Finset ℕ := ([192,1628,1768,1776,2646,2786,2788,3174,3192,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7921 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7921 4 (fun x => (if x<2788 then (if x<1776 then (if x<1628 then 0 else (if x<1768 then 1 else 0)) else (if x<2646 then 1 else (if x<2786 then 2 else 0))) else (if x<3276 then (if x<3174 then 2 else (if x<3192 then 2 else 1)) else (if x<3282 then 3 else (if x<3284 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7922 : Finset ℕ := ([192,246,1628,1642,1650,1652,1734,1752,1768,1776,2646,2662,2680,2762,2764,2772,2786,2788,3150,3174,3192,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7922 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7922 2662 4
  · have he : independentCachedBranchMembers7922.erase 2662=independentCachedBranchMembers7920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7920
  · have he : independentCachedBranchMembers7922.filter (independentCachedEdge 2662)=independentCachedBranchMembers7921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7921
def independentCachedBranchMembers7923 : Finset ℕ := ([192,246,1628,1642,1652,1768,2646,2762,2772,2786,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7923 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7923 4 (fun x => (if x<2646 then (if x<1642 then (if x<246 then 0 else (if x<1628 then 0 else 1)) else (if x<1652 then 1 else (if x<1768 then 2 else 2))) else (if x<2786 then (if x<2762 then 2 else (if x<2772 then 2 else 0)) else (if x<3284 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7924 : Finset ℕ := ([192,246,1628,1642,1644,1650,1652,1734,1752,1768,1776,2646,2662,2680,2762,2764,2772,2786,2788,3150,3174,3192,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7924 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7924 1644 4
  · have he : independentCachedBranchMembers7924.erase 1644=independentCachedBranchMembers7922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7922
  · have he : independentCachedBranchMembers7924.filter (independentCachedEdge 1644)=independentCachedBranchMembers7923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7923
def independentCachedBranchMembers7925 : Finset ℕ := ([246,1628,1650,1652,1752,1776,2646,2680,2772,3192,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7925 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7925 4 (fun x => (if x<2646 then (if x<1652 then (if x<1628 then 0 else (if x<1650 then 1 else 0)) else (if x<1752 then 2 else (if x<1776 then 2 else 1))) else (if x<3192 then (if x<2680 then 0 else (if x<2772 then 1 else 1)) else (if x<3282 then 2 else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7926 : Finset ℕ := ([192,238,246,1628,1642,1644,1650,1652,1734,1752,1768,1776,2646,2662,2680,2762,2764,2772,2786,2788,3150,3174,3192,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7926 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7926 238 4
  · have he : independentCachedBranchMembers7926.erase 238=independentCachedBranchMembers7924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7924
  · have he : independentCachedBranchMembers7926.filter (independentCachedEdge 238)=independentCachedBranchMembers7925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7925
def independentCachedBranchMembers7927 : Finset ℕ := ([192,1642,1650,1752,1768,1776,2680,2762,2786,3192,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7927 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7927 4 (fun x => (if x<2680 then (if x<1752 then (if x<1642 then 0 else (if x<1650 then 1 else 2)) else (if x<1768 then 0 else (if x<1776 then 2 else 1))) else (if x<3192 then (if x<2762 then 1 else (if x<2786 then 0 else 1)) else (if x<3282 then 2 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7928 : Finset ℕ := ([68,192,238,246,1628,1642,1644,1650,1652,1734,1752,1768,1776,2646,2662,2680,2762,2764,2772,2786,2788,3150,3174,3192,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7928 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7928 68 4
  · have he : independentCachedBranchMembers7928.erase 68=independentCachedBranchMembers7926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7926
  · have he : independentCachedBranchMembers7928.filter (independentCachedEdge 68)=independentCachedBranchMembers7927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7927
def independentCachedBranchMembers7929 : Finset ℕ := ([246,1628,1644,1650,1776,2646,2662,2680,2762,2772,2788,3150,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7929 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7929 4 (fun x => (if x<2680 then (if x<1650 then (if x<1628 then 0 else (if x<1644 then 1 else 2)) else (if x<2646 then (if x<1776 then 0 else 1) else (if x<2662 then 0 else 2))) else (if x<3150 then (if x<2772 then (if x<2762 then 1 else 3) else (if x<2788 then 1 else 3)) else (if x<3282 then (if x<3276 then 2 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7930 : Finset ℕ := ([1650,1776,2680,2762,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7930 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7930 3 (fun x => (if x<2762 then (if x<1776 then 0 else (if x<2680 then 1 else 0)) else (if x<3282 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7931 : Finset ℕ := ([68,246,1628,1644,1650,1776,2646,2662,2680,2762,2772,2788,3150,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7931 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7931 68 3
  · have he : independentCachedBranchMembers7931.erase 68=independentCachedBranchMembers7929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7929
  · have he : independentCachedBranchMembers7931.filter (independentCachedEdge 68)=independentCachedBranchMembers7930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7930
def independentCachedBranchMembers7932 : Finset ℕ := ([68,192,238,246,1628,1642,1644,1650,1652,1734,1752,1768,1776,2646,2662,2680,2762,2764,2772,2786,2788,3150,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7932 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7932 3274 4
  · have he : independentCachedBranchMembers7932.erase 3274=independentCachedBranchMembers7928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7928
  · have he : independentCachedBranchMembers7932.filter (independentCachedEdge 3274)=independentCachedBranchMembers7931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7931
def independentCachedBranchMembers7933 : Finset ℕ := ([238,1642,1644,1752,1776,2646,2680,2762,2764,2786,2788,3150,3174,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7933 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7933 4 (fun x => (if x<2762 then (if x<1752 then (if x<1642 then 0 else (if x<1644 then 0 else 1)) else (if x<2646 then (if x<1776 then 1 else 2) else (if x<2680 then 3 else 1))) else (if x<3150 then (if x<2786 then (if x<2764 then 0 else 1) else (if x<2788 then 2 else 3)) else (if x<3282 then (if x<3174 then 0 else 3) else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7934 : Finset ℕ := ([1642,1644,2646,2680,3150,3174] : List ℕ).toFinset
theorem independentCachedBranchBound7934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7934 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7934 3 (fun x => (if x<2680 then (if x<1644 then 0 else (if x<2646 then 1 else 2)) else (if x<3150 then 0 else (if x<3174 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7935 : Finset ℕ := ([192,238,1642,1644,1752,1776,2646,2680,2762,2764,2786,2788,3150,3174,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7935 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7935 192 3
  · have he : independentCachedBranchMembers7935.erase 192=independentCachedBranchMembers7933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7933
  · have he : independentCachedBranchMembers7935.filter (independentCachedEdge 192)=independentCachedBranchMembers7934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7934
end EntropyDesigns.QuadraticRefinement
