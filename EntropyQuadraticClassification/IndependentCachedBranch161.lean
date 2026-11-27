/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch160
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7936 : Finset ℕ := ([68,192,238,246,1628,1642,1644,1650,1652,1734,1752,1768,1776,2646,2662,2680,2762,2764,2772,2786,2788,3150,3158,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7936 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7936 3158 4
  · have he : independentCachedBranchMembers7936.erase 3158=independentCachedBranchMembers7932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7932
  · have he : independentCachedBranchMembers7936.filter (independentCachedEdge 3158)=independentCachedBranchMembers7935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7935
def independentCachedBranchMembers7937 : Finset ℕ := ([68,238,1628,1642,1652,1768,2646,2762,2772,2786,3150,3174,3192,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7937 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7937 4 (fun x => (if x<2772 then (if x<1652 then (if x<1628 then (if x<238 then 0 else 0) else (if x<1642 then 1 else 1)) else (if x<2646 then (if x<1768 then 2 else 2) else (if x<2762 then 2 else 2))) else (if x<3192 then (if x<3150 then (if x<2786 then 1 else 1) else (if x<3174 then 0 else 3)) else (if x<3282 then (if x<3276 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7938 : Finset ℕ := ([68,192,238,246,1628,1642,1644,1650,1652,1734,1752,1768,1776,2646,2662,2680,2762,2764,2770,2772,2786,2788,3150,3158,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7938 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7938 2770 4
  · have he : independentCachedBranchMembers7938.erase 2770=independentCachedBranchMembers7936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7936
  · have he : independentCachedBranchMembers7938.filter (independentCachedEdge 2770)=independentCachedBranchMembers7937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7937
def independentCachedBranchMembers7939 : Finset ℕ := ([192,246,1650,1652,1752,1768,2646,2662,2762,2764,3150,3192,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7939 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7939 4 (fun x => (if x<2762 then (if x<1752 then (if x<1650 then (if x<246 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<2646 then (if x<1768 then 1 else 2) else (if x<2662 then 2 else 1))) else (if x<3282 then (if x<3150 then (if x<2764 then 2 else 1) else (if x<3192 then 3 else 3)) else (if x<3298 then (if x<3284 then 0 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7940 : Finset ℕ := ([68,192,238,246,1628,1642,1644,1650,1652,1734,1752,1768,1776,2638,2646,2662,2680,2762,2764,2770,2772,2786,2788,3150,3158,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7940 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7940 2638 4
  · have he : independentCachedBranchMembers7940.erase 2638=independentCachedBranchMembers7938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7938
  · have he : independentCachedBranchMembers7940.filter (independentCachedEdge 2638)=independentCachedBranchMembers7939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7939
def independentCachedBranchMembers7941 : Finset ℕ := ([68,192,238,246,1628,1642,1650,1752,2662,2764,2772,2786,3174,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7941 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7941 4 (fun x => (if x<2662 then (if x<1628 then (if x<238 then (if x<192 then 0 else 1) else (if x<246 then 0 else 1)) else (if x<1650 then (if x<1642 then 2 else 2) else (if x<1752 then 3 else 3))) else (if x<3174 then (if x<2772 then (if x<2764 then 0 else 0) else (if x<2786 then 1 else 1)) else (if x<3284 then (if x<3276 then 3 else 3) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7942 : Finset ℕ := ([68,192,238,246,1626,1628,1642,1644,1650,1652,1734,1752,1768,1776,2638,2646,2662,2680,2762,2764,2770,2772,2786,2788,3150,3158,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7942 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7942 1626 4
  · have he : independentCachedBranchMembers7942.erase 1626=independentCachedBranchMembers7940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7940
  · have he : independentCachedBranchMembers7942.filter (independentCachedEdge 1626)=independentCachedBranchMembers7941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7941
def independentCachedBranchMembers7943 : Finset ℕ := ([238,246,1642,1644,1650,1652,1768,1776,2662,2680,2786,2788,3174,3192,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7943 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7943 4 (fun x => (if x<2662 then (if x<1650 then (if x<1642 then (if x<246 then 0 else 1) else (if x<1644 then 0 else 2)) else (if x<1768 then (if x<1652 then 1 else 3) else (if x<1776 then 3 else 2))) else (if x<3174 then (if x<2786 then (if x<2680 then 0 else 2) else (if x<2788 then 1 else 2)) else (if x<3298 then (if x<3192 then 1 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7944 : Finset ℕ := ([68,192,222,238,246,1626,1628,1642,1644,1650,1652,1734,1752,1768,1776,2638,2646,2662,2680,2762,2764,2770,2772,2786,2788,3150,3158,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7944 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7944 222 4
  · have he : independentCachedBranchMembers7944.erase 222=independentCachedBranchMembers7942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7942
  · have he : independentCachedBranchMembers7944.filter (independentCachedEdge 222)=independentCachedBranchMembers7943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7943
def independentCachedBranchMembers7945 : Finset ℕ := ([68,192,1628,1644,1652,1752,1768,1776,2680,2764,2772,2788,3192,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7945 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7945 4 (fun x => (if x<2680 then (if x<1652 then (if x<1628 then (if x<192 then 0 else 1) else (if x<1644 then 0 else 2)) else (if x<1768 then (if x<1752 then 3 else 1) else (if x<1776 then 3 else 2))) else (if x<3192 then (if x<2772 then (if x<2764 then 2 else 0) else (if x<2788 then 1 else 2)) else (if x<3284 then (if x<3276 then 3 else 1) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7946 : Finset ℕ := ([66,68,192,222,238,246,1626,1628,1642,1644,1650,1652,1734,1752,1768,1776,2638,2646,2662,2680,2762,2764,2770,2772,2786,2788,3150,3158,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7946 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7946 66 4
  · have he : independentCachedBranchMembers7946.erase 66=independentCachedBranchMembers7944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7944
  · have he : independentCachedBranchMembers7946.filter (independentCachedEdge 66)=independentCachedBranchMembers7945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7945
def independentCachedBranchMembers7947 : Finset ℕ := ([12,18,34,36,66,68,136,144,190,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2560,2590,2606,2614,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7947 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7947 190 5
  · have he : independentCachedBranchMembers7947.erase 190=independentCachedBranchMembers7917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7917
  · have he : independentCachedBranchMembers7947.filter (independentCachedEdge 190)=independentCachedBranchMembers7946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7946
def independentCachedBranchMembers7948 : Finset ℕ := ([192,222,1594,1596,1642,1644,1652,1678,1686,1734,1752,2606,2662,2680,2714,2762,2764,2770,2772,3118,3126,3192,3226,3228,3274,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7948 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7948 5 (fun x => (if x<2680 then (if x<1652 then (if x<1596 then (if x<222 then 0 else (if x<1594 then 0 else 1)) else (if x<1642 then 2 else (if x<1644 then 2 else 1))) else (if x<1734 then (if x<1678 then 3 else (if x<1686 then 1 else 3)) else (if x<2606 then (if x<1752 then 0 else 0) else (if x<2662 then 1 else 4)))) else (if x<3126 then (if x<2764 then (if x<2714 then 1 else (if x<2762 then 1 else 0)) else (if x<2772 then (if x<2770 then 1 else 4) else (if x<3118 then 0 else 2))) else (if x<3228 then (if x<3192 then 3 else (if x<3226 then 2 else 3)) else (if x<3282 then (if x<3274 then 2 else 2) else (if x<3284 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7949 : Finset ℕ := ([192,1594,1596,1652,1678,1734,2680,2762,2764,3126,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound7949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7949 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7949 4 (fun x => (if x<2680 then (if x<1652 then (if x<1594 then 0 else (if x<1596 then 0 else 1)) else (if x<1678 then 2 else (if x<1734 then 1 else 2))) else (if x<3126 then (if x<2762 then 1 else (if x<2764 then 1 else 0)) else (if x<3192 then 0 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7950 : Finset ℕ := ([144,192,222,1594,1596,1642,1644,1652,1678,1686,1734,1752,2606,2662,2680,2714,2762,2764,2770,2772,3118,3126,3192,3226,3228,3274,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7950 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7950 144 4
  · have he : independentCachedBranchMembers7950.erase 144=independentCachedBranchMembers7948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7948
  · have he : independentCachedBranchMembers7950.filter (independentCachedEdge 144)=independentCachedBranchMembers7949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7949
def independentCachedBranchMembers7951 : Finset ℕ := ([222,1594,1642,1678,1686,1734,2680,2764,2772,3192,3228,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7951 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7951 4 (fun x => (if x<2680 then (if x<1678 then (if x<1594 then 0 else (if x<1642 then 1 else 2)) else (if x<1686 then 0 else (if x<1734 then 1 else 2))) else (if x<3192 then (if x<2764 then 1 else (if x<2772 then 0 else 1)) else (if x<3228 then 2 else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7952 : Finset ℕ := ([36,144,192,222,1594,1596,1642,1644,1652,1678,1686,1734,1752,2606,2662,2680,2714,2762,2764,2770,2772,3118,3126,3192,3226,3228,3274,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7952 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7952 36 4
  · have he : independentCachedBranchMembers7952.erase 36=independentCachedBranchMembers7950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7950
  · have he : independentCachedBranchMembers7952.filter (independentCachedEdge 36)=independentCachedBranchMembers7951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7951
def independentCachedBranchMembers7953 : Finset ℕ := ([144,1596,1642,1652,1686,2606,2662,2680,2714,2764,2770,3126,3228,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7953 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7953 4 (fun x => (if x<2680 then (if x<1652 then (if x<1596 then 0 else (if x<1642 then 1 else 0)) else (if x<2606 then (if x<1686 then 2 else 1) else (if x<2662 then 0 else 2))) else (if x<3126 then (if x<2764 then (if x<2714 then 1 else 3) else (if x<2770 then 3 else 1)) else (if x<3274 then (if x<3228 then 2 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7954 : Finset ℕ := ([1642,1686,2680,2764,3228,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7954 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7954 3 (fun x => (if x<2764 then (if x<1686 then 0 else (if x<2680 then 1 else 0)) else (if x<3228 then 2 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7955 : Finset ℕ := ([36,144,1596,1642,1652,1686,2606,2662,2680,2714,2764,2770,3126,3228,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7955 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7955 36 3
  · have he : independentCachedBranchMembers7955.erase 36=independentCachedBranchMembers7953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7953
  · have he : independentCachedBranchMembers7955.filter (independentCachedEdge 36)=independentCachedBranchMembers7954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7954
def independentCachedBranchMembers7956 : Finset ℕ := ([36,144,192,222,1594,1596,1642,1644,1652,1678,1686,1734,1752,2606,2662,2680,2714,2762,2764,2770,2772,3118,3126,3192,3226,3228,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7956 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7956 3276 4
  · have he : independentCachedBranchMembers7956.erase 3276=independentCachedBranchMembers7952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7952
  · have he : independentCachedBranchMembers7956.filter (independentCachedEdge 3276)=independentCachedBranchMembers7955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7955
def independentCachedBranchMembers7957 : Finset ℕ := ([222,1594,1596,1678,1686,2662,2680,2762,2764,2770,2772,3118,3126,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7957 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7957 4 (fun x => (if x<2762 then (if x<1678 then (if x<1594 then 0 else (if x<1596 then 1 else 2)) else (if x<2662 then (if x<1686 then 0 else 1) else (if x<2680 then 3 else 1))) else (if x<3118 then (if x<2770 then (if x<2764 then 0 else 3) else (if x<2772 then 2 else 1)) else (if x<3226 then (if x<3126 then 2 else 3) else (if x<3228 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7958 : Finset ℕ := ([1678,1686,2662,2680,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7958 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7958 3 (fun x => (if x<2680 then (if x<1686 then 0 else (if x<2662 then 1 else 2)) else (if x<3226 then 0 else (if x<3228 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7959 : Finset ℕ := ([192,222,1594,1596,1678,1686,2662,2680,2762,2764,2770,2772,3118,3126,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7959 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7959 192 3
  · have he : independentCachedBranchMembers7959.erase 192=independentCachedBranchMembers7957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7957
  · have he : independentCachedBranchMembers7959.filter (independentCachedEdge 192)=independentCachedBranchMembers7958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7958
def independentCachedBranchMembers7960 : Finset ℕ := ([36,144,192,222,1594,1596,1642,1644,1652,1678,1686,1734,1752,2606,2662,2680,2714,2762,2764,2770,2772,3118,3126,3174,3192,3226,3228,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7960 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7960 3174 4
  · have he : independentCachedBranchMembers7960.erase 3174=independentCachedBranchMembers7956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7956
  · have he : independentCachedBranchMembers7960.filter (independentCachedEdge 3174)=independentCachedBranchMembers7959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7959
def independentCachedBranchMembers7961 : Finset ℕ := ([36,192,1594,1644,1652,1734,2662,2714,2764,2772,3118,3126,3192,3228,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7961 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7961 4 (fun x => (if x<2764 then (if x<1652 then (if x<1594 then (if x<192 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<2662 then (if x<1734 then 2 else 2) else (if x<2714 then 2 else 1))) else (if x<3192 then (if x<3118 then (if x<2772 then 1 else 2) else (if x<3126 then 0 else 3)) else (if x<3274 then (if x<3228 then 3 else 3) else (if x<3282 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7962 : Finset ℕ := ([36,144,192,222,1594,1596,1642,1644,1652,1678,1686,1734,1752,2606,2662,2680,2714,2716,2762,2764,2770,2772,3118,3126,3174,3192,3226,3228,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7962 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7962 2716 4
  · have he : independentCachedBranchMembers7962.erase 2716=independentCachedBranchMembers7960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7960
  · have he : independentCachedBranchMembers7962.filter (independentCachedEdge 2716)=independentCachedBranchMembers7961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7961
def independentCachedBranchMembers7963 : Finset ℕ := ([144,222,1642,1644,1678,1734,2606,2662,2762,2764,3126,3192,3226,3228,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7963 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7963 4 (fun x => (if x<2762 then (if x<1678 then (if x<1642 then (if x<222 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2606 then (if x<1734 then 1 else 2) else (if x<2662 then 1 else 2))) else (if x<3226 then (if x<3126 then (if x<2764 then 1 else 2) else (if x<3192 then 3 else 3)) else (if x<3282 then (if x<3228 then 0 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7964 : Finset ℕ := ([36,144,192,222,1594,1596,1642,1644,1652,1678,1686,1734,1752,2606,2614,2662,2680,2714,2716,2762,2764,2770,2772,3118,3126,3174,3192,3226,3228,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7964 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7964 2614 4
  · have he : independentCachedBranchMembers7964.erase 2614=independentCachedBranchMembers7962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7962
  · have he : independentCachedBranchMembers7964.filter (independentCachedEdge 2614)=independentCachedBranchMembers7963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7963
def independentCachedBranchMembers7965 : Finset ℕ := ([36,144,192,222,1594,1642,1652,1678,2606,2714,2762,2772,3118,3226,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7965 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7965 4 (fun x => (if x<2606 then (if x<1594 then (if x<192 then (if x<144 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1652 then (if x<1642 then 2 else 3) else (if x<1678 then 2 else 3))) else (if x<3118 then (if x<2762 then (if x<2714 then 0 else 0) else (if x<2772 then 1 else 1)) else (if x<3274 then (if x<3226 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7966 : Finset ℕ := ([36,144,192,222,1594,1596,1642,1644,1650,1652,1678,1686,1734,1752,2606,2614,2662,2680,2714,2716,2762,2764,2770,2772,3118,3126,3174,3192,3226,3228,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7966 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7966 1650 4
  · have he : independentCachedBranchMembers7966.erase 1650=independentCachedBranchMembers7964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7964
  · have he : independentCachedBranchMembers7966.filter (independentCachedEdge 1650)=independentCachedBranchMembers7965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7965
def independentCachedBranchMembers7967 : Finset ℕ := ([144,192,1594,1596,1642,1644,1686,1734,2606,2680,2770,2772,3118,3192,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7967 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7967 4 (fun x => (if x<2606 then (if x<1642 then (if x<1594 then (if x<192 then 0 else 1) else (if x<1596 then 1 else 2)) else (if x<1686 then (if x<1644 then 0 else 3) else (if x<1734 then 2 else 3))) else (if x<3118 then (if x<2770 then (if x<2680 then 0 else 2) else (if x<2772 then 2 else 1)) else (if x<3282 then (if x<3192 then 1 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
