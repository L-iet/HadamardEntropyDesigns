/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch156
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7808 : Finset ℕ := ([34,66,144,238,1596,1628,1642,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2716,2762,2772,2786,3118,3150,3174,3192,3228,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7808 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7808 34 4
  · have he : independentCachedBranchMembers7808.erase 34=independentCachedBranchMembers7806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7806
  · have he : independentCachedBranchMembers7808.filter (independentCachedEdge 34)=independentCachedBranchMembers7807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7807
def independentCachedBranchMembers7809 : Finset ℕ := ([238,1596,1678,1702,1720,2638,2662,2680,2762,2772,2786,3118,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7809 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7809 4 (fun x => (if x<2680 then (if x<1702 then (if x<1596 then 0 else (if x<1678 then 1 else 0)) else (if x<2638 then (if x<1720 then 1 else 2) else (if x<2662 then 0 else 2))) else (if x<3118 then (if x<2772 then (if x<2762 then 1 else 3) else (if x<2786 then 3 else 1)) else (if x<3242 then (if x<3228 then 0 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7810 : Finset ℕ := ([1678,1702,2680,2772,3118,3242] : List ℕ).toFinset
theorem independentCachedBranchBound7810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7810 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7810 3 (fun x => (if x<2772 then (if x<1702 then 0 else (if x<2680 then 1 else 0)) else (if x<3118 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7811 : Finset ℕ := ([66,238,1596,1678,1702,1720,2638,2662,2680,2762,2772,2786,3118,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7811 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7811 66 3
  · have he : independentCachedBranchMembers7811.erase 66=independentCachedBranchMembers7809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7809
  · have he : independentCachedBranchMembers7811.filter (independentCachedEdge 66)=independentCachedBranchMembers7810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7810
def independentCachedBranchMembers7812 : Finset ℕ := ([34,66,144,238,1596,1628,1642,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2716,2762,2772,2786,3118,3150,3174,3192,3228,3242,3252,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7812 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7812 3284 4
  · have he : independentCachedBranchMembers7812.erase 3284=independentCachedBranchMembers7808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7808
  · have he : independentCachedBranchMembers7812.filter (independentCachedEdge 3284)=independentCachedBranchMembers7811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7811
def independentCachedBranchMembers7813 : Finset ℕ := ([144,1628,1702,1720,1776,2606,2662,2680,2716,2762,2772,3150,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7813 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7813 4 (fun x => (if x<2680 then (if x<1720 then (if x<1628 then 0 else (if x<1702 then 1 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2662 then 2 else 0))) else (if x<3150 then (if x<2762 then (if x<2716 then 1 else 3) else (if x<2772 then 3 else 1)) else (if x<3252 then (if x<3242 then 0 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7814 : Finset ℕ := ([1720,1776,2680,2762,3150,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7814 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7814 3 (fun x => (if x<2762 then (if x<1776 then 0 else (if x<2680 then 1 else 0)) else (if x<3150 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7815 : Finset ℕ := ([34,144,1628,1702,1720,1776,2606,2662,2680,2716,2762,2772,3150,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7815 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7815 34 3
  · have he : independentCachedBranchMembers7815.erase 34=independentCachedBranchMembers7813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7813
  · have he : independentCachedBranchMembers7815.filter (independentCachedEdge 34)=independentCachedBranchMembers7814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7814
def independentCachedBranchMembers7816 : Finset ℕ := ([34,66,144,238,1596,1628,1642,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2716,2762,2772,2786,3118,3150,3174,3192,3228,3242,3252,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7816 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7816 3274 4
  · have he : independentCachedBranchMembers7816.erase 3274=independentCachedBranchMembers7812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7812
  · have he : independentCachedBranchMembers7816.filter (independentCachedEdge 3274)=independentCachedBranchMembers7815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7815
def independentCachedBranchMembers7817 : Finset ℕ := ([34,66,144,238,1596,1628,1678,1776,2606,2638,2716,2786,3118,3150,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7817 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7817 4 (fun x => (if x<2606 then (if x<1596 then (if x<144 then (if x<66 then 0 else 1) else (if x<238 then 0 else 1)) else (if x<1678 then (if x<1628 then 2 else 3) else (if x<1776 then 2 else 3))) else (if x<3118 then (if x<2716 then (if x<2638 then 0 else 1) else (if x<2786 then 0 else 1)) else (if x<3228 then (if x<3150 then 2 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7818 : Finset ℕ := ([34,66,144,238,1596,1628,1642,1652,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2716,2762,2772,2786,3118,3150,3174,3192,3228,3242,3252,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7818 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7818 1652 4
  · have he : independentCachedBranchMembers7818.erase 1652=independentCachedBranchMembers7816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7816
  · have he : independentCachedBranchMembers7818.filter (independentCachedEdge 1652)=independentCachedBranchMembers7817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7817
def independentCachedBranchMembers7819 : Finset ℕ := ([18,34,36,66,68,136,144,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7819 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7819 18 5
  · have he : independentCachedBranchMembers7819.erase 18=independentCachedBranchMembers7803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7803
  · have he : independentCachedBranchMembers7819.filter (independentCachedEdge 18)=independentCachedBranchMembers7818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7818
def independentCachedBranchMembers7820 : Finset ℕ := ([68,246,1594,1626,1652,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2714,2762,2772,2788,3126,3158,3174,3192,3226,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7820 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7820 5 (fun x => (if x<2662 then (if x<1702 then (if x<1626 then (if x<246 then 0 else (if x<1594 then 0 else 1)) else (if x<1652 then 2 else (if x<1686 then 0 else 1))) else (if x<1752 then (if x<1720 then 3 else (if x<1734 then 2 else 0)) else (if x<2614 then (if x<1768 then 1 else 3) else (if x<2646 then 1 else 0)))) else (if x<3158 then (if x<2762 then (if x<2680 then 4 else (if x<2714 then 1 else 1)) else (if x<2788 then (if x<2772 then 4 else 1) else (if x<3126 then 0 else 3))) else (if x<3226 then (if x<3174 then 2 else (if x<3192 then 0 else 2)) else (if x<3252 then (if x<3242 then 2 else 3) else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7821 : Finset ℕ := ([246,1594,1626,1686,1702,1734,2680,2772,2788,3192,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7821 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7821 4 (fun x => (if x<2680 then (if x<1686 then (if x<1594 then 0 else (if x<1626 then 1 else 2)) else (if x<1702 then 0 else (if x<1734 then 1 else 2))) else (if x<3192 then (if x<2772 then 1 else (if x<2788 then 0 else 1)) else (if x<3252 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7822 : Finset ℕ := ([68,136,246,1594,1626,1652,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2714,2762,2772,2788,3126,3158,3174,3192,3226,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7822 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7822 136 4
  · have he : independentCachedBranchMembers7822.erase 136=independentCachedBranchMembers7820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7820
  · have he : independentCachedBranchMembers7822.filter (independentCachedEdge 136)=independentCachedBranchMembers7821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7821
def independentCachedBranchMembers7823 : Finset ℕ := ([68,1594,1686,1720,1734,1768,2646,2680,2772,3158,3192,3242] : List ℕ).toFinset
theorem independentCachedBranchBound7823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7823 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7823 4 (fun x => (if x<2646 then (if x<1720 then (if x<1594 then 0 else (if x<1686 then 0 else 1)) else (if x<1734 then 1 else (if x<1768 then 2 else 2))) else (if x<3158 then (if x<2680 then 1 else (if x<2772 then 1 else 0)) else (if x<3192 then 2 else (if x<3242 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7824 : Finset ℕ := ([36,68,136,246,1594,1626,1652,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2714,2762,2772,2788,3126,3158,3174,3192,3226,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7824 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7824 36 4
  · have he : independentCachedBranchMembers7824.erase 36=independentCachedBranchMembers7822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7822
  · have he : independentCachedBranchMembers7824.filter (independentCachedEdge 36)=independentCachedBranchMembers7823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7823
def independentCachedBranchMembers7825 : Finset ℕ := ([136,1626,1702,1720,1768,2614,2662,2680,2714,2762,2772,3158,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7825 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7825 4 (fun x => (if x<2680 then (if x<1720 then (if x<1626 then 0 else (if x<1702 then 1 else 2)) else (if x<2614 then (if x<1768 then 0 else 1) else (if x<2662 then 2 else 0))) else (if x<3158 then (if x<2762 then (if x<2714 then 1 else 3) else (if x<2772 then 1 else 3)) else (if x<3252 then (if x<3242 then 0 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7826 : Finset ℕ := ([1720,1768,2680,2772,3158,3242] : List ℕ).toFinset
theorem independentCachedBranchBound7826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7826 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7826 3 (fun x => (if x<2772 then (if x<1768 then 0 else (if x<2680 then 1 else 0)) else (if x<3158 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7827 : Finset ℕ := ([36,136,1626,1702,1720,1768,2614,2662,2680,2714,2762,2772,3158,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7827 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7827 36 3
  · have he : independentCachedBranchMembers7827.erase 36=independentCachedBranchMembers7825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7825
  · have he : independentCachedBranchMembers7827.filter (independentCachedEdge 36)=independentCachedBranchMembers7826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7826
def independentCachedBranchMembers7828 : Finset ℕ := ([36,68,136,246,1594,1626,1652,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2714,2762,2772,2788,3126,3158,3174,3192,3226,3242,3252,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7828 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7828 3284 4
  · have he : independentCachedBranchMembers7828.erase 3284=independentCachedBranchMembers7824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7824
  · have he : independentCachedBranchMembers7828.filter (independentCachedEdge 3284)=independentCachedBranchMembers7827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7827
def independentCachedBranchMembers7829 : Finset ℕ := ([246,1594,1686,1702,1720,2646,2662,2680,2762,2772,2788,3126,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7829 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7829 4 (fun x => (if x<2680 then (if x<1702 then (if x<1594 then 0 else (if x<1686 then 1 else 0)) else (if x<2646 then (if x<1720 then 1 else 2) else (if x<2662 then 0 else 2))) else (if x<3126 then (if x<2772 then (if x<2762 then 1 else 3) else (if x<2788 then 3 else 1)) else (if x<3242 then (if x<3226 then 0 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7830 : Finset ℕ := ([1686,1702,2680,2762,3126,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7830 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7830 3 (fun x => (if x<2762 then (if x<1702 then 0 else (if x<2680 then 1 else 0)) else (if x<3126 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7831 : Finset ℕ := ([68,246,1594,1686,1702,1720,2646,2662,2680,2762,2772,2788,3126,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7831 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7831 68 3
  · have he : independentCachedBranchMembers7831.erase 68=independentCachedBranchMembers7829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7829
  · have he : independentCachedBranchMembers7831.filter (independentCachedEdge 68)=independentCachedBranchMembers7830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7830
def independentCachedBranchMembers7832 : Finset ℕ := ([36,68,136,246,1594,1626,1652,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2714,2762,2772,2788,3126,3158,3174,3192,3226,3242,3252,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7832 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7832 3274 4
  · have he : independentCachedBranchMembers7832.erase 3274=independentCachedBranchMembers7828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7828
  · have he : independentCachedBranchMembers7832.filter (independentCachedEdge 3274)=independentCachedBranchMembers7831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7831
def independentCachedBranchMembers7833 : Finset ℕ := ([36,68,136,246,1594,1626,1686,1768,2614,2646,2714,2788,3126,3158,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7833 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7833 4 (fun x => (if x<2614 then (if x<1594 then (if x<136 then (if x<68 then 0 else 1) else (if x<246 then 0 else 1)) else (if x<1686 then (if x<1626 then 2 else 3) else (if x<1768 then 2 else 3))) else (if x<3126 then (if x<2714 then (if x<2646 then 0 else 1) else (if x<2788 then 0 else 1)) else (if x<3226 then (if x<3158 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7834 : Finset ℕ := ([36,68,136,246,1594,1626,1642,1652,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2714,2762,2772,2788,3126,3158,3174,3192,3226,3242,3252,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7834 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7834 1642 4
  · have he : independentCachedBranchMembers7834.erase 1642=independentCachedBranchMembers7832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7832
  · have he : independentCachedBranchMembers7834.filter (independentCachedEdge 1642)=independentCachedBranchMembers7833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7833
def independentCachedBranchMembers7835 : Finset ℕ := ([12,18,34,36,66,68,136,144,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7835 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7835 12 5
  · have he : independentCachedBranchMembers7835.erase 12=independentCachedBranchMembers7819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7819
  · have he : independentCachedBranchMembers7835.filter (independentCachedEdge 12)=independentCachedBranchMembers7834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7834
def independentCachedBranchMembers7836 : Finset ℕ := ([136,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3118,3158,3174,3192,3226,3242,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7836 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7836 5 (fun x => (if x<2732 then (if x<1678 then (if x<1628 then (if x<238 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1768 then (if x<1734 then 0 else (if x<1752 then 2 else 2)) else (if x<2638 then (if x<2614 then 0 else 3) else (if x<2716 then 3 else 3)))) else (if x<3174 then (if x<2772 then (if x<2738 then 0 else (if x<2762 then 1 else 0)) else (if x<3118 then (if x<2788 then 1 else 3) else (if x<3158 then 4 else 4))) else (if x<3242 then (if x<3192 then 2 else (if x<3226 then 2 else 4)) else (if x<3276 then (if x<3252 then 0 else 3) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7837 : Finset ℕ := ([1650,1678,1752,1768,2614,2716,2732,2762,3118,3192,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7837 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7837 4 (fun x => (if x<2732 then (if x<1768 then (if x<1678 then 0 else (if x<1752 then 1 else 0)) else (if x<2614 then 1 else (if x<2716 then 0 else 0))) else (if x<3192 then (if x<2762 then 1 else (if x<3118 then 1 else 2)) else (if x<3252 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7838 : Finset ℕ := ([68,136,238,1594,1628,1644,1650,1678,1734,1752,1768,2614,2638,2716,2732,2738,2762,2772,2788,3118,3158,3174,3192,3226,3242,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7838 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7838 68 4
  · have he : independentCachedBranchMembers7838.erase 68=independentCachedBranchMembers7836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7836
  · have he : independentCachedBranchMembers7838.filter (independentCachedEdge 68)=independentCachedBranchMembers7837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7837
def independentCachedBranchMembers7839 : Finset ℕ := ([1644,1678,1734,1768,2638,2732,2762,2788,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7839 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7839 4 (fun x => (if x<2762 then (if x<1768 then (if x<1678 then 0 else (if x<1734 then 0 else 1)) else (if x<2638 then 1 else (if x<2732 then 0 else 0))) else (if x<3192 then (if x<2788 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
