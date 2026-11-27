/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch154
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7744 : Finset ℕ := ([34,68,136,238,1594,1628,1642,1652,1678,1702,1720,1768,2606,2646,2714,2732,2738,2762,2772,2786,3126,3150,3174,3192,3228,3242,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7744 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7744 34 4
  · have he : independentCachedBranchMembers7744.erase 34=independentCachedBranchMembers7742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7742
  · have he : independentCachedBranchMembers7744.filter (independentCachedEdge 34)=independentCachedBranchMembers7743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7743
def independentCachedBranchMembers7745 : Finset ℕ := ([34,68,136,238,1594,1628,1678,1768,2606,2646,2714,2786,3126,3150,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7745 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7745 4 (fun x => (if x<2606 then (if x<1594 then (if x<136 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3126 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7746 : Finset ℕ := ([34,68,136,238,1594,1628,1642,1652,1678,1702,1720,1768,2606,2646,2714,2732,2738,2762,2772,2786,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7746 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7746 3252 4
  · have he : independentCachedBranchMembers7746.erase 3252=independentCachedBranchMembers7744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7744
  · have he : independentCachedBranchMembers7746.filter (independentCachedEdge 3252)=independentCachedBranchMembers7745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7745
def independentCachedBranchMembers7747 : Finset ℕ := ([34,68,136,238,1642,1652,1702,1720,2732,2738,2762,2772,3126,3150,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7747 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7747 4 (fun x => (if x<2732 then (if x<1642 then (if x<136 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3126 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7748 : Finset ℕ := ([34,68,136,238,1594,1628,1642,1652,1678,1702,1720,1768,2606,2646,2714,2732,2738,2762,2772,2786,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7748 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7748 3102 4
  · have he : independentCachedBranchMembers7748.erase 3102=independentCachedBranchMembers7746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7746
  · have he : independentCachedBranchMembers7748.filter (independentCachedEdge 3102)=independentCachedBranchMembers7747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7747
def independentCachedBranchMembers7749 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1768,2606,2646,2714,2732,2738,2762,2772,2786] : List ℕ).toFinset
theorem independentCachedBranchBound7749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7749 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7749 4 (fun x => (if x<2606 then (if x<1678 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<2738 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2772 then (if x<2762 then 3 else 3) else (if x<2786 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7750 : Finset ℕ := ([34,68,136,238,1594,1628,1642,1652,1678,1702,1720,1768,2606,2646,2714,2732,2738,2762,2772,2786,3072,3102,3126,3150,3174,3192,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7750 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7750 3072 4
  · have he : independentCachedBranchMembers7750.erase 3072=independentCachedBranchMembers7748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7748
  · have he : independentCachedBranchMembers7750.filter (independentCachedEdge 3072)=independentCachedBranchMembers7749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7749
def independentCachedBranchMembers7751 : Finset ℕ := ([34,36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7751 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7751 2770 5
  · have he : independentCachedBranchMembers7751.erase 2770=independentCachedBranchMembers7739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7739
  · have he : independentCachedBranchMembers7751.filter (independentCachedEdge 2770)=independentCachedBranchMembers7750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7750
def independentCachedBranchMembers7752 : Finset ℕ := ([144,246,1596,1626,1642,1652,1686,1702,1720,1776,2614,2638,2716,2732,2738,2762,2772,2788,3118,3158,3174,3192,3226,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7752 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7752 5 (fun x => (if x<2732 then (if x<1686 then (if x<1626 then (if x<246 then 0 else (if x<1596 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 2 else 2))) else (if x<1776 then (if x<1702 then 0 else (if x<1720 then 2 else 2)) else (if x<2638 then (if x<2614 then 0 else 3) else (if x<2716 then 3 else 3)))) else (if x<3174 then (if x<2772 then (if x<2738 then 1 else (if x<2762 then 0 else 1)) else (if x<3118 then (if x<2788 then 0 else 3) else (if x<3158 then 4 else 4))) else (if x<3252 then (if x<3192 then 2 else (if x<3226 then 2 else 4)) else (if x<3282 then (if x<3276 then 0 else 3) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7753 : Finset ℕ := ([1652,1686,1702,1776,2614,2738,2772,2788,3118,3192,3226,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7753 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7753 4 (fun x => (if x<2772 then (if x<1776 then (if x<1686 then 0 else (if x<1702 then 0 else 1)) else (if x<2614 then 1 else (if x<2738 then 0 else 1))) else (if x<3192 then (if x<2788 then 0 else (if x<3118 then 1 else 2)) else (if x<3226 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7754 : Finset ℕ := ([66,144,246,1596,1626,1642,1652,1686,1702,1720,1776,2614,2638,2716,2732,2738,2762,2772,2788,3118,3158,3174,3192,3226,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7754 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7754 66 4
  · have he : independentCachedBranchMembers7754.erase 66=independentCachedBranchMembers7752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7752
  · have he : independentCachedBranchMembers7754.filter (independentCachedEdge 66)=independentCachedBranchMembers7753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7753
def independentCachedBranchMembers7755 : Finset ℕ := ([1642,1686,1720,1776,2638,2716,2738,2772,3158,3192,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7755 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7755 4 (fun x => (if x<2738 then (if x<1776 then (if x<1686 then 0 else (if x<1720 then 1 else 0)) else (if x<2638 then 1 else (if x<2716 then 0 else 0))) else (if x<3192 then (if x<2772 then 1 else (if x<3158 then 1 else 2)) else (if x<3276 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7756 : Finset ℕ := ([36,66,144,246,1596,1626,1642,1652,1686,1702,1720,1776,2614,2638,2716,2732,2738,2762,2772,2788,3118,3158,3174,3192,3226,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7756 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7756 36 4
  · have he : independentCachedBranchMembers7756.erase 36=independentCachedBranchMembers7754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7754
  · have he : independentCachedBranchMembers7756.filter (independentCachedEdge 36)=independentCachedBranchMembers7755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7755
def independentCachedBranchMembers7757 : Finset ℕ := ([36,66,144,246,1596,1626,1686,1776,2614,2638,2716,2788,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7757 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7757 4 (fun x => (if x<2614 then (if x<1596 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3118 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7758 : Finset ℕ := ([36,66,144,246,1596,1626,1642,1652,1686,1702,1720,1776,2614,2638,2716,2732,2738,2762,2772,2788,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7758 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7758 3242 4
  · have he : independentCachedBranchMembers7758.erase 3242=independentCachedBranchMembers7756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7756
  · have he : independentCachedBranchMembers7758.filter (independentCachedEdge 3242)=independentCachedBranchMembers7757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7757
def independentCachedBranchMembers7759 : Finset ℕ := ([36,66,144,246,1642,1652,1702,1720,2732,2738,2762,2772,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7759 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7759 4 (fun x => (if x<2732 then (if x<1642 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3118 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7760 : Finset ℕ := ([36,66,144,246,1596,1626,1642,1652,1686,1702,1720,1776,2614,2638,2716,2732,2738,2762,2772,2788,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7760 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7760 3102 4
  · have he : independentCachedBranchMembers7760.erase 3102=independentCachedBranchMembers7758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7758
  · have he : independentCachedBranchMembers7760.filter (independentCachedEdge 3102)=independentCachedBranchMembers7759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7759
def independentCachedBranchMembers7761 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1776,2614,2638,2716,2732,2738,2762,2772,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7761 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7761 4 (fun x => (if x<2614 then (if x<1686 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<2738 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2772 then (if x<2762 then 3 else 3) else (if x<2788 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7762 : Finset ℕ := ([36,66,144,246,1596,1626,1642,1652,1686,1702,1720,1776,2614,2638,2716,2732,2738,2762,2772,2788,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7762 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7762 3072 4
  · have he : independentCachedBranchMembers7762.erase 3072=independentCachedBranchMembers7760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7760
  · have he : independentCachedBranchMembers7762.filter (independentCachedEdge 3072)=independentCachedBranchMembers7761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7761
def independentCachedBranchMembers7763 : Finset ℕ := ([34,36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7763 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7763 2764 5
  · have he : independentCachedBranchMembers7763.erase 2764=independentCachedBranchMembers7751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7751
  · have he : independentCachedBranchMembers7763.filter (independentCachedEdge 2764)=independentCachedBranchMembers7762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7762
def independentCachedBranchMembers7764 : Finset ℕ := ([36,246,1594,1596,1644,1650,1652,1702,1768,1776,2606,2614,2662,2680,2732,2738,2786,2788,3118,3126,3174,3192,3242,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7764 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7764 5 (fun x => (if x<2680 then (if x<1652 then (if x<1596 then (if x<246 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 2 else (if x<1650 then 1 else 2))) else (if x<1776 then (if x<1702 then 0 else (if x<1768 then 0 else 2)) else (if x<2614 then (if x<2606 then 1 else 1) else (if x<2662 then 0 else 3)))) else (if x<3126 then (if x<2786 then (if x<2732 then 1 else (if x<2738 then 2 else 1)) else (if x<2788 then 2 else (if x<3118 then 0 else 3))) else (if x<3242 then (if x<3174 then 4 else (if x<3192 then 0 else 4)) else (if x<3298 then (if x<3252 then 4 else 0) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7765 : Finset ℕ := ([36,246,1594,1644,1650,1768,2614,2732,2738,2788,3126,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7765 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7765 4 (fun x => (if x<2614 then (if x<1644 then (if x<246 then 0 else (if x<1594 then 0 else 1)) else (if x<1650 then 1 else (if x<1768 then 2 else 2))) else (if x<2788 then (if x<2732 then 0 else (if x<2738 then 2 else 1)) else (if x<3126 then 0 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7766 : Finset ℕ := ([36,246,1594,1596,1642,1644,1650,1652,1702,1768,1776,2606,2614,2662,2680,2732,2738,2786,2788,3118,3126,3174,3192,3242,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7766 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7766 1642 4
  · have he : independentCachedBranchMembers7766.erase 1642=independentCachedBranchMembers7764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7764
  · have he : independentCachedBranchMembers7766.filter (independentCachedEdge 1642)=independentCachedBranchMembers7765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7765
def independentCachedBranchMembers7767 : Finset ℕ := ([246,1594,1596,1650,1652,1776,2614,2680,2738,3126,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7767 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7767 4 (fun x => (if x<2614 then (if x<1650 then (if x<1594 then 0 else (if x<1596 then 1 else 2)) else (if x<1652 then 0 else (if x<1776 then 1 else 2))) else (if x<3126 then (if x<2680 then 0 else (if x<2738 then 1 else 3)) else (if x<3192 then 3 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7768 : Finset ℕ := ([36,238,246,1594,1596,1642,1644,1650,1652,1702,1768,1776,2606,2614,2662,2680,2732,2738,2786,2788,3118,3126,3174,3192,3242,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7768 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7768 238 4
  · have he : independentCachedBranchMembers7768.erase 238=independentCachedBranchMembers7766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7766
  · have he : independentCachedBranchMembers7768.filter (independentCachedEdge 238)=independentCachedBranchMembers7767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7767
def independentCachedBranchMembers7769 : Finset ℕ := ([36,1596,1644,1652,1768,1776,2680,2732,2788,3192,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7769 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7769 4 (fun x => (if x<2680 then (if x<1652 then (if x<1596 then 0 else (if x<1644 then 0 else 1)) else (if x<1768 then 2 else (if x<1776 then 2 else 1))) else (if x<3192 then (if x<2732 then 1 else (if x<2788 then 0 else 1)) else (if x<3252 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7770 : Finset ℕ := ([34,36,238,246,1594,1596,1642,1644,1650,1652,1702,1768,1776,2606,2614,2662,2680,2732,2738,2786,2788,3118,3126,3174,3192,3242,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7770 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7770 34 4
  · have he : independentCachedBranchMembers7770.erase 34=independentCachedBranchMembers7768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7768
  · have he : independentCachedBranchMembers7770.filter (independentCachedEdge 34)=independentCachedBranchMembers7769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7769
def independentCachedBranchMembers7771 : Finset ℕ := ([238,1596,1642,1652,1768,2606,2662,2680,2732,2738,2788,3126,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7771 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7771 4 (fun x => (if x<2680 then (if x<1652 then (if x<1596 then 0 else (if x<1642 then 1 else 0)) else (if x<2606 then (if x<1768 then 2 else 1) else (if x<2662 then 0 else 2))) else (if x<3126 then (if x<2738 then (if x<2732 then 1 else 1) else (if x<2788 then 3 else 3)) else (if x<3252 then (if x<3242 then 2 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7772 : Finset ℕ := ([1642,1768,2680,2738,3242,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7772 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7772 3 (fun x => (if x<2738 then (if x<1768 then 0 else (if x<2680 then 1 else 0)) else (if x<3242 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7773 : Finset ℕ := ([36,238,1596,1642,1652,1768,2606,2662,2680,2732,2738,2788,3126,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7773 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7773 36 3
  · have he : independentCachedBranchMembers7773.erase 36=independentCachedBranchMembers7771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7771
  · have he : independentCachedBranchMembers7773.filter (independentCachedEdge 36)=independentCachedBranchMembers7772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7772
def independentCachedBranchMembers7774 : Finset ℕ := ([34,36,238,246,1594,1596,1642,1644,1650,1652,1702,1768,1776,2606,2614,2662,2680,2732,2738,2786,2788,3118,3126,3174,3192,3242,3250,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7774 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7774 3250 4
  · have he : independentCachedBranchMembers7774.erase 3250=independentCachedBranchMembers7770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7770
  · have he : independentCachedBranchMembers7774.filter (independentCachedEdge 3250)=independentCachedBranchMembers7773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7773
def independentCachedBranchMembers7775 : Finset ℕ := ([246,1594,1642,1652,1776,2614,2662,2680,2732,2738,2786,3118,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7775 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7775 4 (fun x => (if x<2680 then (if x<1652 then (if x<1594 then 0 else (if x<1642 then 1 else 2)) else (if x<2614 then (if x<1776 then 0 else 1) else (if x<2662 then 0 else 2))) else (if x<3118 then (if x<2738 then (if x<2732 then 1 else 3) else (if x<2786 then 1 else 3)) else (if x<3252 then (if x<3242 then 2 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
