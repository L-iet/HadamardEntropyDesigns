/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch155
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7776 : Finset ℕ := ([1652,1776,2680,2732,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7776 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7776 3 (fun x => (if x<2732 then (if x<1776 then 0 else (if x<2680 then 1 else 0)) else (if x<3252 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7777 : Finset ℕ := ([34,246,1594,1642,1652,1776,2614,2662,2680,2732,2738,2786,3118,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7777 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7777 34 3
  · have he : independentCachedBranchMembers7777.erase 34=independentCachedBranchMembers7775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7775
  · have he : independentCachedBranchMembers7777.filter (independentCachedEdge 34)=independentCachedBranchMembers7776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7776
def independentCachedBranchMembers7778 : Finset ℕ := ([34,36,238,246,1594,1596,1642,1644,1650,1652,1702,1768,1776,2606,2614,2662,2680,2732,2738,2786,2788,3118,3126,3174,3192,3242,3244,3250,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7778 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7778 3244 4
  · have he : independentCachedBranchMembers7778.erase 3244=independentCachedBranchMembers7774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7774
  · have he : independentCachedBranchMembers7778.filter (independentCachedEdge 3244)=independentCachedBranchMembers7777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7777
def independentCachedBranchMembers7779 : Finset ℕ := ([34,36,238,246,1594,1596,1768,1776,2606,2614,2786,2788,3118,3126,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7779 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7779 4 (fun x => (if x<2606 then (if x<1594 then (if x<238 then (if x<36 then 0 else 1) else (if x<246 then 0 else 1)) else (if x<1768 then (if x<1596 then 2 else 3) else (if x<1776 then 2 else 3))) else (if x<3118 then (if x<2786 then (if x<2614 then 0 else 1) else (if x<2788 then 0 else 1)) else (if x<3298 then (if x<3126 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7780 : Finset ℕ := ([34,36,238,246,1594,1596,1642,1644,1650,1652,1702,1720,1768,1776,2606,2614,2662,2680,2732,2738,2786,2788,3118,3126,3174,3192,3242,3244,3250,3252,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7780 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7780 1720 4
  · have he : independentCachedBranchMembers7780.erase 1720=independentCachedBranchMembers7778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7778
  · have he : independentCachedBranchMembers7780.filter (independentCachedEdge 1720)=independentCachedBranchMembers7779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7779
def independentCachedBranchMembers7781 : Finset ℕ := ([34,36,66,68,136,144,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7781 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7781 222 5
  · have he : independentCachedBranchMembers7781.erase 222=independentCachedBranchMembers7763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7763
  · have he : independentCachedBranchMembers7781.filter (independentCachedEdge 222)=independentCachedBranchMembers7780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7780
def independentCachedBranchMembers7782 : Finset ℕ := ([68,144,1626,1628,1642,1644,1652,1678,1686,1720,2638,2662,2680,2714,2732,2738,3150,3158,3174,3192,3226,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7782 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7782 5 (fun x => (if x<2680 then (if x<1652 then (if x<1628 then (if x<144 then 0 else (if x<1626 then 0 else 1)) else (if x<1642 then 2 else (if x<1644 then 2 else 0))) else (if x<1720 then (if x<1678 then 1 else (if x<1686 then 2 else 1)) else (if x<2638 then 0 else (if x<2662 then 0 else 3)))) else (if x<3174 then (if x<2738 then (if x<2714 then 1 else (if x<2732 then 0 else 3)) else (if x<3150 then 3 else (if x<3158 then 2 else 4))) else (if x<3228 then (if x<3192 then 0 else (if x<3226 then 2 else 4)) else (if x<3242 then 2 else (if x<3252 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7783 : Finset ℕ := ([68,1626,1644,1652,2662,2714,2732,3150,3158,3192,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound7783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7783 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7783 4 (fun x => (if x<2732 then (if x<1652 then (if x<1626 then 0 else (if x<1644 then 1 else 0)) else (if x<2662 then 1 else (if x<2714 then 0 else 1))) else (if x<3192 then (if x<3150 then 2 else (if x<3158 then 0 else 2)) else (if x<3228 then 3 else (if x<3242 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7784 : Finset ℕ := ([68,144,1626,1628,1642,1644,1652,1678,1686,1720,2638,2662,2680,2714,2716,2732,2738,3150,3158,3174,3192,3226,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7784 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7784 2716 4
  · have he : independentCachedBranchMembers7784.erase 2716=independentCachedBranchMembers7782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7782
  · have he : independentCachedBranchMembers7784.filter (independentCachedEdge 2716)=independentCachedBranchMembers7783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7783
def independentCachedBranchMembers7785 : Finset ℕ := ([144,1642,1644,1678,2638,2662,2732,3158,3192,3226,3228,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7785 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7785 4 (fun x => (if x<2732 then (if x<1678 then (if x<1642 then 0 else (if x<1644 then 0 else 1)) else (if x<2638 then 1 else (if x<2662 then 0 else 2))) else (if x<3226 then (if x<3158 then 1 else (if x<3192 then 2 else 3)) else (if x<3228 then 2 else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7786 : Finset ℕ := ([68,144,1626,1628,1642,1644,1652,1678,1686,1720,2638,2646,2662,2680,2714,2716,2732,2738,3150,3158,3174,3192,3226,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7786 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7786 2646 4
  · have he : independentCachedBranchMembers7786.erase 2646=independentCachedBranchMembers7784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7784
  · have he : independentCachedBranchMembers7786.filter (independentCachedEdge 2646)=independentCachedBranchMembers7785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7785
def independentCachedBranchMembers7787 : Finset ℕ := ([68,144,1626,1642,1652,1678,2638,2714,3150,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7787 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7787 4 (fun x => (if x<2638 then (if x<1642 then (if x<144 then 0 else (if x<1626 then 0 else 1)) else (if x<1652 then 2 else (if x<1678 then 1 else 2))) else (if x<3226 then (if x<2714 then 0 else (if x<3150 then 0 else 2)) else (if x<3242 then 1 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7788 : Finset ℕ := ([68,144,1626,1628,1642,1644,1650,1652,1678,1686,1720,2638,2646,2662,2680,2714,2716,2732,2738,3150,3158,3174,3192,3226,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7788 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7788 1650 4
  · have he : independentCachedBranchMembers7788.erase 1650=independentCachedBranchMembers7786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7786
  · have he : independentCachedBranchMembers7788.filter (independentCachedEdge 1650)=independentCachedBranchMembers7787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7787
def independentCachedBranchMembers7789 : Finset ℕ := ([144,1626,1628,1642,1644,1686,2638,2680,2738,3150,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7789 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7789 4 (fun x => (if x<2638 then (if x<1642 then (if x<1626 then 0 else (if x<1628 then 1 else 2)) else (if x<1644 then 0 else (if x<1686 then 1 else 2))) else (if x<3150 then (if x<2680 then 0 else (if x<2738 then 1 else 2)) else (if x<3192 then 3 else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7790 : Finset ℕ := ([68,136,144,1626,1628,1642,1644,1650,1652,1678,1686,1720,2638,2646,2662,2680,2714,2716,2732,2738,3150,3158,3174,3192,3226,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7790 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7790 136 4
  · have he : independentCachedBranchMembers7790.erase 136=independentCachedBranchMembers7788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7788
  · have he : independentCachedBranchMembers7790.filter (independentCachedEdge 136)=independentCachedBranchMembers7789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7789
def independentCachedBranchMembers7791 : Finset ℕ := ([68,1628,1644,1652,1678,1686,2680,2714,2738,3192,3226,3242] : List ℕ).toFinset
theorem independentCachedBranchBound7791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7791 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7791 4 (fun x => (if x<2680 then (if x<1652 then (if x<1628 then 0 else (if x<1644 then 0 else 1)) else (if x<1678 then 2 else (if x<1686 then 1 else 2))) else (if x<3192 then (if x<2714 then 1 else (if x<2738 then 1 else 0)) else (if x<3226 then 2 else (if x<3242 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7792 : Finset ℕ := ([66,68,136,144,1626,1628,1642,1644,1650,1652,1678,1686,1720,2638,2646,2662,2680,2714,2716,2732,2738,3150,3158,3174,3192,3226,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7792 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7792 66 4
  · have he : independentCachedBranchMembers7792.erase 66=independentCachedBranchMembers7790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7790
  · have he : independentCachedBranchMembers7792.filter (independentCachedEdge 66)=independentCachedBranchMembers7791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7791
def independentCachedBranchMembers7793 : Finset ℕ := ([136,1626,1642,1652,1678,2646,2662,2680,2716,2732,2738,3150,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7793 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7793 4 (fun x => (if x<2680 then (if x<1652 then (if x<1626 then 0 else (if x<1642 then 1 else 2)) else (if x<2646 then (if x<1678 then 0 else 1) else (if x<2662 then 0 else 2))) else (if x<3150 then (if x<2732 then (if x<2716 then 1 else 3) else (if x<2738 then 1 else 3)) else (if x<3242 then (if x<3226 then 2 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7794 : Finset ℕ := ([1652,1678,2680,2738,3226,3242] : List ℕ).toFinset
theorem independentCachedBranchBound7794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7794 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7794 3 (fun x => (if x<2738 then (if x<1678 then 0 else (if x<2680 then 1 else 0)) else (if x<3226 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7795 : Finset ℕ := ([66,136,1626,1642,1652,1678,2646,2662,2680,2716,2732,2738,3150,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7795 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7795 66 3
  · have he : independentCachedBranchMembers7795.erase 66=independentCachedBranchMembers7793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7793
  · have he : independentCachedBranchMembers7795.filter (independentCachedEdge 66)=independentCachedBranchMembers7794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7794
def independentCachedBranchMembers7796 : Finset ℕ := ([66,68,136,144,1626,1628,1642,1644,1650,1652,1678,1686,1720,2638,2646,2662,2680,2714,2716,2732,2738,3150,3158,3174,3192,3226,3228,3242,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7796 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7796 3250 4
  · have he : independentCachedBranchMembers7796.erase 3250=independentCachedBranchMembers7792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7792
  · have he : independentCachedBranchMembers7796.filter (independentCachedEdge 3250)=independentCachedBranchMembers7795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7795
def independentCachedBranchMembers7797 : Finset ℕ := ([144,1628,1642,1652,1686,2638,2662,2680,2714,2732,2738,3158,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7797 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7797 4 (fun x => (if x<2680 then (if x<1652 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<2638 then (if x<1686 then 2 else 1) else (if x<2662 then 0 else 2))) else (if x<3158 then (if x<2732 then (if x<2714 then 1 else 3) else (if x<2738 then 3 else 1)) else (if x<3242 then (if x<3228 then 2 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7798 : Finset ℕ := ([1642,1686,2680,2732,3228,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7798 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7798 3 (fun x => (if x<2732 then (if x<1686 then 0 else (if x<2680 then 1 else 0)) else (if x<3228 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7799 : Finset ℕ := ([68,144,1628,1642,1652,1686,2638,2662,2680,2714,2732,2738,3158,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7799 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7799 68 3
  · have he : independentCachedBranchMembers7799.erase 68=independentCachedBranchMembers7797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7797
  · have he : independentCachedBranchMembers7799.filter (independentCachedEdge 68)=independentCachedBranchMembers7798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7798
def independentCachedBranchMembers7800 : Finset ℕ := ([66,68,136,144,1626,1628,1642,1644,1650,1652,1678,1686,1720,2638,2646,2662,2680,2714,2716,2732,2738,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7800 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7800 3244 4
  · have he : independentCachedBranchMembers7800.erase 3244=independentCachedBranchMembers7796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7796
  · have he : independentCachedBranchMembers7800.filter (independentCachedEdge 3244)=independentCachedBranchMembers7799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7799
def independentCachedBranchMembers7801 : Finset ℕ := ([66,68,136,144,1626,1628,1678,1686,2638,2646,2714,2716,3150,3158,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7801 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7801 4 (fun x => (if x<2638 then (if x<1626 then (if x<136 then (if x<68 then 0 else 1) else (if x<144 then 0 else 1)) else (if x<1678 then (if x<1628 then 2 else 3) else (if x<1686 then 2 else 3))) else (if x<3150 then (if x<2714 then (if x<2646 then 1 else 0) else (if x<2716 then 1 else 0)) else (if x<3226 then (if x<3158 then 2 else 3) else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7802 : Finset ℕ := ([66,68,136,144,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,2638,2646,2662,2680,2714,2716,2732,2738,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7802 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7802 1702 4
  · have he : independentCachedBranchMembers7802.erase 1702=independentCachedBranchMembers7800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7800
  · have he : independentCachedBranchMembers7802.filter (independentCachedEdge 1702)=independentCachedBranchMembers7801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7801
def independentCachedBranchMembers7803 : Finset ℕ := ([34,36,66,68,136,144,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7803 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7803 192 5
  · have he : independentCachedBranchMembers7803.erase 192=independentCachedBranchMembers7781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7781
  · have he : independentCachedBranchMembers7803.filter (independentCachedEdge 192)=independentCachedBranchMembers7802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7802
def independentCachedBranchMembers7804 : Finset ℕ := ([66,238,1596,1628,1642,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2716,2762,2772,2786,3118,3150,3174,3192,3228,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7804 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7804 5 (fun x => (if x<2662 then (if x<1702 then (if x<1628 then (if x<238 then 0 else (if x<1596 then 0 else 1)) else (if x<1642 then 2 else (if x<1678 then 0 else 1))) else (if x<1752 then (if x<1720 then 3 else (if x<1734 then 2 else 0)) else (if x<2606 then (if x<1776 then 1 else 3) else (if x<2638 then 1 else 0)))) else (if x<3150 then (if x<2762 then (if x<2680 then 4 else (if x<2716 then 1 else 1)) else (if x<2786 then (if x<2772 then 1 else 4) else (if x<3118 then 0 else 3))) else (if x<3228 then (if x<3174 then 2 else (if x<3192 then 0 else 2)) else (if x<3252 then (if x<3242 then 2 else 2) else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7805 : Finset ℕ := ([238,1596,1628,1678,1702,1734,2680,2762,2786,3192,3242,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7805 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7805 4 (fun x => (if x<2680 then (if x<1678 then (if x<1596 then 0 else (if x<1628 then 1 else 2)) else (if x<1702 then 0 else (if x<1734 then 1 else 2))) else (if x<3192 then (if x<2762 then 1 else (if x<2786 then 0 else 1)) else (if x<3242 then 2 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7806 : Finset ℕ := ([66,144,238,1596,1628,1642,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2716,2762,2772,2786,3118,3150,3174,3192,3228,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7806 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7806 144 4
  · have he : independentCachedBranchMembers7806.erase 144=independentCachedBranchMembers7804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7804
  · have he : independentCachedBranchMembers7806.filter (independentCachedEdge 144)=independentCachedBranchMembers7805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7805
def independentCachedBranchMembers7807 : Finset ℕ := ([66,1596,1678,1720,1734,1776,2638,2680,2762,3150,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7807 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7807 4 (fun x => (if x<2638 then (if x<1720 then (if x<1596 then 0 else (if x<1678 then 0 else 1)) else (if x<1734 then 1 else (if x<1776 then 2 else 2))) else (if x<3150 then (if x<2680 then 1 else (if x<2762 then 1 else 0)) else (if x<3192 then 2 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
