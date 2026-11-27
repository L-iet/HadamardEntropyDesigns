/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch151
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7648 : Finset ℕ := ([1626,1644,1652,1678,1686,1720,1734,1768,1776,2638,2646,2680,2714,2732,2762,2788,3150,3158,3192,3226,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7648 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7648 5 (fun x => (if x<2680 then (if x<1720 then (if x<1652 then (if x<1644 then 0 else 0) else (if x<1678 then 1 else (if x<1686 then 0 else 1))) else (if x<1776 then (if x<1734 then 0 else (if x<1768 then 2 else 2)) else (if x<2638 then 3 else (if x<2646 then 0 else 1)))) else (if x<3158 then (if x<2762 then (if x<2714 then 0 else (if x<2732 then 0 else 0)) else (if x<2788 then 2 else (if x<3150 then 2 else 3))) else (if x<3252 then (if x<3192 then 4 else (if x<3226 then 3 else 4)) else (if x<3282 then 4 else (if x<3300 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7649 : Finset ℕ := ([1644,1652,1720,1734,2638,2646,2714,2788,3150,3158,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7649 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7649 4 (fun x => (if x<2714 then (if x<1734 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<2638 then 1 else (if x<2646 then 0 else 1))) else (if x<3158 then (if x<2788 then 0 else (if x<3150 then 1 else 2)) else (if x<3226 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7650 : Finset ℕ := ([1596,1626,1644,1652,1678,1686,1720,1734,1768,1776,2638,2646,2680,2714,2732,2762,2788,3150,3158,3192,3226,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7650 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7650 1596 4
  · have he : independentCachedBranchMembers7650.erase 1596=independentCachedBranchMembers7648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7648
  · have he : independentCachedBranchMembers7650.filter (independentCachedEdge 1596)=independentCachedBranchMembers7649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7649
def independentCachedBranchMembers7651 : Finset ℕ := ([1644,1652,1678,1686,1768,1776,2680,2714,2788,3192,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7651 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7651 4 (fun x => (if x<2680 then (if x<1686 then (if x<1652 then 0 else (if x<1678 then 1 else 0)) else (if x<1768 then 1 else (if x<1776 then 2 else 3))) else (if x<3192 then (if x<2714 then 0 else (if x<2788 then 0 else 2)) else (if x<3226 then 1 else (if x<3300 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7652 : Finset ℕ := ([66,1596,1626,1644,1652,1678,1686,1720,1734,1768,1776,2638,2646,2680,2714,2732,2762,2788,3150,3158,3192,3226,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7652 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7652 66 4
  · have he : independentCachedBranchMembers7652.erase 66=independentCachedBranchMembers7650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7650
  · have he : independentCachedBranchMembers7652.filter (independentCachedEdge 66)=independentCachedBranchMembers7651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7651
def independentCachedBranchMembers7653 : Finset ℕ := ([1686,1720,1734,1768,1776,2638,2646,2680,3150,3158,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7653 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7653 4 (fun x => (if x<2638 then (if x<1734 then (if x<1720 then 0 else 0) else (if x<1768 then 1 else (if x<1776 then 1 else 2))) else (if x<3150 then (if x<2646 then 2 else (if x<2680 then 0 else 0)) else (if x<3158 then 3 else (if x<3192 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7654 : Finset ℕ := ([1686,1734,1776,2646,3158] : List ℕ).toFinset
theorem independentCachedBranchBound7654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7654 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7654 3 (fun x => (if x<1776 then (if x<1734 then 0 else 1) else (if x<2646 then 0 else (if x<3158 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7655 : Finset ℕ := ([1678,1686,1720,1734,1768,1776,2638,2646,2680,3150,3158,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7655 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7655 1678 3
  · have he : independentCachedBranchMembers7655.erase 1678=independentCachedBranchMembers7653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7653
  · have he : independentCachedBranchMembers7655.filter (independentCachedEdge 1678)=independentCachedBranchMembers7654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7654
def independentCachedBranchMembers7656 : Finset ℕ := ([36,66,1596,1626,1644,1652,1678,1686,1720,1734,1768,1776,2638,2646,2680,2714,2732,2762,2788,3150,3158,3192,3226,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7656 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7656 36 4
  · have he : independentCachedBranchMembers7656.erase 36=independentCachedBranchMembers7652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7652
  · have he : independentCachedBranchMembers7656.filter (independentCachedEdge 36)=independentCachedBranchMembers7655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7655
def independentCachedBranchMembers7657 : Finset ℕ := ([34,36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7657 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7657 34 5
  · have he : independentCachedBranchMembers7657.erase 34=independentCachedBranchMembers7647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7647
  · have he : independentCachedBranchMembers7657.filter (independentCachedEdge 34)=independentCachedBranchMembers7656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7656
def independentCachedBranchMembers7658 : Finset ℕ := ([1596,1626,1644,1650,1678,1702,1720,1768,2614,2638,2662,2680,2714,2732,2762,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7658 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7658 5 (fun x => (if x<2714 then (if x<1720 then (if x<1650 then (if x<1626 then 0 else (if x<1644 then 0 else 1)) else (if x<1678 then 1 else (if x<1702 then 0 else 1))) else (if x<2638 then (if x<1768 then 1 else (if x<2614 then 0 else 2)) else (if x<2662 then 2 else (if x<2680 then 1 else 0)))) else (if x<3158 then (if x<2772 then (if x<2732 then 2 else (if x<2762 then 0 else 0)) else (if x<2786 then 2 else (if x<3118 then 2 else 3))) else (if x<3252 then (if x<3228 then 3 else (if x<3242 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7659 : Finset ℕ := ([1596,1626,1650,1720,2614,2680,2714,2772,3158,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7659 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7659 4 (fun x => (if x<2714 then (if x<1720 then (if x<1626 then 0 else (if x<1650 then 0 else 1)) else (if x<2614 then 1 else (if x<2680 then 2 else 0))) else (if x<3228 then (if x<2772 then 2 else (if x<3158 then 2 else 1)) else (if x<3252 then 1 else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7660 : Finset ℕ := ([238,1596,1626,1644,1650,1678,1702,1720,1768,2614,2638,2662,2680,2714,2732,2762,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7660 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7660 238 4
  · have he : independentCachedBranchMembers7660.erase 238=independentCachedBranchMembers7658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7658
  · have he : independentCachedBranchMembers7660.filter (independentCachedEdge 238)=independentCachedBranchMembers7659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7659
def independentCachedBranchMembers7661 : Finset ℕ := ([1596,1626,1644,1702,2638,2680,2772,2786,3118,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7661 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7661 4 (fun x => (if x<2772 then (if x<1702 then (if x<1626 then 0 else (if x<1644 then 0 else 1)) else (if x<2638 then 1 else (if x<2680 then 2 else 0))) else (if x<3252 then (if x<2786 then 2 else (if x<3118 then 2 else 1)) else (if x<3282 then 3 else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7662 : Finset ℕ := ([136,238,1596,1626,1644,1650,1678,1702,1720,1768,2614,2638,2662,2680,2714,2732,2762,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7662 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7662 136 4
  · have he : independentCachedBranchMembers7662.erase 136=independentCachedBranchMembers7660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7660
  · have he : independentCachedBranchMembers7662.filter (independentCachedEdge 136)=independentCachedBranchMembers7661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7661
def independentCachedBranchMembers7663 : Finset ℕ := ([1644,1678,1702,1768,2614,2680,2714,2772,3118,3242,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7663 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7663 4 (fun x => (if x<2714 then (if x<1768 then (if x<1678 then 0 else (if x<1702 then 0 else 1)) else (if x<2614 then 1 else (if x<2680 then 1 else 0))) else (if x<3242 then (if x<2772 then 0 else (if x<3118 then 2 else 2)) else (if x<3276 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7664 : Finset ℕ := ([66,136,238,1596,1626,1644,1650,1678,1702,1720,1768,2614,2638,2662,2680,2714,2732,2762,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7664 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7664 66 4
  · have he : independentCachedBranchMembers7664.erase 66=independentCachedBranchMembers7662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7662
  · have he : independentCachedBranchMembers7664.filter (independentCachedEdge 66)=independentCachedBranchMembers7663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7663
def independentCachedBranchMembers7665 : Finset ℕ := ([1650,1678,1720,1768,2638,2680,2772,2786,3158,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7665 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7665 4 (fun x => (if x<2772 then (if x<1768 then (if x<1678 then 0 else (if x<1720 then 1 else 0)) else (if x<2638 then 1 else (if x<2680 then 2 else 0))) else (if x<3228 then (if x<2786 then 2 else (if x<3158 then 2 else 3)) else (if x<3242 then 3 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7666 : Finset ℕ := ([36,66,136,238,1596,1626,1644,1650,1678,1702,1720,1768,2614,2638,2662,2680,2714,2732,2762,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7666 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7666 36 4
  · have he : independentCachedBranchMembers7666.erase 36=independentCachedBranchMembers7664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7664
  · have he : independentCachedBranchMembers7666.filter (independentCachedEdge 36)=independentCachedBranchMembers7665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7665
def independentCachedBranchMembers7667 : Finset ℕ := ([36,66,136,238,1596,1626,1678,1768,2614,2638,2714,2786,3118,3158,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7667 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7667 4 (fun x => (if x<2614 then (if x<1596 then (if x<136 then (if x<66 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1678 then (if x<1626 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3118 then (if x<2714 then (if x<2638 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3228 then (if x<3158 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7668 : Finset ℕ := ([36,66,136,238,1596,1626,1644,1650,1678,1702,1720,1768,2614,2638,2662,2680,2714,2732,2738,2762,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7668 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7668 2738 4
  · have he : independentCachedBranchMembers7668.erase 2738=independentCachedBranchMembers7666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7666
  · have he : independentCachedBranchMembers7668.filter (independentCachedEdge 2738)=independentCachedBranchMembers7667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7667
def independentCachedBranchMembers7669 : Finset ℕ := ([34,36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7669 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7669 3284 5
  · have he : independentCachedBranchMembers7669.erase 3284=independentCachedBranchMembers7657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7657
  · have he : independentCachedBranchMembers7669.filter (independentCachedEdge 3284)=independentCachedBranchMembers7668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7668
def independentCachedBranchMembers7670 : Finset ℕ := ([1594,1628,1644,1650,1686,1702,1720,1776,2606,2646,2662,2680,2716,2738,2762,2772,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7670 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7670 5 (fun x => (if x<2716 then (if x<1720 then (if x<1650 then (if x<1628 then 0 else (if x<1644 then 0 else 1)) else (if x<1686 then 1 else (if x<1702 then 0 else 1))) else (if x<2646 then (if x<1776 then 1 else (if x<2606 then 0 else 2)) else (if x<2662 then 2 else (if x<2680 then 1 else 0)))) else (if x<3150 then (if x<2772 then (if x<2738 then 2 else (if x<2762 then 0 else 2)) else (if x<2788 then 0 else (if x<3126 then 2 else 3))) else (if x<3252 then (if x<3226 then 3 else (if x<3242 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7671 : Finset ℕ := ([1594,1628,1644,1720,2606,2680,2716,2762,3150,3226,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7671 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7671 4 (fun x => (if x<2716 then (if x<1720 then (if x<1628 then 0 else (if x<1644 then 0 else 1)) else (if x<2606 then 1 else (if x<2680 then 2 else 0))) else (if x<3226 then (if x<2762 then 2 else (if x<3150 then 2 else 1)) else (if x<3242 then 1 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7672 : Finset ℕ := ([246,1594,1628,1644,1650,1686,1702,1720,1776,2606,2646,2662,2680,2716,2738,2762,2772,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7672 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7672 246 4
  · have he : independentCachedBranchMembers7672.erase 246=independentCachedBranchMembers7670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7670
  · have he : independentCachedBranchMembers7672.filter (independentCachedEdge 246)=independentCachedBranchMembers7671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7671
def independentCachedBranchMembers7673 : Finset ℕ := ([1594,1628,1650,1702,2646,2680,2762,2788,3126,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7673 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7673 4 (fun x => (if x<2762 then (if x<1702 then (if x<1628 then 0 else (if x<1650 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 2 else 0))) else (if x<3242 then (if x<2788 then 2 else (if x<3126 then 2 else 1)) else (if x<3276 then 3 else (if x<3298 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7674 : Finset ℕ := ([144,246,1594,1628,1644,1650,1686,1702,1720,1776,2606,2646,2662,2680,2716,2738,2762,2772,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7674 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7674 144 4
  · have he : independentCachedBranchMembers7674.erase 144=independentCachedBranchMembers7672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7672
  · have he : independentCachedBranchMembers7674.filter (independentCachedEdge 144)=independentCachedBranchMembers7673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7673
def independentCachedBranchMembers7675 : Finset ℕ := ([1650,1686,1702,1776,2606,2680,2716,2762,3126,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7675 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7675 4 (fun x => (if x<2716 then (if x<1776 then (if x<1686 then 0 else (if x<1702 then 0 else 1)) else (if x<2606 then 1 else (if x<2680 then 1 else 0))) else (if x<3252 then (if x<2762 then 0 else (if x<3126 then 2 else 2)) else (if x<3282 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7676 : Finset ℕ := ([68,144,246,1594,1628,1644,1650,1686,1702,1720,1776,2606,2646,2662,2680,2716,2738,2762,2772,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7676 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7676 68 4
  · have he : independentCachedBranchMembers7676.erase 68=independentCachedBranchMembers7674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7674
  · have he : independentCachedBranchMembers7676.filter (independentCachedEdge 68)=independentCachedBranchMembers7675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7675
def independentCachedBranchMembers7677 : Finset ℕ := ([1644,1686,1720,1776,2646,2680,2762,2788,3150,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7677 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7677 4 (fun x => (if x<2762 then (if x<1776 then (if x<1686 then 0 else (if x<1720 then 1 else 0)) else (if x<2646 then 1 else (if x<2680 then 2 else 0))) else (if x<3226 then (if x<2788 then 2 else (if x<3150 then 2 else 3)) else (if x<3252 then 3 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7678 : Finset ℕ := ([34,68,144,246,1594,1628,1644,1650,1686,1702,1720,1776,2606,2646,2662,2680,2716,2738,2762,2772,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7678 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7678 34 4
  · have he : independentCachedBranchMembers7678.erase 34=independentCachedBranchMembers7676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7676
  · have he : independentCachedBranchMembers7678.filter (independentCachedEdge 34)=independentCachedBranchMembers7677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7677
def independentCachedBranchMembers7679 : Finset ℕ := ([34,68,144,246,1594,1628,1686,1776,2606,2646,2716,2788,3126,3150,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7679 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7679 4 (fun x => (if x<2606 then (if x<1594 then (if x<144 then (if x<68 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1686 then (if x<1628 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3126 then (if x<2716 then (if x<2646 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3226 then (if x<3150 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
