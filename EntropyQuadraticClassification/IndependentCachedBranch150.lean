/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch149
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7584 : Finset ℕ := ([1594,1596,1642,1644,1678,1702,1752,1776,2614,2638,2662,2732,2772,3118,3158,3192,3226,3228,3252,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7584 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7584 5 (fun x => (if x<2732 then (if x<1702 then (if x<1642 then (if x<1596 then 0 else 1) else (if x<1644 then 1 else (if x<1678 then 0 else 0))) else (if x<2614 then (if x<1752 then 1 else (if x<1776 then 0 else 1)) else (if x<2638 then 2 else (if x<2662 then 2 else 3)))) else (if x<3226 then (if x<3118 then (if x<2772 then 2 else 2) else (if x<3158 then 0 else (if x<3192 then 2 else 0))) else (if x<3276 then (if x<3228 then 0 else (if x<3252 then 3 else 1)) else (if x<3298 then 0 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7585 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7585 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7585 2646 5
  · have he : independentCachedBranchMembers7585.erase 2646=independentCachedBranchMembers7583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7583
  · have he : independentCachedBranchMembers7585.filter (independentCachedEdge 2646)=independentCachedBranchMembers7584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7584
def independentCachedBranchMembers7586 : Finset ℕ := ([1626,1628,1650,1652,1686,1720,1734,1768,2614,2638,2662,2732,2772,3118,3158,3192,3226,3228,3252,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7586 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7586 5 (fun x => (if x<2732 then (if x<1720 then (if x<1650 then (if x<1628 then 0 else 1) else (if x<1652 then 1 else (if x<1686 then 0 else 0))) else (if x<2614 then (if x<1734 then 0 else (if x<1768 then 1 else 1)) else (if x<2638 then 2 else (if x<2662 then 2 else 3)))) else (if x<3226 then (if x<3118 then (if x<2772 then 2 else 2) else (if x<3158 then 2 else (if x<3192 then 0 else 0))) else (if x<3276 then (if x<3228 then 0 else (if x<3252 then 3 else 0)) else (if x<3298 then 1 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7587 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7587 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7587 2606 5
  · have he : independentCachedBranchMembers7587.erase 2606=independentCachedBranchMembers7585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7585
  · have he : independentCachedBranchMembers7587.filter (independentCachedEdge 2606)=independentCachedBranchMembers7586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7586
def independentCachedBranchMembers7588 : Finset ℕ := ([1596,1626,1628,1642,1644,1678,1720,1752,2606,2638,2680,2714,2716,2732,2762,3118,3150,3192,3226,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7588 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7588 5 (fun x => (if x<2714 then (if x<1678 then (if x<1628 then (if x<1626 then 0 else 0) else (if x<1642 then 1 else (if x<1644 then 1 else 2))) else (if x<2606 then (if x<1720 then 0 else (if x<1752 then 1 else 2)) else (if x<2638 then 2 else (if x<2680 then 1 else 0)))) else (if x<3150 then (if x<2732 then (if x<2716 then 2 else 1) else (if x<2762 then 0 else (if x<3118 then 0 else 3))) else (if x<3228 then (if x<3192 then 4 else (if x<3226 then 3 else 3)) else (if x<3242 then 4 else (if x<3276 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7589 : Finset ℕ := ([1596,1626,1642,1720,2638,2716,2732,2762,3150,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7589 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7589 4 (fun x => (if x<2716 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1720 then 1 else (if x<2638 then 1 else 1))) else (if x<2762 then (if x<2732 then 1 else 0) else (if x<3150 then 0 else (if x<3228 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7590 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1678,1720,1752,2606,2638,2680,2714,2716,2732,2762,3118,3150,3192,3226,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7590 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7590 1594 4
  · have he : independentCachedBranchMembers7590.erase 1594=independentCachedBranchMembers7588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7588
  · have he : independentCachedBranchMembers7590.filter (independentCachedEdge 1594)=independentCachedBranchMembers7589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7589
def independentCachedBranchMembers7591 : Finset ℕ := ([1642,1644,1720,1752,2606,2638,2714,2716,3118,3150,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7591 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7591 4 (fun x => (if x<2714 then (if x<1752 then (if x<1644 then 0 else (if x<1720 then 1 else 0)) else (if x<2606 then 1 else (if x<2638 then 1 else 0))) else (if x<3150 then (if x<2716 then 1 else (if x<3118 then 0 else 2)) else (if x<3226 then 3 else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7592 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1678,1720,1752,1768,2606,2638,2680,2714,2716,2732,2762,3118,3150,3192,3226,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7592 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7592 1768 4
  · have he : independentCachedBranchMembers7592.erase 1768=independentCachedBranchMembers7590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7590
  · have he : independentCachedBranchMembers7592.filter (independentCachedEdge 1768)=independentCachedBranchMembers7591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7591
def independentCachedBranchMembers7593 : Finset ℕ := ([246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7593 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7593 246 5
  · have he : independentCachedBranchMembers7593.erase 246=independentCachedBranchMembers7587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7587
  · have he : independentCachedBranchMembers7593.filter (independentCachedEdge 246)=independentCachedBranchMembers7592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7592
def independentCachedBranchMembers7594 : Finset ℕ := ([1596,1626,1628,1650,1652,1702,1734,1768,2614,2646,2680,2732,2762,2786,2788,3126,3158,3192,3242,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7594 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7594 5 (fun x => (if x<2732 then (if x<1702 then (if x<1628 then (if x<1626 then 0 else 0) else (if x<1650 then 1 else (if x<1652 then 1 else 2))) else (if x<2614 then (if x<1734 then 2 else (if x<1768 then 1 else 0)) else (if x<2646 then 2 else (if x<2680 then 1 else 0)))) else (if x<3158 then (if x<2786 then (if x<2762 then 0 else 0) else (if x<2788 then 1 else (if x<3126 then 2 else 3))) else (if x<3276 then (if x<3192 then 4 else (if x<3242 then 3 else 3)) else (if x<3298 then 4 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7595 : Finset ℕ := ([1596,1626,1650,1734,2646,2732,2762,2786,3158,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7595 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7595 4 (fun x => (if x<2732 then (if x<1650 then (if x<1626 then 0 else 0) else (if x<1734 then 1 else (if x<2646 then 1 else 1))) else (if x<2786 then (if x<2762 then 0 else 0) else (if x<3158 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7596 : Finset ℕ := ([1594,1596,1626,1628,1650,1652,1702,1734,1768,2614,2646,2680,2732,2762,2786,2788,3126,3158,3192,3242,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7596 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7596 1594 4
  · have he : independentCachedBranchMembers7596.erase 1594=independentCachedBranchMembers7594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7594
  · have he : independentCachedBranchMembers7596.filter (independentCachedEdge 1594)=independentCachedBranchMembers7595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7595
def independentCachedBranchMembers7597 : Finset ℕ := ([1650,1652,1702,1734,2614,2646,2786,2788,3126,3158,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7597 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7597 4 (fun x => (if x<2786 then (if x<1734 then (if x<1652 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then 1 else (if x<2646 then 0 else 1))) else (if x<3158 then (if x<2788 then 0 else (if x<3126 then 1 else 2)) else (if x<3298 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7598 : Finset ℕ := ([1594,1596,1626,1628,1650,1652,1678,1702,1734,1768,2614,2646,2680,2732,2762,2786,2788,3126,3158,3192,3242,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7598 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7598 1678 4
  · have he : independentCachedBranchMembers7598.erase 1678=independentCachedBranchMembers7596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7596
  · have he : independentCachedBranchMembers7598.filter (independentCachedEdge 1678)=independentCachedBranchMembers7597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7597
def independentCachedBranchMembers7599 : Finset ℕ := ([144,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7599 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7599 144 5
  · have he : independentCachedBranchMembers7599.erase 144=independentCachedBranchMembers7593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7593
  · have he : independentCachedBranchMembers7599.filter (independentCachedEdge 144)=independentCachedBranchMembers7598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7598
def independentCachedBranchMembers7600 : Finset ℕ := ([1594,1628,1644,1652,1678,1686,1702,1752,1768,1776,2606,2614,2680,2714,2738,2772,2788,3118,3126,3192,3226,3242,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7600 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7600 5 (fun x => (if x<2680 then (if x<1702 then (if x<1652 then (if x<1628 then 0 else (if x<1644 then 0 else 1)) else (if x<1678 then 2 else (if x<1686 then 0 else 2))) else (if x<1776 then (if x<1752 then 1 else (if x<1768 then 2 else 0)) else (if x<2606 then 1 else (if x<2614 then 1 else 2)))) else (if x<3126 then (if x<2772 then (if x<2714 then 0 else (if x<2738 then 2 else 1)) else (if x<2788 then 2 else (if x<3118 then 1 else 3))) else (if x<3242 then (if x<3192 then 4 else (if x<3226 then 3 else 3)) else (if x<3276 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7601 : Finset ℕ := ([66,144,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7601 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7601 66 5
  · have he : independentCachedBranchMembers7601.erase 66=independentCachedBranchMembers7599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7599
  · have he : independentCachedBranchMembers7601.filter (independentCachedEdge 66)=independentCachedBranchMembers7600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7600
def independentCachedBranchMembers7602 : Finset ℕ := ([1628,1642,1650,1686,1720,1734,1776,2638,2646,2680,2716,2738,2772,2786,3150,3158,3192,3228,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7602 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7602 5 (fun x => (if x<2716 then (if x<1734 then (if x<1650 then (if x<1642 then 0 else 0) else (if x<1686 then 1 else (if x<1720 then 1 else 0))) else (if x<2638 then (if x<1776 then 2 else 2) else (if x<2646 then 0 else (if x<2680 then 1 else 0)))) else (if x<3158 then (if x<2772 then (if x<2738 then 0 else 1) else (if x<2786 then 2 else (if x<3150 then 2 else 3))) else (if x<3242 then (if x<3192 then 4 else (if x<3228 then 3 else 3)) else (if x<3276 then 3 else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7603 : Finset ℕ := ([1642,1686,1720,1776,2638,2716,2738,2772,3150,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7603 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7603 4 (fun x => (if x<2716 then (if x<1720 then (if x<1686 then 0 else 1) else (if x<1776 then 0 else (if x<2638 then 1 else 0))) else (if x<2772 then (if x<2738 then 0 else 1) else (if x<3150 then 1 else (if x<3228 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7604 : Finset ℕ := ([1628,1642,1650,1686,1720,1734,1768,1776,2638,2646,2680,2716,2738,2772,2786,3150,3158,3192,3228,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7604 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7604 1768 4
  · have he : independentCachedBranchMembers7604.erase 1768=independentCachedBranchMembers7602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7602
  · have he : independentCachedBranchMembers7604.filter (independentCachedEdge 1768)=independentCachedBranchMembers7603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7603
def independentCachedBranchMembers7605 : Finset ℕ := ([1650,1686,1734,1776,2646,2738,2772,2786,3158,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7605 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7605 4 (fun x => (if x<2738 then (if x<1734 then (if x<1686 then 0 else 0) else (if x<1776 then 1 else (if x<2646 then 1 else 0))) else (if x<2786 then (if x<2772 then 0 else 1) else (if x<3158 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7606 : Finset ℕ := ([1628,1642,1650,1678,1686,1720,1734,1768,1776,2638,2646,2680,2716,2738,2772,2786,3150,3158,3192,3228,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7606 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7606 1678 4
  · have he : independentCachedBranchMembers7606.erase 1678=independentCachedBranchMembers7604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7604
  · have he : independentCachedBranchMembers7606.filter (independentCachedEdge 1678)=independentCachedBranchMembers7605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7605
def independentCachedBranchMembers7607 : Finset ℕ := ([1642,1650,1720,1734,2638,2646,2716,2786,3150,3158,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7607 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7607 4 (fun x => (if x<2716 then (if x<1734 then (if x<1650 then 0 else (if x<1720 then 1 else 0)) else (if x<2638 then 1 else (if x<2646 then 0 else 1))) else (if x<3158 then (if x<2786 then 0 else (if x<3150 then 1 else 2)) else (if x<3228 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7608 : Finset ℕ := ([1594,1628,1642,1650,1678,1686,1720,1734,1768,1776,2638,2646,2680,2716,2738,2772,2786,3150,3158,3192,3228,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7608 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7608 1594 4
  · have he : independentCachedBranchMembers7608.erase 1594=independentCachedBranchMembers7606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7606
  · have he : independentCachedBranchMembers7608.filter (independentCachedEdge 1594)=independentCachedBranchMembers7607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7607
def independentCachedBranchMembers7609 : Finset ℕ := ([36,66,144,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7609 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7609 36 5
  · have he : independentCachedBranchMembers7609.erase 36=independentCachedBranchMembers7601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7601
  · have he : independentCachedBranchMembers7609.filter (independentCachedEdge 36)=independentCachedBranchMembers7608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7608
def independentCachedBranchMembers7610 : Finset ℕ := ([1596,1626,1650,1652,1686,1720,1752,2646,2680,2716,2738,3126,3158,3192,3226,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7610 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7610 5 (fun x => (if x<2716 then (if x<1686 then (if x<1650 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<1752 then (if x<1720 then 0 else 1) else (if x<2646 then 2 else (if x<2680 then 1 else 0)))) else (if x<3192 then (if x<3126 then (if x<2738 then 1 else 1) else (if x<3158 then 2 else 3)) else (if x<3228 then (if x<3226 then 2 else 2) else (if x<3252 then 3 else (if x<3282 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7611 : Finset ℕ := ([1596,1626,1650,1720,2646,2716,3126,3192,3226] : List ℕ).toFinset
theorem independentCachedBranchBound7611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7611 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7611 4 (fun x => (if x<2646 then (if x<1650 then (if x<1626 then 0 else 0) else (if x<1720 then 1 else 1)) else (if x<3126 then (if x<2716 then 1 else 1) else (if x<3192 then 2 else (if x<3226 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7612 : Finset ℕ := ([1596,1626,1650,1652,1686,1720,1752,2646,2680,2716,2738,2772,3126,3158,3192,3226,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7612 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7612 2772 4
  · have he : independentCachedBranchMembers7612.erase 2772=independentCachedBranchMembers7610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7610
  · have he : independentCachedBranchMembers7612.filter (independentCachedEdge 2772)=independentCachedBranchMembers7611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7611
def independentCachedBranchMembers7613 : Finset ℕ := ([1596,1650,2716,2738,3126,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound7613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7613 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7613 4 (fun x => (if x<3126 then (if x<2716 then (if x<1650 then 0 else 0) else (if x<2738 then 0 else 1)) else (if x<3192 then (if x<3158 then 1 else 2) else (if x<3226 then 2 else (if x<3252 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7614 : Finset ℕ := ([1596,1626,1650,1652,1686,1720,1752,2646,2680,2714,2716,2738,2772,3126,3158,3192,3226,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7614 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7614 2714 4
  · have he : independentCachedBranchMembers7614.erase 2714=independentCachedBranchMembers7612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7612
  · have he : independentCachedBranchMembers7614.filter (independentCachedEdge 2714)=independentCachedBranchMembers7613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7613
def independentCachedBranchMembers7615 : Finset ℕ := ([1626,1720,2646,2738,3126,3192,3226,3228,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7615 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7615 4 (fun x => (if x<3126 then (if x<2646 then (if x<1720 then 0 else 0) else (if x<2738 then 0 else 1)) else (if x<3226 then (if x<3192 then 1 else 2) else (if x<3228 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
