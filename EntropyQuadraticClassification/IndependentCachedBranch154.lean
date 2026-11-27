/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch153
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7712 : Finset ℕ := ([66,144,246,1642,1644,1650,1652,1702,1720,1734,1752,2662,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7712 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7712 66 4
  · have he : independentCachedBranchMembers7712.erase 66=independentCachedBranchMembers7710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7710
  · have he : independentCachedBranchMembers7712.filter (independentCachedEdge 66)=independentCachedBranchMembers7711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7711
def independentCachedBranchMembers7713 : Finset ℕ := ([1642,1650,1720,1734,2738,2772,3150,3158,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7713 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7713 4 (fun x => (if x<2772 then (if x<1720 then (if x<1650 then 0 else 1) else (if x<1734 then 0 else (if x<2738 then 1 else 2))) else (if x<3158 then (if x<3150 then 2 else 0) else (if x<3228 then 1 else (if x<3298 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7714 : Finset ℕ := ([36,66,144,246,1642,1644,1650,1652,1702,1720,1734,1752,2662,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7714 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7714 36 4
  · have he : independentCachedBranchMembers7714.erase 36=independentCachedBranchMembers7712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7712
  · have he : independentCachedBranchMembers7714.filter (independentCachedEdge 36)=independentCachedBranchMembers7713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7713
def independentCachedBranchMembers7715 : Finset ℕ := ([144,246,1650,1652,1720,1752,2738,2772,3126,3158,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7715 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7715 4 (fun x => (if x<2738 then (if x<1652 then (if x<246 then 0 else (if x<1650 then 0 else 1)) else (if x<1720 then 2 else (if x<1752 then 1 else 2))) else (if x<3158 then (if x<2772 then 0 else (if x<3126 then 0 else 2)) else (if x<3226 then 1 else (if x<3228 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7716 : Finset ℕ := ([36,66,144,238,246,1642,1644,1650,1652,1702,1720,1734,1752,2662,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7716 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7716 238 4
  · have he : independentCachedBranchMembers7716.erase 238=independentCachedBranchMembers7714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7714
  · have he : independentCachedBranchMembers7716.filter (independentCachedEdge 238)=independentCachedBranchMembers7715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7715
def independentCachedBranchMembers7717 : Finset ℕ := ([144,246,1642,1644,1702,1734,2738,2772,3118,3150,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7717 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7717 4 (fun x => (if x<2738 then (if x<1644 then (if x<246 then 0 else (if x<1642 then 0 else 1)) else (if x<1702 then 2 else (if x<1734 then 1 else 2))) else (if x<3150 then (if x<2772 then 0 else (if x<3118 then 0 else 1)) else (if x<3298 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7718 : Finset ℕ := ([36,66,136,144,238,246,1642,1644,1650,1652,1702,1720,1734,1752,2662,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7718 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7718 136 4
  · have he : independentCachedBranchMembers7718.erase 136=independentCachedBranchMembers7716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7716
  · have he : independentCachedBranchMembers7718.filter (independentCachedEdge 136)=independentCachedBranchMembers7717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7717
def independentCachedBranchMembers7719 : Finset ℕ := ([36,66,1642,1650,1702,1752,2732,2762,3118,3126,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7719 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7719 4 (fun x => (if x<2732 then (if x<1650 then (if x<66 then 0 else (if x<1642 then 0 else 1)) else (if x<1702 then 2 else (if x<1752 then 1 else 2))) else (if x<3126 then (if x<2762 then 0 else (if x<3118 then 0 else 1)) else (if x<3228 then 2 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7720 : Finset ℕ := ([36,66,68,136,144,238,246,1642,1644,1650,1652,1702,1720,1734,1752,2662,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7720 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7720 68 4
  · have he : independentCachedBranchMembers7720.erase 68=independentCachedBranchMembers7718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7718
  · have he : independentCachedBranchMembers7720.filter (independentCachedEdge 68)=independentCachedBranchMembers7719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7719
def independentCachedBranchMembers7721 : Finset ℕ := ([36,66,1644,1652,1720,1734,2732,2762,3150,3158,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7721 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7721 4 (fun x => (if x<2732 then (if x<1652 then (if x<66 then 0 else (if x<1644 then 0 else 1)) else (if x<1720 then 2 else (if x<1734 then 1 else 2))) else (if x<3158 then (if x<2762 then 0 else (if x<3150 then 0 else 1)) else (if x<3226 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7722 : Finset ℕ := ([34,36,66,68,136,144,238,246,1642,1644,1650,1652,1702,1720,1734,1752,2662,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7722 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7722 34 4
  · have he : independentCachedBranchMembers7722.erase 34=independentCachedBranchMembers7720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7720
  · have he : independentCachedBranchMembers7722.filter (independentCachedEdge 34)=independentCachedBranchMembers7721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7721
def independentCachedBranchMembers7723 : Finset ℕ := ([34,36,66,68,136,144,238,246,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7723 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7723 4 (fun x => (if x<3118 then (if x<136 then (if x<66 then (if x<36 then 0 else 1) else (if x<68 then 1 else 0)) else (if x<238 then (if x<144 then 0 else 1) else (if x<246 then 0 else 1))) else (if x<3226 then (if x<3150 then (if x<3126 then 2 else 3) else (if x<3158 then 3 else 2)) else (if x<3298 then (if x<3228 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7724 : Finset ℕ := ([34,36,66,68,136,144,238,246,1642,1644,1650,1652,1702,1720,1734,1752,2662,2680,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7724 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7724 2680 4
  · have he : independentCachedBranchMembers7724.erase 2680=independentCachedBranchMembers7722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7722
  · have he : independentCachedBranchMembers7724.filter (independentCachedEdge 2680)=independentCachedBranchMembers7723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7723
def independentCachedBranchMembers7725 : Finset ℕ := ([34,36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7725 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7725 3102 5
  · have he : independentCachedBranchMembers7725.erase 3102=independentCachedBranchMembers7705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7705
  · have he : independentCachedBranchMembers7725.filter (independentCachedEdge 3102)=independentCachedBranchMembers7724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7724
def independentCachedBranchMembers7726 : Finset ℕ := ([1626,1642,1644,1650,1652,1686,1702,1720,1734,1752,1776,2606,2614,2638,2646,2680,2714,2716,2732,2738,2762,2772,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7726 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7726 5 (fun x => (if x<2614 then (if x<1702 then (if x<1650 then (if x<1642 then 0 else (if x<1644 then 1 else 0)) else (if x<1652 then 2 else (if x<1686 then 1 else 2))) else (if x<1752 then (if x<1720 then 1 else (if x<1734 then 0 else 3)) else (if x<1776 then 2 else (if x<2606 then 3 else 4)))) else (if x<2732 then (if x<2680 then (if x<2638 then 2 else (if x<2646 then 0 else 4)) else (if x<2714 then 0 else (if x<2716 then 0 else 2))) else (if x<2772 then (if x<2738 then 0 else (if x<2762 then 4 else 4)) else (if x<2786 then 3 else (if x<2788 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7727 : Finset ℕ := ([1644,1652,1720,1734,2638,2646,2714,2738,2772,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7727 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7727 4 (fun x => (if x<2646 then (if x<1720 then (if x<1652 then 0 else 1) else (if x<1734 then 0 else (if x<2638 then 1 else 0))) else (if x<2738 then (if x<2714 then 1 else 0) else (if x<2772 then 2 else (if x<2788 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7728 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1720,1734,1752,1776,2606,2614,2638,2646,2680,2714,2716,2732,2738,2762,2772,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7728 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7728 1596 4
  · have he : independentCachedBranchMembers7728.erase 1596=independentCachedBranchMembers7726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7726
  · have he : independentCachedBranchMembers7728.filter (independentCachedEdge 1596)=independentCachedBranchMembers7727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7727
def independentCachedBranchMembers7729 : Finset ℕ := ([1642,1644,1686,1720,1752,1776,2606,2638,2714,2716,2738,2772] : List ℕ).toFinset
theorem independentCachedBranchBound7729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7729 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7729 4 (fun x => (if x<2606 then (if x<1720 then (if x<1644 then 0 else (if x<1686 then 1 else 2)) else (if x<1752 then 0 else (if x<1776 then 1 else 2))) else (if x<2716 then (if x<2638 then 1 else (if x<2714 then 0 else 1)) else (if x<2738 then 0 else (if x<2772 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7730 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2680,2714,2716,2732,2738,2762,2772,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7730 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7730 1768 4
  · have he : independentCachedBranchMembers7730.erase 1768=independentCachedBranchMembers7728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7728
  · have he : independentCachedBranchMembers7730.filter (independentCachedEdge 1768)=independentCachedBranchMembers7729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7729
def independentCachedBranchMembers7731 : Finset ℕ := ([1650,1652,1686,1702,1734,1776,2614,2646,2738,2772,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7731 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7731 4 (fun x => (if x<2614 then (if x<1702 then (if x<1652 then 0 else (if x<1686 then 1 else 0)) else (if x<1734 then 1 else (if x<1776 then 2 else 2))) else (if x<2772 then (if x<2646 then 0 else (if x<2738 then 3 else 3)) else (if x<2786 then 2 else (if x<2788 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7732 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2680,2714,2716,2732,2738,2762,2772,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7732 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7732 1678 4
  · have he : independentCachedBranchMembers7732.erase 1678=independentCachedBranchMembers7730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7730
  · have he : independentCachedBranchMembers7732.filter (independentCachedEdge 1678)=independentCachedBranchMembers7731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7731
def independentCachedBranchMembers7733 : Finset ℕ := ([1596,1626,1644,1652,1702,1752,2606,2614,2714,2732,2762,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7733 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7733 4 (fun x => (if x<2606 then (if x<1652 then (if x<1626 then 0 else (if x<1644 then 0 else 1)) else (if x<1702 then 2 else (if x<1752 then 1 else 2))) else (if x<2732 then (if x<2614 then 1 else (if x<2714 then 2 else 2)) else (if x<2762 then 0 else (if x<2788 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7734 : Finset ℕ := ([1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2680,2714,2716,2732,2738,2762,2772,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7734 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7734 1628 4
  · have he : independentCachedBranchMembers7734.erase 1628=independentCachedBranchMembers7732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7732
  · have he : independentCachedBranchMembers7734.filter (independentCachedEdge 1628)=independentCachedBranchMembers7733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7733
def independentCachedBranchMembers7735 : Finset ℕ := ([1596,1626,1642,1650,1720,1734,2638,2646,2716,2732,2762,2786] : List ℕ).toFinset
theorem independentCachedBranchBound7735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7735 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7735 4 (fun x => (if x<2638 then (if x<1650 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then 2 else (if x<1734 then 1 else 2))) else (if x<2732 then (if x<2646 then 1 else (if x<2716 then 2 else 1)) else (if x<2762 then 0 else (if x<2786 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7736 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2680,2714,2716,2732,2738,2762,2772,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7736 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7736 1594 4
  · have he : independentCachedBranchMembers7736.erase 1594=independentCachedBranchMembers7734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7734
  · have he : independentCachedBranchMembers7736.filter (independentCachedEdge 1594)=independentCachedBranchMembers7735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7735
def independentCachedBranchMembers7737 : Finset ℕ := ([1594,1596,1626,1628,1678,1686,1768,1776,2606,2614,2638,2646,2714,2716,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7737 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7737 4 (fun x => (if x<2606 then (if x<1678 then (if x<1626 then (if x<1596 then 0 else 1) else (if x<1628 then 1 else 0)) else (if x<1768 then (if x<1686 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<2714 then (if x<2638 then (if x<2614 then 2 else 3) else (if x<2646 then 3 else 2)) else (if x<2786 then (if x<2716 then 2 else 3) else (if x<2788 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7738 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound7738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7738 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7738 2662 4
  · have he : independentCachedBranchMembers7738.erase 2662=independentCachedBranchMembers7736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7736
  · have he : independentCachedBranchMembers7738.filter (independentCachedEdge 2662)=independentCachedBranchMembers7737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7737
def independentCachedBranchMembers7739 : Finset ℕ := ([34,36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7739 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7739 3072 5
  · have he : independentCachedBranchMembers7739.erase 3072=independentCachedBranchMembers7725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7725
  · have he : independentCachedBranchMembers7739.filter (independentCachedEdge 3072)=independentCachedBranchMembers7738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7738
def independentCachedBranchMembers7740 : Finset ℕ := ([136,238,1594,1628,1642,1652,1678,1702,1720,1768,2606,2646,2714,2732,2738,2762,2772,2786,3126,3150,3174,3192,3228,3242,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7740 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7740 5 (fun x => (if x<2732 then (if x<1678 then (if x<1628 then (if x<238 then 0 else (if x<1594 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 2 else 2))) else (if x<1768 then (if x<1702 then 0 else (if x<1720 then 2 else 2)) else (if x<2646 then (if x<2606 then 0 else 3) else (if x<2714 then 3 else 3)))) else (if x<3174 then (if x<2772 then (if x<2738 then 0 else (if x<2762 then 1 else 0)) else (if x<3126 then (if x<2786 then 1 else 3) else (if x<3150 then 4 else 4))) else (if x<3242 then (if x<3192 then 2 else (if x<3228 then 2 else 4)) else (if x<3282 then (if x<3276 then 0 else 0) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7741 : Finset ℕ := ([1642,1678,1702,1768,2606,2732,2762,2786,3126,3192,3228,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7741 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7741 4 (fun x => (if x<2762 then (if x<1768 then (if x<1678 then 0 else (if x<1702 then 0 else 1)) else (if x<2606 then 1 else (if x<2732 then 0 else 1))) else (if x<3192 then (if x<2786 then 0 else (if x<3126 then 1 else 2)) else (if x<3228 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7742 : Finset ℕ := ([68,136,238,1594,1628,1642,1652,1678,1702,1720,1768,2606,2646,2714,2732,2738,2762,2772,2786,3126,3150,3174,3192,3228,3242,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7742 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7742 68 4
  · have he : independentCachedBranchMembers7742.erase 68=independentCachedBranchMembers7740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7740
  · have he : independentCachedBranchMembers7742.filter (independentCachedEdge 68)=independentCachedBranchMembers7741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7741
def independentCachedBranchMembers7743 : Finset ℕ := ([1652,1678,1720,1768,2646,2714,2732,2762,3150,3192,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7743 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7743 4 (fun x => (if x<2732 then (if x<1768 then (if x<1678 then 0 else (if x<1720 then 1 else 0)) else (if x<2646 then 1 else (if x<2714 then 0 else 0))) else (if x<3192 then (if x<2762 then 1 else (if x<3150 then 1 else 2)) else (if x<3282 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
