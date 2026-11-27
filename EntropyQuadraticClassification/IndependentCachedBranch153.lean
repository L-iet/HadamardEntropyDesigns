/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch152
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7680 : Finset ℕ := ([34,68,144,246,1594,1628,1644,1650,1686,1702,1720,1776,2606,2646,2662,2680,2716,2732,2738,2762,2772,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7680 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7680 2732 4
  · have he : independentCachedBranchMembers7680.erase 2732=independentCachedBranchMembers7678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7678
  · have he : independentCachedBranchMembers7680.filter (independentCachedEdge 2732)=independentCachedBranchMembers7679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7679
def independentCachedBranchMembers7681 : Finset ℕ := ([34,36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7681 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7681 3274 5
  · have he : independentCachedBranchMembers7681.erase 3274=independentCachedBranchMembers7669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7669
  · have he : independentCachedBranchMembers7681.filter (independentCachedEdge 3274)=independentCachedBranchMembers7680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7680
def independentCachedBranchMembers7682 : Finset ℕ := ([1596,1626,1642,1652,1678,1734,1752,1768,2606,2646,2662,2680,2716,2732,2738,2762,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7682 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7682 5 (fun x => (if x<2716 then (if x<1752 then (if x<1652 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1678 then 1 else (if x<1734 then 0 else 1))) else (if x<2646 then (if x<1768 then 1 else (if x<2606 then 0 else 2)) else (if x<2662 then 2 else (if x<2680 then 1 else 0)))) else (if x<3150 then (if x<2762 then (if x<2732 then 2 else (if x<2738 then 0 else 2)) else (if x<2788 then 0 else (if x<3126 then 2 else 3))) else (if x<3252 then (if x<3226 then 3 else (if x<3242 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7683 : Finset ℕ := ([1596,1626,1652,1752,2646,2680,2716,2738,3126,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7683 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7683 4 (fun x => (if x<2716 then (if x<1752 then (if x<1626 then 0 else (if x<1652 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 2 else 0))) else (if x<3226 then (if x<2738 then 2 else (if x<3126 then 2 else 1)) else (if x<3252 then 1 else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7684 : Finset ℕ := ([238,1596,1626,1642,1652,1678,1734,1752,1768,2606,2646,2662,2680,2716,2732,2738,2762,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7684 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7684 238 4
  · have he : independentCachedBranchMembers7684.erase 238=independentCachedBranchMembers7682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7682
  · have he : independentCachedBranchMembers7684.filter (independentCachedEdge 238)=independentCachedBranchMembers7683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7683
def independentCachedBranchMembers7685 : Finset ℕ := ([1596,1626,1642,1734,2606,2680,2738,2788,3150,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7685 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7685 4 (fun x => (if x<2738 then (if x<1734 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<2606 then 1 else (if x<2680 then 2 else 0))) else (if x<3252 then (if x<2788 then 2 else (if x<3150 then 2 else 1)) else (if x<3282 then 3 else (if x<3298 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7686 : Finset ℕ := ([136,238,1596,1626,1642,1652,1678,1734,1752,1768,2606,2646,2662,2680,2716,2732,2738,2762,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7686 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7686 136 4
  · have he : independentCachedBranchMembers7686.erase 136=independentCachedBranchMembers7684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7684
  · have he : independentCachedBranchMembers7686.filter (independentCachedEdge 136)=independentCachedBranchMembers7685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7685
def independentCachedBranchMembers7687 : Finset ℕ := ([1652,1678,1752,1768,2606,2680,2738,2788,3126,3226,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7687 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7687 4 (fun x => (if x<2738 then (if x<1768 then (if x<1678 then 0 else (if x<1752 then 1 else 0)) else (if x<2606 then 1 else (if x<2680 then 2 else 0))) else (if x<3226 then (if x<2788 then 2 else (if x<3126 then 2 else 3)) else (if x<3242 then 3 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7688 : Finset ℕ := ([66,136,238,1596,1626,1642,1652,1678,1734,1752,1768,2606,2646,2662,2680,2716,2732,2738,2762,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7688 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7688 66 4
  · have he : independentCachedBranchMembers7688.erase 66=independentCachedBranchMembers7686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7686
  · have he : independentCachedBranchMembers7688.filter (independentCachedEdge 66)=independentCachedBranchMembers7687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7687
def independentCachedBranchMembers7689 : Finset ℕ := ([1642,1678,1734,1768,2646,2680,2716,2738,3150,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7689 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7689 4 (fun x => (if x<2716 then (if x<1768 then (if x<1678 then 0 else (if x<1734 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 1 else 0))) else (if x<3242 then (if x<2738 then 0 else (if x<3150 then 2 else 2)) else (if x<3276 then 2 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7690 : Finset ℕ := ([36,66,136,238,1596,1626,1642,1652,1678,1734,1752,1768,2606,2646,2662,2680,2716,2732,2738,2762,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7690 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7690 36 4
  · have he : independentCachedBranchMembers7690.erase 36=independentCachedBranchMembers7688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7688
  · have he : independentCachedBranchMembers7690.filter (independentCachedEdge 36)=independentCachedBranchMembers7689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7689
def independentCachedBranchMembers7691 : Finset ℕ := ([36,66,136,238,1596,1626,1678,1768,2606,2646,2716,2788,3126,3150,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7691 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7691 4 (fun x => (if x<2606 then (if x<1596 then (if x<136 then (if x<66 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1678 then (if x<1626 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3126 then (if x<2716 then (if x<2646 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3226 then (if x<3150 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7692 : Finset ℕ := ([36,66,136,238,1596,1626,1642,1652,1678,1734,1752,1768,2606,2646,2662,2680,2716,2732,2738,2762,2772,2788,3126,3150,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7692 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7692 2772 4
  · have he : independentCachedBranchMembers7692.erase 2772=independentCachedBranchMembers7690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7690
  · have he : independentCachedBranchMembers7692.filter (independentCachedEdge 2772)=independentCachedBranchMembers7691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7691
def independentCachedBranchMembers7693 : Finset ℕ := ([34,36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7693 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7693 3250 5
  · have he : independentCachedBranchMembers7693.erase 3250=independentCachedBranchMembers7681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7681
  · have he : independentCachedBranchMembers7693.filter (independentCachedEdge 3250)=independentCachedBranchMembers7692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7692
def independentCachedBranchMembers7694 : Finset ℕ := ([1594,1628,1642,1652,1686,1734,1752,1776,2614,2638,2662,2680,2714,2732,2738,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7694 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7694 5 (fun x => (if x<2714 then (if x<1752 then (if x<1652 then (if x<1628 then 0 else (if x<1642 then 0 else 1)) else (if x<1686 then 1 else (if x<1734 then 0 else 1))) else (if x<2638 then (if x<1776 then 1 else (if x<2614 then 0 else 2)) else (if x<2662 then 2 else (if x<2680 then 1 else 0)))) else (if x<3158 then (if x<2772 then (if x<2732 then 2 else (if x<2738 then 2 else 0)) else (if x<2786 then 0 else (if x<3118 then 2 else 3))) else (if x<3252 then (if x<3228 then 3 else (if x<3242 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7695 : Finset ℕ := ([1594,1628,1642,1752,2638,2680,2714,2732,3118,3228,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7695 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7695 4 (fun x => (if x<2714 then (if x<1752 then (if x<1628 then 0 else (if x<1642 then 0 else 1)) else (if x<2638 then 1 else (if x<2680 then 2 else 0))) else (if x<3228 then (if x<2732 then 2 else (if x<3118 then 2 else 1)) else (if x<3242 then 1 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7696 : Finset ℕ := ([246,1594,1628,1642,1652,1686,1734,1752,1776,2614,2638,2662,2680,2714,2732,2738,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7696 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7696 246 4
  · have he : independentCachedBranchMembers7696.erase 246=independentCachedBranchMembers7694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7694
  · have he : independentCachedBranchMembers7696.filter (independentCachedEdge 246)=independentCachedBranchMembers7695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7695
def independentCachedBranchMembers7697 : Finset ℕ := ([1594,1628,1652,1734,2614,2680,2732,2786,3158,3242,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7697 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7697 4 (fun x => (if x<2732 then (if x<1734 then (if x<1628 then 0 else (if x<1652 then 0 else 1)) else (if x<2614 then 1 else (if x<2680 then 2 else 0))) else (if x<3242 then (if x<2786 then 2 else (if x<3158 then 2 else 1)) else (if x<3276 then 3 else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7698 : Finset ℕ := ([144,246,1594,1628,1642,1652,1686,1734,1752,1776,2614,2638,2662,2680,2714,2732,2738,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7698 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7698 144 4
  · have he : independentCachedBranchMembers7698.erase 144=independentCachedBranchMembers7696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7696
  · have he : independentCachedBranchMembers7698.filter (independentCachedEdge 144)=independentCachedBranchMembers7697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7697
def independentCachedBranchMembers7699 : Finset ℕ := ([1642,1686,1752,1776,2614,2680,2732,2786,3118,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7699 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7699 4 (fun x => (if x<2732 then (if x<1776 then (if x<1686 then 0 else (if x<1752 then 1 else 0)) else (if x<2614 then 1 else (if x<2680 then 2 else 0))) else (if x<3228 then (if x<2786 then 2 else (if x<3118 then 2 else 3)) else (if x<3252 then 3 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7700 : Finset ℕ := ([68,144,246,1594,1628,1642,1652,1686,1734,1752,1776,2614,2638,2662,2680,2714,2732,2738,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7700 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7700 68 4
  · have he : independentCachedBranchMembers7700.erase 68=independentCachedBranchMembers7698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7698
  · have he : independentCachedBranchMembers7700.filter (independentCachedEdge 68)=independentCachedBranchMembers7699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7699
def independentCachedBranchMembers7701 : Finset ℕ := ([1652,1686,1734,1776,2638,2680,2714,2732,3158,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7701 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7701 4 (fun x => (if x<2714 then (if x<1776 then (if x<1686 then 0 else (if x<1734 then 0 else 1)) else (if x<2638 then 1 else (if x<2680 then 1 else 0))) else (if x<3252 then (if x<2732 then 0 else (if x<3158 then 2 else 2)) else (if x<3282 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7702 : Finset ℕ := ([34,68,144,246,1594,1628,1642,1652,1686,1734,1752,1776,2614,2638,2662,2680,2714,2732,2738,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7702 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7702 34 4
  · have he : independentCachedBranchMembers7702.erase 34=independentCachedBranchMembers7700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7700
  · have he : independentCachedBranchMembers7702.filter (independentCachedEdge 34)=independentCachedBranchMembers7701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7701
def independentCachedBranchMembers7703 : Finset ℕ := ([34,68,144,246,1594,1628,1686,1776,2614,2638,2714,2786,3118,3158,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7703 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7703 4 (fun x => (if x<2614 then (if x<1594 then (if x<144 then (if x<68 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1686 then (if x<1628 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3118 then (if x<2714 then (if x<2638 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3228 then (if x<3158 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7704 : Finset ℕ := ([34,68,144,246,1594,1628,1642,1652,1686,1734,1752,1776,2614,2638,2662,2680,2714,2732,2738,2762,2772,2786,3118,3158,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7704 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7704 2762 4
  · have he : independentCachedBranchMembers7704.erase 2762=independentCachedBranchMembers7702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7702
  · have he : independentCachedBranchMembers7704.filter (independentCachedEdge 2762)=independentCachedBranchMembers7703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7703
def independentCachedBranchMembers7705 : Finset ℕ := ([34,36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7705 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7705 3244 5
  · have he : independentCachedBranchMembers7705.erase 3244=independentCachedBranchMembers7693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7693
  · have he : independentCachedBranchMembers7705.filter (independentCachedEdge 3244)=independentCachedBranchMembers7704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7704
def independentCachedBranchMembers7706 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1734,1752,2662,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7706 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7706 5 (fun x => (if x<2738 then (if x<1720 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else (if x<1702 then 0 else 0))) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<2662 then 1 else (if x<2732 then 0 else 2)))) else (if x<3150 then (if x<2772 then (if x<2762 then 2 else 2) else (if x<3118 then 2 else (if x<3126 then 3 else 4))) else (if x<3228 then (if x<3158 then 4 else (if x<3226 then 3 else 3)) else (if x<3298 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7707 : Finset ℕ := ([1642,1644,1720,1752,2732,2762,3118,3150,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7707 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7707 4 (fun x => (if x<2762 then (if x<1720 then (if x<1644 then 0 else 1) else (if x<1752 then 0 else (if x<2732 then 1 else 2))) else (if x<3150 then (if x<3118 then 2 else 1) else (if x<3226 then 0 else (if x<3228 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7708 : Finset ℕ := ([246,1642,1644,1650,1652,1702,1720,1734,1752,2662,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7708 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7708 246 4
  · have he : independentCachedBranchMembers7708.erase 246=independentCachedBranchMembers7706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7706
  · have he : independentCachedBranchMembers7708.filter (independentCachedEdge 246)=independentCachedBranchMembers7707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7707
def independentCachedBranchMembers7709 : Finset ℕ := ([1650,1652,1702,1734,2732,2762,3126,3158,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7709 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7709 4 (fun x => (if x<2762 then (if x<1702 then (if x<1652 then 0 else 1) else (if x<1734 then 0 else (if x<2732 then 1 else 0))) else (if x<3158 then (if x<3126 then 1 else 2) else (if x<3298 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7710 : Finset ℕ := ([144,246,1642,1644,1650,1652,1702,1720,1734,1752,2662,2732,2738,2762,2772,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7710 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7710 144 4
  · have he : independentCachedBranchMembers7710.erase 144=independentCachedBranchMembers7708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7708
  · have he : independentCachedBranchMembers7710.filter (independentCachedEdge 144)=independentCachedBranchMembers7709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7709
def independentCachedBranchMembers7711 : Finset ℕ := ([1644,1652,1702,1752,2738,2772,3118,3126,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7711 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7711 4 (fun x => (if x<2772 then (if x<1702 then (if x<1652 then 0 else 1) else (if x<1752 then 0 else (if x<2738 then 1 else 0))) else (if x<3126 then (if x<3118 then 1 else 2) else (if x<3226 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
