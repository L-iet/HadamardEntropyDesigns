/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch150
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7616 : Finset ℕ := ([1596,1626,1650,1652,1686,1720,1752,2614,2646,2680,2714,2716,2738,2772,3126,3158,3192,3226,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7616 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7616 2614 4
  · have he : independentCachedBranchMembers7616.erase 2614=independentCachedBranchMembers7614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7614
  · have he : independentCachedBranchMembers7616.filter (independentCachedEdge 2614)=independentCachedBranchMembers7615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7615
def independentCachedBranchMembers7617 : Finset ℕ := ([1596,1626,1652,1752,2614,2714,3126,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7617 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7617 4 (fun x => (if x<2714 then (if x<1652 then (if x<1626 then 0 else 0) else (if x<1752 then 1 else (if x<2614 then 1 else 1))) else (if x<3226 then (if x<3126 then 1 else 2) else (if x<3252 then 2 else (if x<3282 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7618 : Finset ℕ := ([1596,1626,1628,1650,1652,1686,1720,1752,2614,2646,2680,2714,2716,2738,2772,3126,3158,3192,3226,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7618 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7618 1628 4
  · have he : independentCachedBranchMembers7618.erase 1628=independentCachedBranchMembers7616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7616
  · have he : independentCachedBranchMembers7618.filter (independentCachedEdge 1628)=independentCachedBranchMembers7617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7617
def independentCachedBranchMembers7619 : Finset ℕ := ([1596,1626,1650,1720,2646,2716,3158,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7619 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7619 4 (fun x => (if x<2716 then (if x<1650 then (if x<1626 then 0 else 0) else (if x<1720 then 1 else (if x<2646 then 1 else 1))) else (if x<3228 then (if x<3158 then 1 else 2) else (if x<3252 then 2 else (if x<3282 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7620 : Finset ℕ := ([1594,1596,1626,1628,1650,1652,1686,1720,1752,2614,2646,2680,2714,2716,2738,2772,3126,3158,3192,3226,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7620 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7620 1594 4
  · have he : independentCachedBranchMembers7620.erase 1594=independentCachedBranchMembers7618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7618
  · have he : independentCachedBranchMembers7620.filter (independentCachedEdge 1594)=independentCachedBranchMembers7619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7619
def independentCachedBranchMembers7621 : Finset ℕ := ([1650,1652,1720,1752,2614,2646,2714,2716,3126,3158,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7621 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7621 4 (fun x => (if x<2714 then (if x<1752 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<2614 then 1 else (if x<2646 then 1 else 0))) else (if x<3158 then (if x<2716 then 1 else (if x<3126 then 0 else 2)) else (if x<3226 then 3 else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7622 : Finset ℕ := ([1594,1596,1626,1628,1650,1652,1686,1720,1752,1776,2614,2646,2680,2714,2716,2738,2772,3126,3158,3192,3226,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7622 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7622 1776 4
  · have he : independentCachedBranchMembers7622.erase 1776=independentCachedBranchMembers7620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7620
  · have he : independentCachedBranchMembers7622.filter (independentCachedEdge 1776)=independentCachedBranchMembers7621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7621
def independentCachedBranchMembers7623 : Finset ℕ := ([1594,1596,1626,1628,1720,1752,2680,2714,2716,3192,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound7623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7623 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7623 4 (fun x => (if x<2680 then (if x<1628 then (if x<1596 then 0 else (if x<1626 then 1 else 1)) else (if x<1720 then 0 else (if x<1752 then 2 else 3))) else (if x<3192 then (if x<2714 then 0 else (if x<2716 then 2 else 3)) else (if x<3226 then 1 else (if x<3228 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7624 : Finset ℕ := ([246,1594,1596,1626,1628,1650,1652,1686,1720,1752,1776,2614,2646,2680,2714,2716,2738,2772,3126,3158,3192,3226,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7624 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7624 246 4
  · have he : independentCachedBranchMembers7624.erase 246=independentCachedBranchMembers7622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7622
  · have he : independentCachedBranchMembers7624.filter (independentCachedEdge 246)=independentCachedBranchMembers7623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7623
def independentCachedBranchMembers7625 : Finset ℕ := ([1594,1596,1626,1628,1650,1652,2614,2646,2680,3126,3158,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7625 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7625 4 (fun x => (if x<2614 then (if x<1628 then (if x<1596 then 0 else (if x<1626 then 1 else 1)) else (if x<1650 then 0 else (if x<1652 then 2 else 3))) else (if x<3126 then (if x<2646 then 2 else (if x<2680 then 3 else 0)) else (if x<3158 then 3 else (if x<3192 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7626 : Finset ℕ := ([144,246,1594,1596,1626,1628,1650,1652,1686,1720,1752,1776,2614,2646,2680,2714,2716,2738,2772,3126,3158,3192,3226,3228,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7626 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7626 144 4
  · have he : independentCachedBranchMembers7626.erase 144=independentCachedBranchMembers7624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7624
  · have he : independentCachedBranchMembers7626.filter (independentCachedEdge 144)=independentCachedBranchMembers7625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7625
def independentCachedBranchMembers7627 : Finset ℕ := ([36,66,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7627 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7627 238 5
  · have he : independentCachedBranchMembers7627.erase 238=independentCachedBranchMembers7609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7609
  · have he : independentCachedBranchMembers7627.filter (independentCachedEdge 238)=independentCachedBranchMembers7626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7626
def independentCachedBranchMembers7628 : Finset ℕ := ([1596,1626,1628,1642,1644,1702,1734,1776,2606,2638,2680,2738,2772,2786,2788,3118,3150,3192,3252,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7628 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7628 5 (fun x => (if x<2738 then (if x<1702 then (if x<1628 then (if x<1626 then 0 else 0) else (if x<1642 then 1 else (if x<1644 then 1 else 2))) else (if x<2606 then (if x<1734 then 2 else (if x<1776 then 1 else 0)) else (if x<2638 then 2 else (if x<2680 then 1 else 0)))) else (if x<3150 then (if x<2786 then (if x<2772 then 2 else 1) else (if x<2788 then 1 else (if x<3118 then 2 else 3))) else (if x<3282 then (if x<3192 then 4 else (if x<3252 then 3 else 3)) else (if x<3298 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7629 : Finset ℕ := ([1596,1626,1642,1734,2638,2786,3150,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7629 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7629 4 (fun x => (if x<2786 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1734 then 1 else (if x<2638 then 1 else 1))) else (if x<3252 then (if x<3150 then 1 else 2) else (if x<3282 then 0 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7630 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1702,1734,1776,2606,2638,2680,2738,2772,2786,2788,3118,3150,3192,3252,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7630 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7630 1594 4
  · have he : independentCachedBranchMembers7630.erase 1594=independentCachedBranchMembers7628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7628
  · have he : independentCachedBranchMembers7630.filter (independentCachedEdge 1594)=independentCachedBranchMembers7629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7629
def independentCachedBranchMembers7631 : Finset ℕ := ([1642,1644,1702,1734,2606,2638,2786,2788,3118,3150,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7631 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7631 4 (fun x => (if x<2786 then (if x<1734 then (if x<1644 then 0 else (if x<1702 then 1 else 0)) else (if x<2606 then 1 else (if x<2638 then 0 else 1))) else (if x<3150 then (if x<2788 then 0 else (if x<3118 then 1 else 2)) else (if x<3298 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7632 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1686,1702,1734,1776,2606,2638,2680,2738,2772,2786,2788,3118,3150,3192,3252,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7632 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7632 1686 4
  · have he : independentCachedBranchMembers7632.erase 1686=independentCachedBranchMembers7630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7630
  · have he : independentCachedBranchMembers7632.filter (independentCachedEdge 1686)=independentCachedBranchMembers7631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7631
def independentCachedBranchMembers7633 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,2606,2638,2680,3118,3150,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7633 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7633 4 (fun x => (if x<2606 then (if x<1628 then (if x<1596 then 0 else (if x<1626 then 1 else 1)) else (if x<1642 then 0 else (if x<1644 then 2 else 3))) else (if x<3118 then (if x<2638 then 2 else (if x<2680 then 3 else 0)) else (if x<3150 then 3 else (if x<3192 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7634 : Finset ℕ := ([246,1594,1596,1626,1628,1642,1644,1686,1702,1734,1776,2606,2638,2680,2738,2772,2786,2788,3118,3150,3192,3252,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7634 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7634 246 4
  · have he : independentCachedBranchMembers7634.erase 246=independentCachedBranchMembers7632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7632
  · have he : independentCachedBranchMembers7634.filter (independentCachedEdge 246)=independentCachedBranchMembers7633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7633
def independentCachedBranchMembers7635 : Finset ℕ := ([1594,1596,1626,1628,1702,1734,2680,2786,2788,3192,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7635 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7635 4 (fun x => (if x<2680 then (if x<1628 then (if x<1596 then 0 else (if x<1626 then 1 else 1)) else (if x<1702 then 0 else (if x<1734 then 2 else 3))) else (if x<3192 then (if x<2786 then 0 else (if x<2788 then 2 else 3)) else (if x<3298 then 1 else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7636 : Finset ℕ := ([144,246,1594,1596,1626,1628,1642,1644,1686,1702,1734,1776,2606,2638,2680,2738,2772,2786,2788,3118,3150,3192,3252,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7636 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7636 144 4
  · have he : independentCachedBranchMembers7636.erase 144=independentCachedBranchMembers7634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7634
  · have he : independentCachedBranchMembers7636.filter (independentCachedEdge 144)=independentCachedBranchMembers7635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7635
def independentCachedBranchMembers7637 : Finset ℕ := ([36,66,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7637 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7637 136 5
  · have he : independentCachedBranchMembers7637.erase 136=independentCachedBranchMembers7627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7627
  · have he : independentCachedBranchMembers7637.filter (independentCachedEdge 136)=independentCachedBranchMembers7636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7636
def independentCachedBranchMembers7638 : Finset ℕ := ([1596,1642,1650,1678,1686,1702,1752,1768,1776,2606,2614,2680,2716,2732,2762,2786,3118,3126,3192,3228,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7638 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7638 5 (fun x => (if x<2680 then (if x<1702 then (if x<1650 then (if x<1642 then 0 else 0) else (if x<1678 then 1 else (if x<1686 then 0 else 1))) else (if x<1776 then (if x<1752 then 2 else (if x<1768 then 0 else 2)) else (if x<2606 then 3 else (if x<2614 then 0 else 1)))) else (if x<3126 then (if x<2762 then (if x<2716 then 0 else (if x<2732 then 0 else 2)) else (if x<2786 then 0 else (if x<3118 then 2 else 3))) else (if x<3252 then (if x<3192 then 4 else (if x<3228 then 3 else 4)) else (if x<3282 then 3 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7639 : Finset ℕ := ([1642,1650,1702,1752,2606,2614,2716,2786,3118,3126,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7639 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7639 4 (fun x => (if x<2716 then (if x<1752 then (if x<1650 then 0 else (if x<1702 then 1 else 0)) else (if x<2606 then 1 else (if x<2614 then 0 else 1))) else (if x<3126 then (if x<2786 then 1 else (if x<3118 then 0 else 2)) else (if x<3228 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7640 : Finset ℕ := ([1596,1626,1642,1650,1678,1686,1702,1752,1768,1776,2606,2614,2680,2716,2732,2762,2786,3118,3126,3192,3228,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7640 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7640 1626 4
  · have he : independentCachedBranchMembers7640.erase 1626=independentCachedBranchMembers7638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7638
  · have he : independentCachedBranchMembers7640.filter (independentCachedEdge 1626)=independentCachedBranchMembers7639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7639
def independentCachedBranchMembers7641 : Finset ℕ := ([1686,1702,1752,1768,1776,2606,2614,2680,3118,3126,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7641 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7641 4 (fun x => (if x<2606 then (if x<1752 then (if x<1702 then 0 else 1) else (if x<1768 then 0 else (if x<1776 then 1 else 2))) else (if x<3118 then (if x<2614 then 2 else (if x<2680 then 0 else 0)) else (if x<3126 then 3 else (if x<3192 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7642 : Finset ℕ := ([1686,1702,1776,2614,3126] : List ℕ).toFinset
theorem independentCachedBranchBound7642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7642 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7642 3 (fun x => (if x<1776 then (if x<1702 then 0 else 1) else (if x<2614 then 0 else (if x<3126 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7643 : Finset ℕ := ([1678,1686,1702,1752,1768,1776,2606,2614,2680,3118,3126,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7643 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7643 1678 3
  · have he : independentCachedBranchMembers7643.erase 1678=independentCachedBranchMembers7641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7641
  · have he : independentCachedBranchMembers7643.filter (independentCachedEdge 1678)=independentCachedBranchMembers7642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7642
def independentCachedBranchMembers7644 : Finset ℕ := ([66,1596,1626,1642,1650,1678,1686,1702,1752,1768,1776,2606,2614,2680,2716,2732,2762,2786,3118,3126,3192,3228,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7644 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7644 66 4
  · have he : independentCachedBranchMembers7644.erase 66=independentCachedBranchMembers7640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7640
  · have he : independentCachedBranchMembers7644.filter (independentCachedEdge 66)=independentCachedBranchMembers7643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7643
def independentCachedBranchMembers7645 : Finset ℕ := ([1642,1650,1678,1686,1768,1776,2680,2716,2786,3192,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7645 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7645 4 (fun x => (if x<2680 then (if x<1686 then (if x<1650 then 0 else (if x<1678 then 1 else 0)) else (if x<1768 then 1 else (if x<1776 then 2 else 3))) else (if x<3192 then (if x<2716 then 0 else (if x<2786 then 0 else 2)) else (if x<3228 then 1 else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7646 : Finset ℕ := ([36,66,1596,1626,1642,1650,1678,1686,1702,1752,1768,1776,2606,2614,2680,2716,2732,2762,2786,3118,3126,3192,3228,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7646 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7646 36 4
  · have he : independentCachedBranchMembers7646.erase 36=independentCachedBranchMembers7644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7644
  · have he : independentCachedBranchMembers7646.filter (independentCachedEdge 36)=independentCachedBranchMembers7645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7645
def independentCachedBranchMembers7647 : Finset ℕ := ([36,66,68,136,144,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2606,2614,2638,2646,2662,2680,2714,2716,2732,2738,2762,2772,2786,2788,3118,3126,3150,3158,3174,3192,3226,3228,3242,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7647 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7647 68 5
  · have he : independentCachedBranchMembers7647.erase 68=independentCachedBranchMembers7637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7637
  · have he : independentCachedBranchMembers7647.filter (independentCachedEdge 68)=independentCachedBranchMembers7646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7646
end EntropyDesigns.QuadraticRefinement
