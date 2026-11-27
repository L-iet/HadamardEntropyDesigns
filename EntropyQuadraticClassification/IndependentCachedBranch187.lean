/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch186
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8768 : Finset ℕ := ([40,80,130,144,246,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8768 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8768 144 4
  · have he : independentCachedBranchMembers8768.erase 144=independentCachedBranchMembers8766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8766
  · have he : independentCachedBranchMembers8768.filter (independentCachedEdge 144)=independentCachedBranchMembers8767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8767
def independentCachedBranchMembers8769 : Finset ℕ := ([80,130,1582,1686,1690,1776,2668,2738,2772,2776,3102,3188,3192,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8769 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8769 4 (fun x => (if x<2772 then (if x<1690 then (if x<1582 then (if x<130 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2668 then (if x<1776 then 2 else 2) else (if x<2738 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2776 then 1 else 2) else (if x<3188 then 3 else 0)) else (if x<3242 then (if x<3238 then 3 else 0) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8770 : Finset ℕ := ([40,66,80,130,144,246,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8770 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8770 66 4
  · have he : independentCachedBranchMembers8770.erase 66=independentCachedBranchMembers8768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8768
  · have he : independentCachedBranchMembers8770.filter (independentCachedEdge 66)=independentCachedBranchMembers8769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8769
def independentCachedBranchMembers8771 : Finset ℕ := ([40,250,1622,1686,1762,1776,2674,2738,2758,2772,3102,3178,3192,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8771 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8771 4 (fun x => (if x<2758 then (if x<1762 then (if x<1622 then (if x<250 then 0 else 0) else (if x<1686 then 1 else 2)) else (if x<2674 then (if x<1776 then 1 else 2) else (if x<2738 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2772 then 1 else 2) else (if x<3178 then 3 else 0)) else (if x<3256 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8772 : Finset ℕ := ([36,40,66,80,130,144,246,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8772 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8772 36 4
  · have he : independentCachedBranchMembers8772.erase 36=independentCachedBranchMembers8770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8770
  · have he : independentCachedBranchMembers8772.filter (independentCachedEdge 36)=independentCachedBranchMembers8771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8771
def independentCachedBranchMembers8773 : Finset ℕ := ([36,40,48,66,72,80,130,132,144,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8773 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8773 2764 5
  · have he : independentCachedBranchMembers8773.erase 2764=independentCachedBranchMembers8753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8753
  · have he : independentCachedBranchMembers8773.filter (independentCachedEdge 2764)=independentCachedBranchMembers8772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8772
def independentCachedBranchMembers8774 : Finset ℕ := ([132,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3102,3180,3186,3192,3242,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8774 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8774 5 (fun x => (if x<2732 then (if x<1686 then (if x<1596 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1614 then 2 else (if x<1626 then 1 else 2))) else (if x<1776 then (if x<1692 then 2 else (if x<1764 then 0 else 0)) else (if x<2676 then (if x<2666 then 2 else 3) else (if x<2726 then 3 else 3)))) else (if x<3186 then (if x<2762 then (if x<2738 then 0 else (if x<2744 then 1 else 3)) else (if x<3102 then (if x<2772 then 1 else 0) else (if x<3180 then 2 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3242 then 2 else 3)) else (if x<3276 then (if x<3270 then 0 else 4) else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8775 : Finset ℕ := ([1596,1692,1764,1776,2676,2732,2744,2772,3102,3186,3242,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8775 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8775 4 (fun x => (if x<2744 then (if x<1776 then (if x<1692 then 0 else (if x<1764 then 1 else 0)) else (if x<2676 then 1 else (if x<2732 then 0 else 0))) else (if x<3186 then (if x<2772 then 1 else (if x<3102 then 1 else 2)) else (if x<3242 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8776 : Finset ℕ := ([72,132,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3102,3180,3186,3192,3242,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8776 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8776 72 4
  · have he : independentCachedBranchMembers8776.erase 72=independentCachedBranchMembers8774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8774
  · have he : independentCachedBranchMembers8776.filter (independentCachedEdge 72)=independentCachedBranchMembers8775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8775
def independentCachedBranchMembers8777 : Finset ℕ := ([1626,1686,1692,1764,2666,2726,2732,2772,3102,3180,3242,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8777 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8777 4 (fun x => (if x<2732 then (if x<1764 then (if x<1686 then 0 else (if x<1692 then 0 else 1)) else (if x<2666 then 1 else (if x<2726 then 0 else 0))) else (if x<3180 then (if x<2772 then 1 else (if x<3102 then 1 else 2)) else (if x<3242 then 2 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8778 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3102,3180,3186,3192,3242,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8778 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8778 48 4
  · have he : independentCachedBranchMembers8778.erase 48=independentCachedBranchMembers8776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8776
  · have he : independentCachedBranchMembers8778.filter (independentCachedEdge 48)=independentCachedBranchMembers8777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8777
def independentCachedBranchMembers8779 : Finset ℕ := ([48,72,132,252,1590,1614,1692,1764,2666,2676,2726,2744,3180,3186,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8779 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8779 4 (fun x => (if x<2666 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3180 then (if x<2726 then (if x<2676 then 2 else 2) else (if x<2744 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8780 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3102,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8780 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8780 3282 4
  · have he : independentCachedBranchMembers8780.erase 3282=independentCachedBranchMembers8778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8778
  · have he : independentCachedBranchMembers8780.filter (independentCachedEdge 3282)=independentCachedBranchMembers8779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8779
def independentCachedBranchMembers8781 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1776,2732,2738,2762,2772,3180,3186,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8781 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8781 4 (fun x => (if x<2732 then (if x<1596 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3180 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8782 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8782 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8782 3174 4
  · have he : independentCachedBranchMembers8782.erase 3174=independentCachedBranchMembers8780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8780
  · have he : independentCachedBranchMembers8782.filter (independentCachedEdge 3174)=independentCachedBranchMembers8781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8781
def independentCachedBranchMembers8783 : Finset ℕ := ([1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772] : List ℕ).toFinset
theorem independentCachedBranchBound8783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8783 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8783 4 (fun x => (if x<2666 then (if x<1686 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1626 then 0 else 1)) else (if x<1764 then (if x<1692 then 1 else 0) else (if x<1776 then 0 else 1))) else (if x<2738 then (if x<2726 then (if x<2676 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2762 then (if x<2744 then 3 else 2) else (if x<2772 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8784 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8784 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8784 3072 4
  · have he : independentCachedBranchMembers8784.erase 3072=independentCachedBranchMembers8782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8782
  · have he : independentCachedBranchMembers8784.filter (independentCachedEdge 3072)=independentCachedBranchMembers8783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8783
def independentCachedBranchMembers8785 : Finset ℕ := ([72,252,1596,1614,1626,1692,2666,2732,2744,2762,3102,3180,3192,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8785 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8785 4 (fun x => (if x<2744 then (if x<1626 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1614 then 1 else 1)) else (if x<2666 then (if x<1692 then 2 else 2) else (if x<2732 then 2 else 2))) else (if x<3192 then (if x<3102 then (if x<2762 then 1 else 1) else (if x<3180 then 3 else 0)) else (if x<3276 then (if x<3242 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8786 : Finset ℕ := ([48,72,132,246,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8786 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8786 246 4
  · have he : independentCachedBranchMembers8786.erase 246=independentCachedBranchMembers8784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8784
  · have he : independentCachedBranchMembers8786.filter (independentCachedEdge 246)=independentCachedBranchMembers8785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8785
def independentCachedBranchMembers8787 : Finset ℕ := ([48,132,1590,1596,1626,1764,2676,2726,2732,2762,3102,3186,3192,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8787 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8787 4 (fun x => (if x<2732 then (if x<1626 then (if x<1590 then (if x<132 then 0 else 0) else (if x<1596 then 1 else 2)) else (if x<2676 then (if x<1764 then 1 else 2) else (if x<2726 then 2 else 1))) else (if x<3192 then (if x<3102 then (if x<2762 then 2 else 1) else (if x<3186 then 3 else 0)) else (if x<3270 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8788 : Finset ℕ := ([48,72,132,144,246,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8788 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8788 144 4
  · have he : independentCachedBranchMembers8788.erase 144=independentCachedBranchMembers8786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8786
  · have he : independentCachedBranchMembers8788.filter (independentCachedEdge 144)=independentCachedBranchMembers8787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8787
def independentCachedBranchMembers8789 : Finset ℕ := ([72,252,1590,1686,1764,1776,2676,2726,2738,2772,3102,3180,3192,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8789 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8789 4 (fun x => (if x<2738 then (if x<1764 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1686 then 1 else 2)) else (if x<2676 then (if x<1776 then 1 else 2) else (if x<2726 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2772 then 2 else 2) else (if x<3180 then 3 else 0)) else (if x<3276 then (if x<3242 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8790 : Finset ℕ := ([48,66,72,132,144,246,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8790 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8790 66 4
  · have he : independentCachedBranchMembers8790.erase 66=independentCachedBranchMembers8788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8788
  · have he : independentCachedBranchMembers8790.filter (independentCachedEdge 66)=independentCachedBranchMembers8789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8789
def independentCachedBranchMembers8791 : Finset ℕ := ([48,132,1614,1686,1692,1776,2666,2738,2744,2772,3102,3186,3192,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8791 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8791 4 (fun x => (if x<2744 then (if x<1692 then (if x<1614 then (if x<132 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2666 then (if x<1776 then 2 else 2) else (if x<2738 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2772 then 2 else 2) else (if x<3186 then 3 else 0)) else (if x<3270 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8792 : Finset ℕ := ([36,48,66,72,132,144,246,252,1590,1596,1614,1626,1686,1692,1764,1776,2666,2676,2726,2732,2738,2744,2762,2772,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8792 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8792 36 4
  · have he : independentCachedBranchMembers8792.erase 36=independentCachedBranchMembers8790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8790
  · have he : independentCachedBranchMembers8792.filter (independentCachedEdge 36)=independentCachedBranchMembers8791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8791
def independentCachedBranchMembers8793 : Finset ℕ := ([36,40,48,66,72,80,130,132,144,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8793 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8793 2730 5
  · have he : independentCachedBranchMembers8793.erase 2730=independentCachedBranchMembers8773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8773
  · have he : independentCachedBranchMembers8793.filter (independentCachedEdge 2730)=independentCachedBranchMembers8792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8792
def independentCachedBranchMembers8794 : Finset ℕ := ([1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8794 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8794 5 (fun x => (if x<2726 then (if x<1768 then (if x<1628 then (if x<1596 then 0 else (if x<1626 then 1 else 1)) else (if x<1678 then 0 else (if x<1686 then 0 else 1))) else (if x<2668 then (if x<1776 then 0 else (if x<2666 then 1 else 2)) else (if x<2674 then 3 else (if x<2676 then 3 else 2)))) else (if x<3192 then (if x<2776 then (if x<2744 then 2 else (if x<2758 then 2 else 3)) else (if x<3102 then 3 else (if x<3174 then 0 else 2))) else (if x<3252 then (if x<3244 then 0 else (if x<3250 then 4 else 4)) else (if x<3276 then (if x<3274 then 1 else 4) else (if x<3284 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8795 : Finset ℕ := ([1594,1626,1678,1686,2666,2674,2726,2758,3102,3174,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8795 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8795 4 (fun x => (if x<2726 then (if x<1686 then (if x<1626 then 0 else (if x<1678 then 1 else 0)) else (if x<2666 then 1 else (if x<2674 then 1 else 0))) else (if x<3174 then (if x<2758 then 1 else (if x<3102 then 0 else 2)) else (if x<3250 then 2 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8796 : Finset ℕ := ([252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8796 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8796 252 4
  · have he : independentCachedBranchMembers8796.erase 252=independentCachedBranchMembers8794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8794
  · have he : independentCachedBranchMembers8796.filter (independentCachedEdge 252)=independentCachedBranchMembers8795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8795
def independentCachedBranchMembers8797 : Finset ℕ := ([1596,1628,1768,1776,2668,2676,2744,2776,3102,3174,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8797 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8797 4 (fun x => (if x<2744 then (if x<1776 then (if x<1628 then 0 else (if x<1768 then 1 else 0)) else (if x<2668 then 1 else (if x<2676 then 0 else 1))) else (if x<3174 then (if x<2776 then 0 else (if x<3102 then 1 else 2)) else (if x<3250 then 2 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8798 : Finset ℕ := ([132,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8798 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8798 132 4
  · have he : independentCachedBranchMembers8798.erase 132=independentCachedBranchMembers8796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8796
  · have he : independentCachedBranchMembers8798.filter (independentCachedEdge 132)=independentCachedBranchMembers8797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8797
def independentCachedBranchMembers8799 : Finset ℕ := ([1594,1596,1678,1776,2674,2676,2744,2758,3102,3174,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8799 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8799 4 (fun x => (if x<2744 then (if x<1776 then (if x<1596 then 0 else (if x<1678 then 1 else 0)) else (if x<2674 then 1 else (if x<2676 then 0 else 1))) else (if x<3174 then (if x<2758 then 1 else (if x<3102 then 0 else 2)) else (if x<3244 then 2 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
