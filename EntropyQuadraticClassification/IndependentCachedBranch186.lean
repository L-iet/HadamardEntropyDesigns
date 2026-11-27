/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch185
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8736 : Finset ℕ := ([72,80,130,252,1582,1590,1594,1628,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2726,2738,2772,2776,3102,3180,3188,3192,3238,3242,3250,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8736 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8736 1594 4
  · have he : independentCachedBranchMembers8736.erase 1594=independentCachedBranchMembers8734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8734
  · have he : independentCachedBranchMembers8736.filter (independentCachedEdge 1594)=independentCachedBranchMembers8735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8735
def independentCachedBranchMembers8737 : Finset ℕ := ([40,48,66,72,80,130,132,144,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8737 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8737 66 5
  · have he : independentCachedBranchMembers8737.erase 66=independentCachedBranchMembers8721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8721
  · have he : independentCachedBranchMembers8737.filter (independentCachedEdge 66)=independentCachedBranchMembers8736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8736
def independentCachedBranchMembers8738 : Finset ℕ := ([48,250,1594,1614,1622,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2738,2744,2758,2772,3102,3178,3186,3192,3242,3256,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8738 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8738 5 (fun x => (if x<2674 then (if x<1686 then (if x<1614 then (if x<250 then 0 else (if x<1594 then 0 else 0)) else (if x<1622 then 1 else (if x<1678 then 2 else 2))) else (if x<1768 then (if x<1692 then 1 else (if x<1762 then 3 else 1)) else (if x<2590 then (if x<1776 then 3 else 0) else (if x<2666 then 1 else 1)))) else (if x<3178 then (if x<2744 then (if x<2680 then 0 else (if x<2738 then 4 else 1)) else (if x<2772 then (if x<2758 then 0 else 1) else (if x<3102 then 4 else 2))) else (if x<3242 then (if x<3186 then 3 else (if x<3192 then 2 else 0)) else (if x<3270 then (if x<3256 then 2 else 3) else (if x<3276 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8739 : Finset ℕ := ([250,1614,1622,1762,1768,1776,2590,2738,2744,3102,3242,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8739 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8739 4 (fun x => (if x<2590 then (if x<1762 then (if x<1614 then 0 else (if x<1622 then 1 else 2)) else (if x<1768 then 0 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2738 then 1 else (if x<2744 then 0 else 1)) else (if x<3242 then 2 else (if x<3256 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8740 : Finset ℕ := ([48,132,250,1594,1614,1622,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2738,2744,2758,2772,3102,3178,3186,3192,3242,3256,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8740 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8740 132 4
  · have he : independentCachedBranchMembers8740.erase 132=independentCachedBranchMembers8738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8738
  · have he : independentCachedBranchMembers8740.filter (independentCachedEdge 132)=independentCachedBranchMembers8739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8739
def independentCachedBranchMembers8741 : Finset ℕ := ([48,1614,1678,1692,1762,1776,2590,2674,2738,3102,3186,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8741 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8741 4 (fun x => (if x<2590 then (if x<1692 then (if x<1614 then 0 else (if x<1678 then 0 else 1)) else (if x<1762 then 2 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2674 then 1 else (if x<2738 then 1 else 0)) else (if x<3186 then 2 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8742 : Finset ℕ := ([40,48,132,250,1594,1614,1622,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2738,2744,2758,2772,3102,3178,3186,3192,3242,3256,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8742 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8742 40 4
  · have he : independentCachedBranchMembers8742.erase 40=independentCachedBranchMembers8740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8740
  · have he : independentCachedBranchMembers8742.filter (independentCachedEdge 40)=independentCachedBranchMembers8741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8741
def independentCachedBranchMembers8743 : Finset ℕ := ([250,1614,1678,1762,1768,2590,2674,2680,2738,2744,2772,3178,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8743 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8743 4 (fun x => (if x<2680 then (if x<1762 then (if x<1614 then 0 else (if x<1678 then 1 else 2)) else (if x<2590 then (if x<1768 then 0 else 1) else (if x<2674 then 1 else 0))) else (if x<3178 then (if x<2744 then (if x<2738 then 2 else 3) else (if x<2772 then 1 else 3)) else (if x<3270 then (if x<3242 then 0 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8744 : Finset ℕ := ([1762,1768,2590,2772,3178,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8744 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8744 3 (fun x => (if x<2772 then (if x<1768 then 0 else (if x<2590 then 1 else 0)) else (if x<3178 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8745 : Finset ℕ := ([48,250,1614,1678,1762,1768,2590,2674,2680,2738,2744,2772,3178,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8745 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8745 48 3
  · have he : independentCachedBranchMembers8745.erase 48=independentCachedBranchMembers8743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8743
  · have he : independentCachedBranchMembers8745.filter (independentCachedEdge 48)=independentCachedBranchMembers8744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8744
def independentCachedBranchMembers8746 : Finset ℕ := ([40,48,132,250,1594,1614,1622,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2738,2744,2758,2772,3102,3178,3186,3192,3242,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8746 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8746 3284 4
  · have he : independentCachedBranchMembers8746.erase 3284=independentCachedBranchMembers8742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8742
  · have he : independentCachedBranchMembers8746.filter (independentCachedEdge 3284)=independentCachedBranchMembers8745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8745
def independentCachedBranchMembers8747 : Finset ℕ := ([132,1622,1678,1692,1768,2590,2666,2680,2738,2758,2772,3186,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8747 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8747 4 (fun x => (if x<2680 then (if x<1692 then (if x<1622 then 0 else (if x<1678 then 1 else 0)) else (if x<2590 then (if x<1768 then 1 else 2) else (if x<2666 then 1 else 2))) else (if x<3186 then (if x<2758 then (if x<2738 then 0 else 3) else (if x<2772 then 3 else 1)) else (if x<3256 then (if x<3242 then 0 else 2) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8748 : Finset ℕ := ([1678,1692,2590,2738,3186,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8748 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8748 3 (fun x => (if x<2738 then (if x<1692 then 0 else (if x<2590 then 1 else 0)) else (if x<3186 then 2 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8749 : Finset ℕ := ([40,132,1622,1678,1692,1768,2590,2666,2680,2738,2758,2772,3186,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8749 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8749 40 3
  · have he : independentCachedBranchMembers8749.erase 40=independentCachedBranchMembers8747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8747
  · have he : independentCachedBranchMembers8749.filter (independentCachedEdge 40)=independentCachedBranchMembers8748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8748
def independentCachedBranchMembers8750 : Finset ℕ := ([40,48,132,250,1594,1614,1622,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2738,2744,2758,2772,3102,3178,3186,3192,3242,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8750 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8750 3250 4
  · have he : independentCachedBranchMembers8750.erase 3250=independentCachedBranchMembers8746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8746
  · have he : independentCachedBranchMembers8750.filter (independentCachedEdge 3250)=independentCachedBranchMembers8749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8749
def independentCachedBranchMembers8751 : Finset ℕ := ([40,48,132,250,1614,1622,1692,1762,2666,2674,2744,2758,3178,3186,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8751 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8751 4 (fun x => (if x<2666 then (if x<1614 then (if x<132 then (if x<48 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1692 then (if x<1622 then 2 else 3) else (if x<1762 then 2 else 3))) else (if x<3178 then (if x<2744 then (if x<2674 then 0 else 1) else (if x<2758 then 1 else 0)) else (if x<3256 then (if x<3186 then 2 else 3) else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8752 : Finset ℕ := ([40,48,132,250,1594,1614,1622,1628,1678,1686,1692,1762,1768,1776,2590,2666,2674,2680,2738,2744,2758,2772,3102,3178,3186,3192,3242,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8752 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8752 1628 4
  · have he : independentCachedBranchMembers8752.erase 1628=independentCachedBranchMembers8750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8750
  · have he : independentCachedBranchMembers8752.filter (independentCachedEdge 1628)=independentCachedBranchMembers8751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8751
def independentCachedBranchMembers8753 : Finset ℕ := ([36,40,48,66,72,80,130,132,144,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8753 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8753 36 5
  · have he : independentCachedBranchMembers8753.erase 36=independentCachedBranchMembers8737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8737
  · have he : independentCachedBranchMembers8753.filter (independentCachedEdge 36)=independentCachedBranchMembers8752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8752
def independentCachedBranchMembers8754 : Finset ℕ := ([130,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3102,3178,3188,3192,3238,3242,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8754 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8754 5 (fun x => (if x<2738 then (if x<1686 then (if x<1596 then (if x<250 then 0 else (if x<1582 then 0 else 1)) else (if x<1622 then 2 else (if x<1626 then 1 else 2))) else (if x<1776 then (if x<1690 then 2 else (if x<1762 then 0 else 0)) else (if x<2674 then (if x<2668 then 2 else 3) else (if x<2732 then 3 else 1)))) else (if x<3188 then (if x<2772 then (if x<2758 then 0 else (if x<2762 then 3 else 0)) else (if x<3102 then (if x<2776 then 1 else 3) else (if x<3178 then 2 else 4))) else (if x<3242 then (if x<3192 then 4 else (if x<3238 then 2 else 4)) else (if x<3276 then (if x<3256 then 0 else 4) else (if x<3282 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8755 : Finset ℕ := ([1596,1686,1690,1762,2668,2738,2758,2762,3102,3178,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8755 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8755 4 (fun x => (if x<2758 then (if x<1762 then (if x<1686 then 0 else (if x<1690 then 0 else 1)) else (if x<2668 then 1 else (if x<2738 then 0 else 1))) else (if x<3178 then (if x<2762 then 0 else (if x<3102 then 1 else 2)) else (if x<3256 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8756 : Finset ℕ := ([80,130,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3102,3178,3188,3192,3238,3242,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8756 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8756 80 4
  · have he : independentCachedBranchMembers8756.erase 80=independentCachedBranchMembers8754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8754
  · have he : independentCachedBranchMembers8756.filter (independentCachedEdge 80)=independentCachedBranchMembers8755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8755
def independentCachedBranchMembers8757 : Finset ℕ := ([1626,1690,1762,1776,2674,2738,2762,2776,3102,3188,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8757 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8757 4 (fun x => (if x<2762 then (if x<1776 then (if x<1690 then 0 else (if x<1762 then 1 else 0)) else (if x<2674 then 1 else (if x<2738 then 0 else 1))) else (if x<3188 then (if x<2776 then 0 else (if x<3102 then 1 else 2)) else (if x<3238 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8758 : Finset ℕ := ([40,80,130,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3102,3178,3188,3192,3238,3242,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8758 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8758 40 4
  · have he : independentCachedBranchMembers8758.erase 40=independentCachedBranchMembers8756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8756
  · have he : independentCachedBranchMembers8758.filter (independentCachedEdge 40)=independentCachedBranchMembers8757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8757
def independentCachedBranchMembers8759 : Finset ℕ := ([40,80,130,250,1582,1622,1690,1762,2668,2674,2758,2776,3178,3188,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8759 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8759 4 (fun x => (if x<2668 then (if x<1582 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3178 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3238 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8760 : Finset ℕ := ([40,80,130,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3102,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8760 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8760 3252 4
  · have he : independentCachedBranchMembers8760.erase 3252=independentCachedBranchMembers8758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8758
  · have he : independentCachedBranchMembers8760.filter (independentCachedEdge 3252)=independentCachedBranchMembers8759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8759
def independentCachedBranchMembers8761 : Finset ℕ := ([40,80,130,250,1596,1626,1686,1776,2732,2738,2762,2772,3178,3188,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8761 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8761 4 (fun x => (if x<2732 then (if x<1596 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3178 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3238 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8762 : Finset ℕ := ([40,80,130,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8762 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8762 3174 4
  · have he : independentCachedBranchMembers8762.erase 3174=independentCachedBranchMembers8760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8760
  · have he : independentCachedBranchMembers8762.filter (independentCachedEdge 3174)=independentCachedBranchMembers8761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8761
def independentCachedBranchMembers8763 : Finset ℕ := ([1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8763 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8763 4 (fun x => (if x<2668 then (if x<1686 then (if x<1622 then (if x<1596 then 0 else 1) else (if x<1626 then 0 else 1)) else (if x<1762 then (if x<1690 then 1 else 0) else (if x<1776 then 0 else 1))) else (if x<2758 then (if x<2732 then (if x<2674 then 2 else 2) else (if x<2738 then 3 else 3)) else (if x<2772 then (if x<2762 then 2 else 3) else (if x<2776 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8764 : Finset ℕ := ([40,80,130,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8764 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8764 3072 4
  · have he : independentCachedBranchMembers8764.erase 3072=independentCachedBranchMembers8762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8762
  · have he : independentCachedBranchMembers8764.filter (independentCachedEdge 3072)=independentCachedBranchMembers8763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8763
def independentCachedBranchMembers8765 : Finset ℕ := ([40,250,1582,1596,1626,1690,2668,2732,2762,2776,3102,3178,3192,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8765 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8765 4 (fun x => (if x<2762 then (if x<1626 then (if x<1582 then (if x<250 then 0 else 0) else (if x<1596 then 1 else 2)) else (if x<2668 then (if x<1690 then 1 else 2) else (if x<2732 then 2 else 1))) else (if x<3192 then (if x<3102 then (if x<2776 then 2 else 1) else (if x<3178 then 3 else 0)) else (if x<3256 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8766 : Finset ℕ := ([40,80,130,246,250,1582,1596,1622,1626,1686,1690,1762,1776,2668,2674,2732,2738,2758,2762,2772,2776,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8766 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8766 246 4
  · have he : independentCachedBranchMembers8766.erase 246=independentCachedBranchMembers8764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8764
  · have he : independentCachedBranchMembers8766.filter (independentCachedEdge 246)=independentCachedBranchMembers8765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8765
def independentCachedBranchMembers8767 : Finset ℕ := ([80,130,1596,1622,1626,1762,2674,2732,2758,2762,3102,3188,3192,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8767 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8767 4 (fun x => (if x<2758 then (if x<1626 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1622 then 1 else 1)) else (if x<2674 then (if x<1762 then 2 else 2) else (if x<2732 then 2 else 1))) else (if x<3192 then (if x<3102 then (if x<2762 then 1 else 2) else (if x<3188 then 3 else 0)) else (if x<3242 then (if x<3238 then 3 else 0) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
