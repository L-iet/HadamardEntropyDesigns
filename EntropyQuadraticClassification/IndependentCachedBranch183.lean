/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch182
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8640 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1768,1776,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8640 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8640 40 4
  · have he : independentCachedBranchMembers8640.erase 40=independentCachedBranchMembers8638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8638
  · have he : independentCachedBranchMembers8640.filter (independentCachedEdge 40)=independentCachedBranchMembers8639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8639
def independentCachedBranchMembers8641 : Finset ℕ := ([40,48,72,80,130,132,250,252,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8641 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8641 4 (fun x => (if x<3178 then (if x<130 then (if x<72 then (if x<48 then 0 else 1) else (if x<80 then 1 else 0)) else (if x<250 then (if x<132 then 0 else 1) else (if x<252 then 0 else 1))) else (if x<3238 then (if x<3186 then (if x<3180 then 2 else 3) else (if x<3188 then 3 else 2)) else (if x<3270 then (if x<3256 then 2 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8642 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1768,1776,2590,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8642 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8642 2590 4
  · have he : independentCachedBranchMembers8642.erase 2590=independentCachedBranchMembers8640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8640
  · have he : independentCachedBranchMembers8642.filter (independentCachedEdge 2590)=independentCachedBranchMembers8641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8641
def independentCachedBranchMembers8643 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8643 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8643 3174 5
  · have he : independentCachedBranchMembers8643.erase 3174=independentCachedBranchMembers8623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8623
  · have he : independentCachedBranchMembers8643.filter (independentCachedEdge 3174)=independentCachedBranchMembers8642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8642
def independentCachedBranchMembers8644 : Finset ℕ := ([1594,1596,1614,1626,1628,1678,1686,1692,1764,1768,1776,2590,2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8644 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8644 5 (fun x => (if x<2666 then (if x<1686 then (if x<1626 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1628 then 1 else (if x<1678 then 2 else 1))) else (if x<1768 then (if x<1692 then 0 else (if x<1764 then 3 else 2)) else (if x<1776 then 1 else (if x<2590 then 3 else 0)))) else (if x<2738 then (if x<2676 then (if x<2668 then 0 else (if x<2674 then 2 else 3)) else (if x<2726 then 4 else (if x<2732 then 2 else 1))) else (if x<2762 then (if x<2744 then 0 else (if x<2758 then 3 else 0)) else (if x<2772 then 1 else (if x<2776 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8645 : Finset ℕ := ([1594,1596,1686,1768,2666,2668,2732,2744,2758,2772] : List ℕ).toFinset
theorem independentCachedBranchBound8645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8645 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8645 4 (fun x => (if x<2668 then (if x<1686 then (if x<1596 then 0 else 1) else (if x<1768 then 0 else (if x<2666 then 1 else 0))) else (if x<2744 then (if x<2732 then 1 else 2) else (if x<2758 then 1 else (if x<2772 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8646 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1692,1764,1768,1776,2590,2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8646 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8646 1590 4
  · have he : independentCachedBranchMembers8646.erase 1590=independentCachedBranchMembers8644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8644
  · have he : independentCachedBranchMembers8646.filter (independentCachedEdge 1590)=independentCachedBranchMembers8645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8645
def independentCachedBranchMembers8647 : Finset ℕ := ([1596,1628,1692,1764,1768,1776,2668,2676,2732,2744,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8647 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8647 4 (fun x => (if x<2668 then (if x<1764 then (if x<1628 then 0 else (if x<1692 then 1 else 2)) else (if x<1768 then 0 else (if x<1776 then 1 else 2))) else (if x<2744 then (if x<2676 then 0 else (if x<2732 then 3 else 3)) else (if x<2772 then 2 else (if x<2776 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8648 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8648 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8648 1762 4
  · have he : independentCachedBranchMembers8648.erase 1762=independentCachedBranchMembers8646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8646
  · have he : independentCachedBranchMembers8648.filter (independentCachedEdge 1762)=independentCachedBranchMembers8647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8647
def independentCachedBranchMembers8649 : Finset ℕ := ([1594,1626,1678,1686,1692,1764,2666,2674,2726,2732,2758,2772] : List ℕ).toFinset
theorem independentCachedBranchBound8649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8649 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8649 4 (fun x => (if x<2666 then (if x<1686 then (if x<1626 then 0 else (if x<1678 then 1 else 0)) else (if x<1692 then 1 else (if x<1764 then 2 else 2))) else (if x<2732 then (if x<2674 then 1 else (if x<2726 then 0 else 1)) else (if x<2758 then 2 else (if x<2772 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8650 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8650 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8650 1690 4
  · have he : independentCachedBranchMembers8650.erase 1690=independentCachedBranchMembers8648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8648
  · have he : independentCachedBranchMembers8650.filter (independentCachedEdge 1690)=independentCachedBranchMembers8649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8649
def independentCachedBranchMembers8651 : Finset ℕ := ([1590,1614,1626,1628,1686,1768,2666,2668,2726,2738,2762,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8651 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8651 4 (fun x => (if x<2666 then (if x<1628 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<1686 then 2 else (if x<1768 then 1 else 2))) else (if x<2738 then (if x<2668 then 1 else (if x<2726 then 2 else 1)) else (if x<2762 then 0 else (if x<2776 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8652 : Finset ℕ := ([1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8652 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8652 1622 4
  · have he : independentCachedBranchMembers8652.erase 1622=independentCachedBranchMembers8650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8650
  · have he : independentCachedBranchMembers8652.filter (independentCachedEdge 1622)=independentCachedBranchMembers8651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8651
def independentCachedBranchMembers8653 : Finset ℕ := ([1590,1594,1596,1614,1678,1776,2674,2676,2738,2744,2758,2762] : List ℕ).toFinset
theorem independentCachedBranchBound8653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8653 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8653 4 (fun x => (if x<2674 then (if x<1614 then (if x<1594 then 0 else (if x<1596 then 1 else 2)) else (if x<1678 then 0 else (if x<1776 then 1 else 2))) else (if x<2744 then (if x<2676 then 1 else (if x<2738 then 2 else 0)) else (if x<2758 then 2 else (if x<2762 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8654 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8654 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8654 1582 4
  · have he : independentCachedBranchMembers8654.erase 1582=independentCachedBranchMembers8652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8652
  · have he : independentCachedBranchMembers8654.filter (independentCachedEdge 1582)=independentCachedBranchMembers8653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8653
def independentCachedBranchMembers8655 : Finset ℕ := ([1582,1590,1614,1622,1690,1692,1762,1764,2666,2668,2674,2676,2726,2744,2758,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8655 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8655 4 (fun x => (if x<2666 then (if x<1690 then (if x<1614 then (if x<1590 then 0 else 1) else (if x<1622 then 1 else 0)) else (if x<1762 then (if x<1692 then 0 else 1) else (if x<1764 then 0 else 1))) else (if x<2726 then (if x<2674 then (if x<2668 then 2 else 3) else (if x<2676 then 3 else 2)) else (if x<2758 then (if x<2744 then 2 else 2) else (if x<2776 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8656 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8656 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8656 2680 4
  · have he : independentCachedBranchMembers8656.erase 2680=independentCachedBranchMembers8654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8654
  · have he : independentCachedBranchMembers8656.filter (independentCachedEdge 2680)=independentCachedBranchMembers8655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8655
def independentCachedBranchMembers8657 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8657 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8657 3072 5
  · have he : independentCachedBranchMembers8657.erase 3072=independentCachedBranchMembers8643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8643
  · have he : independentCachedBranchMembers8657.filter (independentCachedEdge 3072)=independentCachedBranchMembers8656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8656
def independentCachedBranchMembers8658 : Finset ℕ := ([132,252,1590,1594,1614,1628,1678,1692,1764,1768,2668,2674,2732,2738,2758,2762,2772,2776,3102,3178,3188,3192,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8658 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8658 5 (fun x => (if x<2738 then (if x<1678 then (if x<1594 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1614 then 2 else (if x<1628 then 1 else 2))) else (if x<1768 then (if x<1692 then 2 else (if x<1764 then 0 else 0)) else (if x<2674 then (if x<2668 then 2 else 3) else (if x<2732 then 3 else 0)))) else (if x<3188 then (if x<2772 then (if x<2758 then 1 else (if x<2762 then 3 else 1)) else (if x<3102 then (if x<2776 then 0 else 3) else (if x<3178 then 2 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3238 then 2 else 4)) else (if x<3276 then (if x<3256 then 0 else 4) else (if x<3282 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8659 : Finset ℕ := ([1594,1678,1692,1764,2674,2732,2758,2772,3102,3188,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8659 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8659 4 (fun x => (if x<2758 then (if x<1764 then (if x<1678 then 0 else (if x<1692 then 0 else 1)) else (if x<2674 then 1 else (if x<2732 then 0 else 1))) else (if x<3188 then (if x<2772 then 0 else (if x<3102 then 1 else 2)) else (if x<3256 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8660 : Finset ℕ := ([72,132,252,1590,1594,1614,1628,1678,1692,1764,1768,2668,2674,2732,2738,2758,2762,2772,2776,3102,3178,3188,3192,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8660 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8660 72 4
  · have he : independentCachedBranchMembers8660.erase 72=independentCachedBranchMembers8658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8658
  · have he : independentCachedBranchMembers8660.filter (independentCachedEdge 72)=independentCachedBranchMembers8659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8659
def independentCachedBranchMembers8661 : Finset ℕ := ([1628,1692,1764,1768,2668,2732,2772,2776,3102,3178,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8661 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8661 4 (fun x => (if x<2772 then (if x<1768 then (if x<1692 then 0 else (if x<1764 then 1 else 0)) else (if x<2668 then 1 else (if x<2732 then 0 else 1))) else (if x<3178 then (if x<2776 then 0 else (if x<3102 then 1 else 2)) else (if x<3238 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8662 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1678,1692,1764,1768,2668,2674,2732,2738,2758,2762,2772,2776,3102,3178,3188,3192,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8662 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8662 48 4
  · have he : independentCachedBranchMembers8662.erase 48=independentCachedBranchMembers8660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8660
  · have he : independentCachedBranchMembers8662.filter (independentCachedEdge 48)=independentCachedBranchMembers8661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8661
def independentCachedBranchMembers8663 : Finset ℕ := ([48,72,132,252,1590,1614,1692,1764,2668,2674,2758,2776,3178,3188,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8663 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8663 4 (fun x => (if x<2668 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3178 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3238 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8664 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1678,1692,1764,1768,2668,2674,2732,2738,2758,2762,2772,2776,3102,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8664 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8664 3242 4
  · have he : independentCachedBranchMembers8664.erase 3242=independentCachedBranchMembers8662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8662
  · have he : independentCachedBranchMembers8664.filter (independentCachedEdge 3242)=independentCachedBranchMembers8663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8663
def independentCachedBranchMembers8665 : Finset ℕ := ([48,72,132,252,1594,1628,1678,1768,2732,2738,2762,2772,3178,3188,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8665 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8665 4 (fun x => (if x<2732 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3178 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3238 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8666 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1678,1692,1764,1768,2668,2674,2732,2738,2758,2762,2772,2776,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8666 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8666 3174 4
  · have he : independentCachedBranchMembers8666.erase 3174=independentCachedBranchMembers8664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8664
  · have he : independentCachedBranchMembers8666.filter (independentCachedEdge 3174)=independentCachedBranchMembers8665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8665
def independentCachedBranchMembers8667 : Finset ℕ := ([1590,1594,1614,1628,1678,1692,1764,1768,2668,2674,2732,2738,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8667 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8667 4 (fun x => (if x<2668 then (if x<1678 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1764 then (if x<1692 then 1 else 0) else (if x<1768 then 0 else 1))) else (if x<2758 then (if x<2732 then (if x<2674 then 2 else 2) else (if x<2738 then 3 else 3)) else (if x<2772 then (if x<2762 then 2 else 3) else (if x<2776 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8668 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1678,1692,1764,1768,2668,2674,2732,2738,2758,2762,2772,2776,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8668 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8668 3072 4
  · have he : independentCachedBranchMembers8668.erase 3072=independentCachedBranchMembers8666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8666
  · have he : independentCachedBranchMembers8668.filter (independentCachedEdge 3072)=independentCachedBranchMembers8667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8667
def independentCachedBranchMembers8669 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8669 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8669 2770 5
  · have he : independentCachedBranchMembers8669.erase 2770=independentCachedBranchMembers8657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8657
  · have he : independentCachedBranchMembers8669.filter (independentCachedEdge 2770)=independentCachedBranchMembers8668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8668
def independentCachedBranchMembers8670 : Finset ℕ := ([130,250,1582,1594,1622,1628,1678,1690,1762,1768,2666,2676,2726,2732,2738,2744,2762,2772,3102,3180,3186,3192,3242,3252,3270,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8670 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8670 5 (fun x => (if x<2732 then (if x<1678 then (if x<1594 then (if x<250 then 0 else (if x<1582 then 0 else 1)) else (if x<1622 then 2 else (if x<1628 then 1 else 2))) else (if x<1768 then (if x<1690 then 2 else (if x<1762 then 0 else 0)) else (if x<2676 then (if x<2666 then 2 else 3) else (if x<2726 then 3 else 3)))) else (if x<3186 then (if x<2762 then (if x<2738 then 1 else (if x<2744 then 0 else 3)) else (if x<3102 then (if x<2772 then 0 else 1) else (if x<3180 then 2 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3242 then 2 else 0)) else (if x<3282 then (if x<3270 then 3 else 4) else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8671 : Finset ℕ := ([1594,1690,1762,1768,2666,2738,2744,2762,3102,3180,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8671 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8671 4 (fun x => (if x<2744 then (if x<1768 then (if x<1690 then 0 else (if x<1762 then 1 else 0)) else (if x<2666 then 1 else (if x<2738 then 0 else 0))) else (if x<3180 then (if x<2762 then 1 else (if x<3102 then 1 else 2)) else (if x<3252 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
