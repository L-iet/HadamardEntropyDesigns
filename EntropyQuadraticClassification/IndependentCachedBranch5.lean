/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch4
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers640 : Finset ℕ := ([1590,1628,1692,1738,1748,1768,2620,2646,2710,2730,2740,2786,3102,3158,3178,3188,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers640 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers640 5 (fun x => (if x<2730 then (if x<1748 then (if x<1692 then (if x<1628 then 0 else 0) else (if x<1738 then 1 else 1)) else (if x<2620 then (if x<1768 then 2 else 2) else (if x<2646 then 0 else (if x<2710 then 0 else 2)))) else (if x<3158 then (if x<2786 then (if x<2740 then 2 else 1) else (if x<3102 then 1 else 0)) else (if x<3188 then (if x<3178 then 2 else 1) else (if x<3252 then 0 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers641 : Finset ℕ := ([1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2620,2638,2646,2674,2710,2730,2740,2776,2786,2788,3102,3130,3158,3178,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers641 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers641 1740 5
  · have he : independentCachedBranchMembers641.erase 1740=independentCachedBranchMembers639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound639
  · have he : independentCachedBranchMembers641.filter (independentCachedEdge 1740)=independentCachedBranchMembers640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound640
def independentCachedBranchMembers642 : Finset ℕ := ([1590,1626,1628,1720,1746,1748,1768,2638,2674,2710,2730,3130,3158,3178,3214,3250,3252,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers642 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers642 5 (fun x => (if x<2710 then (if x<1746 then (if x<1628 then (if x<1626 then 0 else 0) else (if x<1720 then 1 else 0)) else (if x<1768 then (if x<1748 then 1 else 0) else (if x<2638 then 1 else (if x<2674 then 2 else 2)))) else (if x<3214 then (if x<3130 then (if x<2730 then 2 else 2) else (if x<3158 then 0 else (if x<3178 then 0 else 2))) else (if x<3252 then (if x<3250 then 2 else 2) else (if x<3288 then 0 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers643 : Finset ℕ := ([1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2620,2638,2646,2674,2702,2710,2730,2740,2776,2786,2788,3102,3130,3158,3178,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers643 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers643 2702 5
  · have he : independentCachedBranchMembers643.erase 2702=independentCachedBranchMembers641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound641
  · have he : independentCachedBranchMembers643.filter (independentCachedEdge 2702)=independentCachedBranchMembers642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound642
def independentCachedBranchMembers644 : Finset ℕ := ([1628,1692,1702,1738,1746,1768,1776,2620,2674,2730,2788,3130,3158,3188,3214,3244,3252,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers644 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers644 5 (fun x => (if x<2730 then (if x<1746 then (if x<1702 then (if x<1692 then 0 else 1) else (if x<1738 then 1 else 0)) else (if x<1776 then (if x<1768 then 1 else 1) else (if x<2620 then 0 else (if x<2674 then 2 else 2)))) else (if x<3214 then (if x<3130 then (if x<2788 then 2 else 2) else (if x<3158 then 2 else (if x<3188 then 3 else 0))) else (if x<3252 then (if x<3244 then 3 else 1) else (if x<3288 then 3 else (if x<3298 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers645 : Finset ℕ := ([1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2740,2776,2786,2788,3102,3130,3158,3178,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers645 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers645 2618 5
  · have he : independentCachedBranchMembers645.erase 2618=independentCachedBranchMembers643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound643
  · have he : independentCachedBranchMembers645.filter (independentCachedEdge 2618)=independentCachedBranchMembers644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound644
def independentCachedBranchMembers646 : Finset ℕ := ([1590,1628,1720,1738,1746,1768,1776,2620,2638,2646,2730,2776,2786,3102,3158,3188,3250,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers646 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers646 5 (fun x => (if x<2646 then (if x<1746 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<1738 then 0 else 1)) else (if x<1776 then (if x<1768 then 0 else 2) else (if x<2620 then 1 else (if x<2638 then 0 else 1)))) else (if x<3158 then (if x<2776 then (if x<2730 then 0 else 2) else (if x<2786 then 0 else (if x<3102 then 1 else 3))) else (if x<3250 then (if x<3188 then 2 else 3) else (if x<3288 then 3 else (if x<3298 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers647 : Finset ℕ := ([132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2740,2776,2786,2788,3102,3130,3158,3178,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers647 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers647 132 5
  · have he : independentCachedBranchMembers647.erase 132=independentCachedBranchMembers645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound645
  · have he : independentCachedBranchMembers647.filter (independentCachedEdge 132)=independentCachedBranchMembers646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound646
def independentCachedBranchMembers648 : Finset ℕ := ([1626,1628,1692,1702,1746,1748,1768,2646,2710,2730,2776,2786,2788,3102,3158,3178,3244,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers648 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers648 5 (fun x => (if x<2730 then (if x<1746 then (if x<1692 then (if x<1628 then 0 else 1) else (if x<1702 then 0 else 2)) else (if x<1768 then (if x<1748 then 1 else 2) else (if x<2646 then 0 else (if x<2710 then 1 else 2)))) else (if x<3158 then (if x<2786 then (if x<2776 then 2 else 0) else (if x<2788 then 1 else (if x<3102 then 2 else 3))) else (if x<3244 then (if x<3178 then 4 else 3) else (if x<3288 then 3 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers649 : Finset ℕ := ([48,132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2740,2776,2786,2788,3102,3130,3158,3178,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers649 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers649 48 5
  · have he : independentCachedBranchMembers649.erase 48=independentCachedBranchMembers647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound647
  · have he : independentCachedBranchMembers649.filter (independentCachedEdge 48)=independentCachedBranchMembers648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound648
def independentCachedBranchMembers650 : Finset ℕ := ([1628,1702,1720,1738,1748,1768,2620,2638,2674,2710,2730,2740,2776,2788,3130,3158,3178,3188,3214,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers650 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers650 5 (fun x => (if x<2740 then (if x<1768 then (if x<1720 then (if x<1702 then 0 else 1) else (if x<1738 then 0 else (if x<1748 then 0 else 1))) else (if x<2674 then (if x<2620 then 1 else (if x<2638 then 0 else 0)) else (if x<2710 then 2 else (if x<2730 then 1 else 0)))) else (if x<3178 then (if x<2788 then (if x<2776 then 2 else 0) else (if x<3130 then 1 else (if x<3158 then 3 else 3))) else (if x<3244 then (if x<3188 then 2 else (if x<3214 then 2 else 3)) else (if x<3250 then 2 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers651 : Finset ℕ := ([48,132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2740,2776,2786,2788,3102,3130,3158,3178,3186,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers651 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers651 3186 5
  · have he : independentCachedBranchMembers651.erase 3186=independentCachedBranchMembers649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound649
  · have he : independentCachedBranchMembers651.filter (independentCachedEdge 3186)=independentCachedBranchMembers650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound650
def independentCachedBranchMembers652 : Finset ℕ := ([48,132,1590,1626,1692,1702,1720,1738,1748,1776,2618,2646,2674,2702,2730,2740,2776,2786,3178,3188,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers652 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers652 5 (fun x => (if x<2646 then (if x<1702 then (if x<1590 then (if x<132 then 0 else 0) else (if x<1626 then 1 else (if x<1692 then 1 else 1))) else (if x<1748 then (if x<1720 then 2 else (if x<1738 then 2 else 2)) else (if x<1776 then 2 else (if x<2618 then 1 else 0)))) else (if x<2776 then (if x<2702 then (if x<2674 then 3 else 1) else (if x<2730 then 0 else (if x<2740 then 2 else 0))) else (if x<3188 then (if x<2786 then 1 else (if x<3178 then 3 else 4)) else (if x<3244 then 4 else (if x<3250 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers653 : Finset ℕ := ([48,132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2740,2776,2786,2788,3102,3130,3158,3178,3180,3186,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers653 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers653 3180 5
  · have he : independentCachedBranchMembers653.erase 3180=independentCachedBranchMembers651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound651
  · have he : independentCachedBranchMembers653.filter (independentCachedEdge 3180)=independentCachedBranchMembers652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound652
def independentCachedBranchMembers654 : Finset ℕ := ([132,1626,1692,1738,1748,1768,2618,2638,2674,2710,2730,2740,2786,3102,3158,3178,3188,3214,3244,3250,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers654 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers654 5 (fun x => (if x<2740 then (if x<1768 then (if x<1692 then (if x<1626 then 0 else 0) else (if x<1738 then 0 else (if x<1748 then 1 else 1))) else (if x<2674 then (if x<2618 then 2 else (if x<2638 then 3 else 3)) else (if x<2710 then 0 else (if x<2730 then 2 else 1)))) else (if x<3188 then (if x<3102 then (if x<2786 then 0 else 2) else (if x<3158 then 2 else (if x<3178 then 4 else 0))) else (if x<3250 then (if x<3214 then 1 else (if x<3244 then 4 else 0)) else (if x<3270 then 3 else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers655 : Finset ℕ := ([48,132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2738,2740,2776,2786,2788,3102,3130,3158,3178,3180,3186,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers655 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers655 2738 5
  · have he : independentCachedBranchMembers655.erase 2738=independentCachedBranchMembers653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound653
  · have he : independentCachedBranchMembers655.filter (independentCachedEdge 2738)=independentCachedBranchMembers654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound654
def independentCachedBranchMembers656 : Finset ℕ := ([1590,1628,1738,1748,1776,2620,2646,2674,2702,2730,2740,2788,3102,3130,3178,3188,3244,3250,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers656 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers656 5 (fun x => (if x<2740 then (if x<2620 then (if x<1738 then (if x<1628 then 0 else 0) else (if x<1748 then 1 else (if x<1776 then 1 else 0))) else (if x<2674 then (if x<2646 then 2 else 2) else (if x<2702 then 3 else (if x<2730 then 2 else 1)))) else (if x<3188 then (if x<3102 then (if x<2788 then 1 else 2) else (if x<3130 then 0 else (if x<3178 then 3 else 1))) else (if x<3270 then (if x<3244 then 0 else (if x<3250 then 2 else 0)) else (if x<3288 then 2 else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers657 : Finset ℕ := ([1628,1748,2646,2730,2788,3102,3178,3244,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers657 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers657 4 (fun x => (if x<3102 then (if x<2646 then (if x<1748 then 0 else 1) else (if x<2730 then 0 else (if x<2788 then 1 else 1))) else (if x<3244 then (if x<3178 then 0 else 2) else (if x<3288 then 2 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers658 : Finset ℕ := ([48,1590,1628,1738,1748,1776,2620,2646,2674,2702,2730,2740,2788,3102,3130,3178,3188,3244,3250,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers658 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers658 48 4
  · have he : independentCachedBranchMembers658.erase 48=independentCachedBranchMembers656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound656
  · have he : independentCachedBranchMembers658.filter (independentCachedEdge 48)=independentCachedBranchMembers657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound657
def independentCachedBranchMembers659 : Finset ℕ := ([48,132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2732,2738,2740,2776,2786,2788,3102,3130,3158,3178,3180,3186,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers659 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers659 2732 5
  · have he : independentCachedBranchMembers659.erase 2732=independentCachedBranchMembers655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound655
  · have he : independentCachedBranchMembers659.filter (independentCachedEdge 2732)=independentCachedBranchMembers658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound658
def independentCachedBranchMembers660 : Finset ℕ := ([1590,1626,1628,1692,1768,1776,2618,2620,2638,2646,2702,2710,2786,2788,3102,3178,3180,3186,3188,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers660 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers660 5 (fun x => (if x<2786 then (if x<2618 then (if x<1692 then (if x<1626 then 0 else (if x<1628 then 0 else 1)) else (if x<1768 then 0 else (if x<1776 then 1 else 0))) else (if x<2646 then (if x<2620 then 2 else (if x<2638 then 3 else 2)) else (if x<2702 then 1 else (if x<2710 then 3 else 2)))) else (if x<3188 then (if x<3178 then (if x<2788 then 1 else (if x<3102 then 3 else 0)) else (if x<3180 then 2 else (if x<3186 then 4 else 0))) else (if x<3252 then (if x<3244 then 3 else (if x<3250 then 3 else 2)) else (if x<3270 then 0 else (if x<3288 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers661 : Finset ℕ := ([48,132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3102,3130,3158,3178,3180,3186,3188,3214,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers661 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers661 2758 5
  · have he : independentCachedBranchMembers661.erase 2758=independentCachedBranchMembers659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound659
  · have he : independentCachedBranchMembers661.filter (independentCachedEdge 2758)=independentCachedBranchMembers660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound660
def independentCachedBranchMembers662 : Finset ℕ := ([48,1590,1628,1692,1720,1738,1746,2620,2638,2646,2674,2702,2710,2730,2738,2776,2788,3102,3130,3180,3188,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers662 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers662 5 (fun x => (if x<2710 then (if x<1746 then (if x<1692 then (if x<1590 then 0 else (if x<1628 then 0 else 1)) else (if x<1720 then 2 else (if x<1738 then 0 else 1))) else (if x<2646 then (if x<2620 then 2 else (if x<2638 then 0 else 1)) else (if x<2674 then 3 else (if x<2702 then 2 else 3)))) else (if x<3130 then (if x<2776 then (if x<2730 then 2 else (if x<2738 then 1 else 0)) else (if x<2788 then 1 else (if x<3102 then 3 else 3))) else (if x<3244 then (if x<3180 then 0 else (if x<3188 then 4 else 3)) else (if x<3270 then (if x<3252 then 3 else 0) else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers663 : Finset ℕ := ([48,132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3102,3130,3158,3178,3180,3186,3188,3214,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers663 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers663 3300 5
  · have he : independentCachedBranchMembers663.erase 3300=independentCachedBranchMembers661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound661
  · have he : independentCachedBranchMembers663.filter (independentCachedEdge 3300)=independentCachedBranchMembers662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound662
def independentCachedBranchMembers664 : Finset ℕ := ([132,1590,1692,1702,1746,1748,1768,2618,2620,2638,2674,2710,2730,2732,2776,2786,2788,3102,3158,3178,3180,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers664 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers664 5 (fun x => (if x<2730 then (if x<1768 then (if x<1702 then (if x<1590 then 0 else (if x<1692 then 1 else 0)) else (if x<1746 then 0 else (if x<1748 then 1 else 2))) else (if x<2638 then (if x<2618 then 2 else (if x<2620 then 3 else 1)) else (if x<2674 then 3 else (if x<2710 then 1 else 0)))) else (if x<3158 then (if x<2786 then (if x<2732 then 2 else (if x<2776 then 0 else 1)) else (if x<2788 then 3 else (if x<3102 then 2 else 3))) else (if x<3214 then (if x<3178 then 4 else (if x<3180 then 3 else 4)) else (if x<3252 then (if x<3250 then 0 else 3) else (if x<3270 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers665 : Finset ℕ := ([48,132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2674,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3102,3130,3150,3158,3178,3180,3186,3188,3214,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers665 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers665 3150 5
  · have he : independentCachedBranchMembers665.erase 3150=independentCachedBranchMembers663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound663
  · have he : independentCachedBranchMembers665.filter (independentCachedEdge 3150)=independentCachedBranchMembers664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound664
def independentCachedBranchMembers666 : Finset ℕ := ([132,1590,1626,1692,1702,1720,1738,1748,1776,2620,2638,2710,2732,2738,2788,3102,3130,3158,3180,3186,3214,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers666 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers666 5 (fun x => (if x<2732 then (if x<1738 then (if x<1692 then (if x<1590 then 0 else (if x<1626 then 1 else 0)) else (if x<1702 then 0 else (if x<1720 then 2 else 1))) else (if x<2620 then (if x<1748 then 2 else (if x<1776 then 1 else 2)) else (if x<2638 then 3 else (if x<2710 then 3 else 3)))) else (if x<3180 then (if x<3102 then (if x<2738 then 0 else (if x<2788 then 4 else 3)) else (if x<3130 then 3 else (if x<3158 then 1 else 1))) else (if x<3252 then (if x<3186 then 3 else (if x<3214 then 0 else 2)) else (if x<3288 then (if x<3270 then 0 else 3) else (if x<3298 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers667 : Finset ℕ := ([1626,1692,1702,1748,2710,2732,2788,3102,3158,3180,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers667 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers667 4 (fun x => (if x<2788 then (if x<1748 then (if x<1692 then 0 else (if x<1702 then 0 else 1)) else (if x<2710 then 1 else (if x<2732 then 1 else 0))) else (if x<3180 then (if x<3102 then 1 else (if x<3158 then 2 else 3)) else (if x<3288 then 2 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers668 : Finset ℕ := ([48,132,1590,1626,1692,1702,1720,1738,1748,1776,2620,2638,2710,2732,2738,2788,3102,3130,3158,3180,3186,3214,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers668 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers668 48 4
  · have he : independentCachedBranchMembers668.erase 48=independentCachedBranchMembers666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound666
  · have he : independentCachedBranchMembers668.filter (independentCachedEdge 48)=independentCachedBranchMembers667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound667
def independentCachedBranchMembers669 : Finset ℕ := ([48,132,1590,1626,1628,1692,1702,1720,1738,1740,1746,1748,1768,1776,2618,2620,2638,2646,2668,2674,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3102,3130,3150,3158,3178,3180,3186,3188,3214,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers669 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers669 2668 5
  · have he : independentCachedBranchMembers669.erase 2668=independentCachedBranchMembers665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound665
  · have he : independentCachedBranchMembers669.filter (independentCachedEdge 2668)=independentCachedBranchMembers668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound668
def independentCachedBranchMembers670 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1708,1714,1720,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers670 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers670 1752 6
  · have he : independentCachedBranchMembers670.erase 1752=independentCachedBranchMembers638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound638
  · have he : independentCachedBranchMembers670.filter (independentCachedEdge 1752)=independentCachedBranchMembers669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound669
def independentCachedBranchMembers671 : Finset ℕ := ([1596,1614,1678,1686,1702,1720,1738,1746,1748,1764,2614,2650,2668,2716,2730,2758,2800,3102,3118,3178,3188,3226,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers671 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers671 6 (fun x => (if x<2716 then (if x<1738 then (if x<1686 then (if x<1614 then 0 else (if x<1678 then 0 else 1)) else (if x<1702 then 0 else (if x<1720 then 2 else 1))) else (if x<1764 then (if x<1746 then 2 else (if x<1748 then 1 else 2)) else (if x<2650 then (if x<2614 then 0 else 3) else (if x<2668 then 3 else 0)))) else (if x<3188 then (if x<2800 then (if x<2730 then 3 else (if x<2758 then 2 else 0)) else (if x<3118 then (if x<3102 then 1 else 3) else (if x<3178 then 4 else 5))) else (if x<3250 then (if x<3226 then 4 else (if x<3244 then 5 else 5)) else (if x<3270 then (if x<3252 then 4 else 3) else (if x<3288 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers672 : Finset ℕ := ([1596,1720,1748,1764,2668,2716,2800,3188,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers672 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers672 5 (fun x => (if x<2716 then (if x<1748 then (if x<1720 then 0 else 1) else (if x<1764 then 0 else (if x<2668 then 1 else 2))) else (if x<3244 then (if x<2800 then 0 else (if x<3188 then 1 else 2)) else (if x<3252 then 2 else (if x<3288 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers673 : Finset ℕ := ([1594,1596,1614,1678,1686,1702,1720,1738,1746,1748,1764,2614,2650,2668,2716,2730,2758,2800,3102,3118,3178,3188,3226,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers673 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers673 1594 5
  · have he : independentCachedBranchMembers673.erase 1594=independentCachedBranchMembers671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound671
  · have he : independentCachedBranchMembers673.filter (independentCachedEdge 1594)=independentCachedBranchMembers672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound672
def independentCachedBranchMembers674 : Finset ℕ := ([1594,1678,1746,2614,2650,2716,2800,3102,3118,3226,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers674 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers674 5 (fun x => (if x<2800 then (if x<2614 then (if x<1678 then 0 else (if x<1746 then 0 else 0)) else (if x<2650 then 1 else (if x<2716 then 1 else 1))) else (if x<3226 then (if x<3102 then 1 else (if x<3118 then 1 else 0)) else (if x<3270 then (if x<3252 then 0 else 1) else (if x<3288 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers675 : Finset ℕ := ([1594,1596,1614,1678,1686,1702,1720,1738,1746,1748,1764,2614,2650,2668,2716,2730,2740,2758,2800,3102,3118,3178,3188,3226,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers675 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers675 2740 5
  · have he : independentCachedBranchMembers675.erase 2740=independentCachedBranchMembers673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound673
  · have he : independentCachedBranchMembers675.filter (independentCachedEdge 2740)=independentCachedBranchMembers674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound674
def independentCachedBranchMembers676 : Finset ℕ := ([1596,1614,1702,1748,2650,2668,2716,2730,3118,3178,3226,3244,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers676 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers676 5 (fun x => (if x<2730 then (if x<1748 then (if x<1614 then 0 else (if x<1702 then 0 else 0)) else (if x<2668 then (if x<2650 then 0 else 1) else (if x<2716 then 1 else 1))) else (if x<3226 then (if x<3118 then 1 else (if x<3178 then 0 else 1)) else (if x<3252 then (if x<3244 then 1 else 1) else (if x<3270 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers677 : Finset ℕ := ([1594,1596,1614,1678,1686,1702,1720,1738,1746,1748,1764,2614,2650,2668,2714,2716,2730,2740,2758,2800,3102,3118,3178,3188,3226,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers677 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers677 2714 5
  · have he : independentCachedBranchMembers677.erase 2714=independentCachedBranchMembers675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound675
  · have he : independentCachedBranchMembers677.filter (independentCachedEdge 2714)=independentCachedBranchMembers676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound676
def independentCachedBranchMembers678 : Finset ℕ := ([1686,1720,1738,1764,2614,2668,2730,2800,3118,3188,3226,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers678 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers678 5 (fun x => (if x<2800 then (if x<1764 then (if x<1720 then 0 else (if x<1738 then 0 else 0)) else (if x<2668 then (if x<2614 then 0 else 1) else (if x<2730 then 1 else 1))) else (if x<3226 then (if x<3118 then 1 else (if x<3188 then 1 else 1)) else (if x<3252 then (if x<3250 then 0 else 1) else (if x<3270 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers679 : Finset ℕ := ([1594,1596,1614,1678,1686,1702,1720,1738,1746,1748,1764,2606,2614,2650,2668,2714,2716,2730,2740,2758,2800,3102,3118,3178,3188,3226,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers679 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers679 2606 5
  · have he : independentCachedBranchMembers679.erase 2606=independentCachedBranchMembers677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound677
  · have he : independentCachedBranchMembers679.filter (independentCachedEdge 2606)=independentCachedBranchMembers678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound678
def independentCachedBranchMembers680 : Finset ℕ := ([1594,1596,1614,1678,1702,1746,1748,2606,2650,2714,2716,2740,2758,3102,3178,3244,3288] : List ℕ).toFinset
theorem independentCachedBranchBound680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers680 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers680 5 (fun x => (if x<2650 then (if x<1702 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<1748 then (if x<1746 then 0 else 0) else (if x<2606 then 1 else 0))) else (if x<2758 then (if x<2716 then (if x<2714 then 0 else 2) else (if x<2740 then 1 else 2)) else (if x<3178 then (if x<3102 then 0 else 3) else (if x<3244 then 3 else (if x<3288 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers681 : Finset ℕ := ([1594,1596,1614,1678,1686,1702,1720,1738,1746,1748,1764,2606,2614,2650,2668,2714,2716,2730,2740,2758,2800,3102,3118,3178,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers681 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers681 3304 5
  · have he : independentCachedBranchMembers681.erase 3304=independentCachedBranchMembers679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound679
  · have he : independentCachedBranchMembers681.filter (independentCachedEdge 3304)=independentCachedBranchMembers680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound680
def independentCachedBranchMembers682 : Finset ℕ := ([1594,1678,1686,1720,1738,1746,1764,2606,2614,2714,2740,2758,2800,3102,3188,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers682 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers682 5 (fun x => (if x<2614 then (if x<1738 then (if x<1686 then (if x<1678 then 0 else 0) else (if x<1720 then 1 else 1)) else (if x<1764 then (if x<1746 then 1 else 0) else (if x<2606 then 1 else 0))) else (if x<2800 then (if x<2740 then (if x<2714 then 2 else 0) else (if x<2758 then 1 else 0)) else (if x<3188 then (if x<3102 then 2 else 2) else (if x<3250 then 2 else (if x<3288 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers683 : Finset ℕ := ([1594,1596,1614,1678,1686,1702,1720,1738,1746,1748,1764,2606,2614,2650,2668,2714,2716,2730,2740,2758,2800,3102,3118,3164,3178,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers683 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers683 3164 5
  · have he : independentCachedBranchMembers683.erase 3164=independentCachedBranchMembers681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound681
  · have he : independentCachedBranchMembers683.filter (independentCachedEdge 3164)=independentCachedBranchMembers682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound682
def independentCachedBranchMembers684 : Finset ℕ := ([1594,1614,1678,1738,1748,1764,2606,2650,2714,2730,2740,2800,3102,3118,3178,3188,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers684 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers684 5 (fun x => (if x<2730 then (if x<1748 then (if x<1678 then (if x<1614 then 0 else 0) else (if x<1738 then 1 else 2)) else (if x<2606 then (if x<1764 then 1 else 2) else (if x<2650 then 0 else (if x<2714 then 0 else 2)))) else (if x<3118 then (if x<2800 then (if x<2740 then 1 else 2) else (if x<3102 then 1 else 0)) else (if x<3188 then (if x<3178 then 1 else 0) else (if x<3226 then 1 else (if x<3252 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers685 : Finset ℕ := ([1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2668,2714,2716,2730,2740,2758,2800,3102,3118,3164,3178,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers685 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers685 1740 5
  · have he : independentCachedBranchMembers685.erase 1740=independentCachedBranchMembers683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound683
  · have he : independentCachedBranchMembers685.filter (independentCachedEdge 1740)=independentCachedBranchMembers684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound684
def independentCachedBranchMembers686 : Finset ℕ := ([1594,1596,1614,1678,1702,1746,1748,2614,2668,2730,2800,3118,3164,3188,3226,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers686 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers686 5 (fun x => (if x<2730 then (if x<1702 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<1748 then (if x<1746 then 0 else 0) else (if x<2614 then 1 else (if x<2668 then 2 else 2)))) else (if x<3226 then (if x<3118 then (if x<2800 then 2 else 2) else (if x<3164 then 0 else (if x<3188 then 3 else 1))) else (if x<3252 then (if x<3250 then 3 else 0) else (if x<3270 then 3 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers687 : Finset ℕ := ([1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2668,2714,2716,2730,2740,2758,2792,2800,3102,3118,3164,3178,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers687 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers687 2792 5
  · have he : independentCachedBranchMembers687.erase 2792=independentCachedBranchMembers685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound685
  · have he : independentCachedBranchMembers687.filter (independentCachedEdge 2792)=independentCachedBranchMembers686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound686
def independentCachedBranchMembers688 : Finset ℕ := ([1594,1678,1686,1720,1738,1746,1764,2650,2668,2716,2730,3118,3164,3178,3226,3244,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers688 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers688 5 (fun x => (if x<2716 then (if x<1738 then (if x<1686 then (if x<1678 then 0 else 0) else (if x<1720 then 1 else 1)) else (if x<1764 then (if x<1746 then 1 else 0) else (if x<2650 then 1 else (if x<2668 then 2 else 2)))) else (if x<3226 then (if x<3118 then (if x<2730 then 2 else 2) else (if x<3164 then 0 else (if x<3178 then 2 else 2))) else (if x<3252 then (if x<3244 then 0 else 2) else (if x<3270 then 1 else (if x<3304 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers689 : Finset ℕ := ([1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2740,2758,2792,2800,3102,3118,3164,3178,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers689 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers689 2652 5
  · have he : independentCachedBranchMembers689.erase 2652=independentCachedBranchMembers687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound687
  · have he : independentCachedBranchMembers689.filter (independentCachedEdge 2652)=independentCachedBranchMembers688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound688
def independentCachedBranchMembers690 : Finset ℕ := ([1594,1614,1678,1686,1702,1738,1746,2606,2614,2650,2714,2730,2758,3102,3118,3178,3226,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers690 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers690 5 (fun x => (if x<2650 then (if x<1702 then (if x<1678 then (if x<1614 then 0 else 0) else (if x<1686 then 1 else 0)) else (if x<1746 then (if x<1738 then 2 else 2) else (if x<2606 then 1 else (if x<2614 then 1 else 2)))) else (if x<3118 then (if x<2730 then (if x<2714 then 2 else 1) else (if x<2758 then 2 else (if x<3102 then 0 else 3))) else (if x<3226 then (if x<3178 then 4 else 3) else (if x<3250 then 4 else (if x<3270 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers691 : Finset ℕ := ([252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2740,2758,2792,2800,3102,3118,3164,3178,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers691 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers691 252 5
  · have he : independentCachedBranchMembers691.erase 252=independentCachedBranchMembers689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound689
  · have he : independentCachedBranchMembers691.filter (independentCachedEdge 252)=independentCachedBranchMembers690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound690
def independentCachedBranchMembers692 : Finset ℕ := ([1596,1678,1720,1746,1748,1764,2606,2714,2716,2730,2758,2800,3102,3118,3188,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers692 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers692 5 (fun x => (if x<2730 then (if x<1748 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2606 then (if x<1764 then 0 else 1) else (if x<2714 then 0 else (if x<2716 then 1 else 0)))) else (if x<3118 then (if x<2800 then (if x<2758 then 2 else 0) else (if x<3102 then 1 else 3)) else (if x<3226 then (if x<3188 then 2 else 2) else (if x<3244 then 4 else (if x<3270 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers693 : Finset ℕ := ([1596,1720,1748,1764,2716,2800,3188,3244] : List ℕ).toFinset
theorem independentCachedBranchBound693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers693 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers693 4 (fun x => (if x<2716 then (if x<1748 then (if x<1720 then 0 else 1) else (if x<1764 then 0 else 1)) else (if x<3188 then (if x<2800 then 0 else 1) else (if x<3244 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers694 : Finset ℕ := ([1594,1596,1678,1720,1746,1748,1764,2606,2714,2716,2730,2758,2800,3102,3118,3188,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers694 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers694 1594 4
  · have he : independentCachedBranchMembers694.erase 1594=independentCachedBranchMembers692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound692
  · have he : independentCachedBranchMembers694.filter (independentCachedEdge 1594)=independentCachedBranchMembers693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound693
def independentCachedBranchMembers695 : Finset ℕ := ([72,252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2740,2758,2792,2800,3102,3118,3164,3178,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers695 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers695 72 5
  · have he : independentCachedBranchMembers695.erase 72=independentCachedBranchMembers691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound691
  · have he : independentCachedBranchMembers695.filter (independentCachedEdge 72)=independentCachedBranchMembers694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound694
def independentCachedBranchMembers696 : Finset ℕ := ([72,252,1596,1614,1686,1702,1720,1738,1748,1764,2606,2652,2668,2714,2730,2740,2758,2792,3178,3188,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers696 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers696 5 (fun x => (if x<2652 then (if x<1702 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1614 then 1 else (if x<1686 then 1 else 1))) else (if x<1748 then (if x<1720 then 2 else (if x<1738 then 2 else 2)) else (if x<1764 then 2 else (if x<2606 then 1 else 3)))) else (if x<2758 then (if x<2714 then (if x<2668 then 0 else 1) else (if x<2730 then 3 else (if x<2740 then 2 else 0))) else (if x<3188 then (if x<2792 then 1 else (if x<3178 then 0 else 4)) else (if x<3244 then 4 else (if x<3250 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers697 : Finset ℕ := ([72,252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2740,2758,2792,2800,3102,3118,3164,3178,3186,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers697 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers697 3186 5
  · have he : independentCachedBranchMembers697.erase 3186=independentCachedBranchMembers695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound695
  · have he : independentCachedBranchMembers697.filter (independentCachedEdge 3186)=independentCachedBranchMembers696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound696
def independentCachedBranchMembers698 : Finset ℕ := ([1594,1678,1702,1720,1738,1748,2614,2650,2668,2716,2730,2740,2758,2800,3118,3164,3178,3188,3226,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers698 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers698 5 (fun x => (if x<2740 then (if x<1748 then (if x<1702 then (if x<1678 then 0 else 0) else (if x<1720 then 1 else (if x<1738 then 1 else 1))) else (if x<2668 then (if x<2614 then 1 else (if x<2650 then 2 else 2)) else (if x<2716 then 2 else (if x<2730 then 2 else 0)))) else (if x<3178 then (if x<2800 then (if x<2758 then 1 else 0) else (if x<3118 then 2 else (if x<3164 then 3 else 3))) else (if x<3244 then (if x<3188 then 4 else (if x<3226 then 4 else 3)) else (if x<3250 then 4 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers699 : Finset ℕ := ([72,252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2740,2758,2792,2800,3102,3118,3164,3178,3180,3186,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers699 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers699 3180 5
  · have he : independentCachedBranchMembers699.erase 3180=independentCachedBranchMembers697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound697
  · have he : independentCachedBranchMembers699.filter (independentCachedEdge 3180)=independentCachedBranchMembers698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound698
def independentCachedBranchMembers700 : Finset ℕ := ([252,1596,1678,1738,1748,1764,2614,2652,2668,2714,2730,2740,2800,3102,3118,3178,3188,3244,3250,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers700 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers700 5 (fun x => (if x<2740 then (if x<1764 then (if x<1678 then (if x<1596 then 0 else 0) else (if x<1738 then 1 else (if x<1748 then 2 else 0))) else (if x<2668 then (if x<2614 then 1 else (if x<2652 then 2 else 0)) else (if x<2714 then 3 else (if x<2730 then 1 else 2)))) else (if x<3188 then (if x<3102 then (if x<2800 then 0 else 1) else (if x<3118 then 1 else (if x<3178 then 3 else 4))) else (if x<3270 then (if x<3244 then 0 else (if x<3250 then 4 else 3)) else (if x<3288 then 4 else (if x<3304 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers701 : Finset ℕ := ([72,252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2738,2740,2758,2792,2800,3102,3118,3164,3178,3180,3186,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers701 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers701 2738 5
  · have he : independentCachedBranchMembers701.erase 2738=independentCachedBranchMembers699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound699
  · have he : independentCachedBranchMembers701.filter (independentCachedEdge 2738)=independentCachedBranchMembers700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound700
def independentCachedBranchMembers702 : Finset ℕ := ([1594,1614,1686,1738,1748,2606,2650,2668,2716,2730,2740,2792,3102,3164,3178,3188,3226,3244,3250,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers702 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers702 5 (fun x => (if x<2740 then (if x<2606 then (if x<1686 then (if x<1614 then 0 else 0) else (if x<1738 then 0 else (if x<1748 then 1 else 1))) else (if x<2668 then (if x<2650 then 2 else 2) else (if x<2716 then 3 else (if x<2730 then 2 else 1)))) else (if x<3188 then (if x<3102 then (if x<2792 then 1 else 2) else (if x<3164 then 0 else (if x<3178 then 3 else 0))) else (if x<3250 then (if x<3226 then 1 else (if x<3244 then 3 else 2)) else (if x<3270 then 0 else (if x<3288 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers703 : Finset ℕ := ([1594,1748,2606,2716,2730,3102,3188,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers703 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers703 4 (fun x => (if x<3102 then (if x<2606 then (if x<1748 then 0 else 1) else (if x<2716 then 0 else (if x<2730 then 1 else 1))) else (if x<3226 then (if x<3188 then 0 else 2) else (if x<3244 then 3 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers704 : Finset ℕ := ([72,1594,1614,1686,1738,1748,2606,2650,2668,2716,2730,2740,2792,3102,3164,3178,3188,3226,3244,3250,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers704 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers704 72 4
  · have he : independentCachedBranchMembers704.erase 72=independentCachedBranchMembers702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound702
  · have he : independentCachedBranchMembers704.filter (independentCachedEdge 72)=independentCachedBranchMembers703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound703
def independentCachedBranchMembers705 : Finset ℕ := ([72,252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2732,2738,2740,2758,2792,2800,3102,3118,3164,3178,3180,3186,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers705 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers705 2732 5
  · have he : independentCachedBranchMembers705.erase 2732=independentCachedBranchMembers701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound701
  · have he : independentCachedBranchMembers705.filter (independentCachedEdge 2732)=independentCachedBranchMembers704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound704
def independentCachedBranchMembers706 : Finset ℕ := ([1594,1596,1614,1678,1686,1764,2606,2614,2650,2652,2714,2716,2792,2800,3102,3178,3180,3186,3188,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers706 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers706 5 (fun x => (if x<2792 then (if x<2606 then (if x<1678 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1686 then 1 else (if x<1764 then 0 else 1))) else (if x<2652 then (if x<2614 then 2 else (if x<2650 then 3 else 2)) else (if x<2714 then 3 else (if x<2716 then 3 else 2)))) else (if x<3188 then (if x<3178 then (if x<2800 then 2 else (if x<3102 then 3 else 0)) else (if x<3180 then 0 else (if x<3186 then 4 else 4))) else (if x<3252 then (if x<3244 then 1 else (if x<3250 then 1 else 0)) else (if x<3270 then 4 else (if x<3288 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers707 : Finset ℕ := ([72,252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3102,3118,3164,3178,3180,3186,3188,3226,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers707 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers707 2776 5
  · have he : independentCachedBranchMembers707.erase 2776=independentCachedBranchMembers705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound705
  · have he : independentCachedBranchMembers707.filter (independentCachedEdge 2776)=independentCachedBranchMembers706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound706
def independentCachedBranchMembers708 : Finset ℕ := ([72,1594,1614,1702,1738,1746,1764,2606,2614,2650,2668,2716,2730,2738,2758,2792,2800,3102,3164,3178,3186,3226,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers708 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers708 5 (fun x => (if x<2730 then (if x<1764 then (if x<1702 then (if x<1594 then 0 else (if x<1614 then 1 else 0)) else (if x<1738 then 0 else (if x<1746 then 1 else 2))) else (if x<2650 then (if x<2606 then 2 else (if x<2614 then 3 else 1)) else (if x<2668 then 0 else (if x<2716 then 2 else 3)))) else (if x<3164 then (if x<2792 then (if x<2738 then 1 else (if x<2758 then 0 else 1)) else (if x<2800 then 3 else (if x<3102 then 2 else 3))) else (if x<3226 then (if x<3178 then 0 else (if x<3186 then 3 else 4)) else (if x<3252 then (if x<3244 then 4 else 3) else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers709 : Finset ℕ := ([72,252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3102,3118,3164,3178,3180,3186,3188,3226,3228,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers709 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers709 3228 5
  · have he : independentCachedBranchMembers709.erase 3228=independentCachedBranchMembers707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound707
  · have he : independentCachedBranchMembers709.filter (independentCachedEdge 3228)=independentCachedBranchMembers708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound708
def independentCachedBranchMembers710 : Finset ℕ := ([1614,1678,1720,1746,1748,1764,2614,2650,2652,2668,2714,2716,2730,2732,2758,2800,3102,3118,3186,3188,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers710 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers710 5 (fun x => (if x<2730 then (if x<2614 then (if x<1746 then (if x<1678 then 0 else (if x<1720 then 1 else 1)) else (if x<1748 then 0 else (if x<1764 then 1 else 0))) else (if x<2668 then (if x<2650 then 2 else (if x<2652 then 0 else 2)) else (if x<2714 then 0 else (if x<2716 then 2 else 1)))) else (if x<3186 then (if x<2800 then (if x<2732 then 1 else (if x<2758 then 2 else 0)) else (if x<3102 then 0 else (if x<3118 then 3 else 4))) else (if x<3252 then (if x<3188 then 3 else (if x<3250 then 4 else 4)) else (if x<3288 then 3 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers711 : Finset ℕ := ([1614,1678,1746,2614,2650,2714,2730,2758,3102,3118,3186,3250] : List ℕ).toFinset
theorem independentCachedBranchBound711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers711 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers711 4 (fun x => (if x<2730 then (if x<2614 then (if x<1678 then 0 else (if x<1746 then 1 else 0)) else (if x<2650 then 2 else (if x<2714 then 0 else 1))) else (if x<3118 then (if x<2758 then 2 else (if x<3102 then 0 else 1)) else (if x<3186 then 2 else (if x<3250 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers712 : Finset ℕ := ([252,1614,1678,1720,1746,1748,1764,2614,2650,2652,2668,2714,2716,2730,2732,2758,2800,3102,3118,3186,3188,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers712 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers712 252 4
  · have he : independentCachedBranchMembers712.erase 252=independentCachedBranchMembers710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound710
  · have he : independentCachedBranchMembers712.filter (independentCachedEdge 252)=independentCachedBranchMembers711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound711
def independentCachedBranchMembers713 : Finset ℕ := ([72,252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3102,3118,3126,3164,3178,3180,3186,3188,3226,3228,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers713 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers713 3126 5
  · have he : independentCachedBranchMembers713.erase 3126=independentCachedBranchMembers709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound709
  · have he : independentCachedBranchMembers713.filter (independentCachedEdge 3126)=independentCachedBranchMembers712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound712
def independentCachedBranchMembers714 : Finset ℕ := ([1596,1614,1686,1702,1720,1738,1748,1764,2614,2650,2716,2732,2738,2800,3102,3118,3164,3180,3186,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers714 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers714 5 (fun x => (if x<2738 then (if x<1748 then (if x<1702 then (if x<1614 then 0 else (if x<1686 then 0 else 0)) else (if x<1720 then 1 else (if x<1738 then 1 else 1))) else (if x<2650 then (if x<1764 then 1 else (if x<2614 then 0 else 2)) else (if x<2716 then 2 else (if x<2732 then 2 else 3)))) else (if x<3186 then (if x<3118 then (if x<2800 then 3 else (if x<3102 then 2 else 0)) else (if x<3164 then 4 else (if x<3180 then 4 else 0))) else (if x<3270 then (if x<3226 then 2 else (if x<3252 then 4 else 0)) else (if x<3288 then 0 else (if x<3304 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers715 : Finset ℕ := ([1614,1686,1702,1738,2614,2650,2738,3102,3118,3186,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers715 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers715 4 (fun x => (if x<2738 then (if x<1738 then (if x<1686 then 0 else (if x<1702 then 0 else 1)) else (if x<2614 then 1 else (if x<2650 then 1 else 1))) else (if x<3186 then (if x<3102 then 0 else (if x<3118 then 2 else 3)) else (if x<3226 then 2 else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers716 : Finset ℕ := ([252,1596,1614,1686,1702,1720,1738,1748,1764,2614,2650,2716,2732,2738,2800,3102,3118,3164,3180,3186,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers716 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers716 252 4
  · have he : independentCachedBranchMembers716.erase 252=independentCachedBranchMembers714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound714
  · have he : independentCachedBranchMembers716.filter (independentCachedEdge 252)=independentCachedBranchMembers715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound715
def independentCachedBranchMembers717 : Finset ℕ := ([1596,1720,1748,1764,2716,2732,2800,3102,3118,3186,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers717 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers717 4 (fun x => (if x<2800 then (if x<1764 then (if x<1720 then 0 else (if x<1748 then 1 else 0)) else (if x<2716 then 1 else (if x<2732 then 0 else 1))) else (if x<3186 then (if x<3102 then 1 else (if x<3118 then 2 else 3)) else (if x<3226 then 2 else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers718 : Finset ℕ := ([72,252,1596,1614,1686,1702,1720,1738,1748,1764,2614,2650,2716,2732,2738,2800,3102,3118,3164,3180,3186,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers718 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers718 72 4
  · have he : independentCachedBranchMembers718.erase 72=independentCachedBranchMembers716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound716
  · have he : independentCachedBranchMembers718.filter (independentCachedEdge 72)=independentCachedBranchMembers717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound717
def independentCachedBranchMembers719 : Finset ℕ := ([72,252,1594,1596,1614,1678,1686,1702,1720,1738,1740,1746,1748,1764,2606,2614,2650,2652,2668,2674,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3102,3118,3126,3164,3178,3180,3186,3188,3226,3228,3244,3250,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers719 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers719 2674 5
  · have he : independentCachedBranchMembers719.erase 2674=independentCachedBranchMembers713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound713
  · have he : independentCachedBranchMembers719.filter (independentCachedEdge 2674)=independentCachedBranchMembers718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound718
def independentCachedBranchMembers720 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers720 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers720 1734 6
  · have he : independentCachedBranchMembers720.erase 1734=independentCachedBranchMembers670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound670
  · have he : independentCachedBranchMembers720.filter (independentCachedEdge 1734)=independentCachedBranchMembers719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound719
def independentCachedBranchMembers721 : Finset ℕ := ([1590,1626,1642,1652,1678,1692,1708,1714,1746,1776,2620,2638,2674,2710,2730,2776,2788,3102,3118,3180,3186,3226,3238,3252,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers721 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers721 6 (fun x => (if x<2710 then (if x<1708 then (if x<1652 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1678 then 1 else (if x<1692 then 0 else 2))) else (if x<1776 then (if x<1714 then 1 else (if x<1746 then 1 else 2)) else (if x<2638 then (if x<2620 then 3 else 2) else (if x<2674 then 3 else 0)))) else (if x<3186 then (if x<2788 then (if x<2730 then 2 else (if x<2776 then 1 else 2)) else (if x<3118 then (if x<3102 then 3 else 3) else (if x<3180 then 4 else 5))) else (if x<3252 then (if x<3226 then 4 else (if x<3238 then 4 else 5)) else (if x<3274 then (if x<3256 then 3 else 5) else (if x<3284 then 5 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers722 : Finset ℕ := ([1590,1626,1642,1714,2638,2710,2776,3180,3238,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers722 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers722 5 (fun x => (if x<2710 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1714 then 1 else (if x<2638 then 1 else 1))) else (if x<3238 then (if x<2776 then 1 else (if x<3180 then 0 else 1)) else (if x<3252 then 0 else (if x<3274 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers723 : Finset ℕ := ([1590,1594,1626,1642,1652,1678,1692,1708,1714,1746,1776,2620,2638,2674,2710,2730,2776,2788,3102,3118,3180,3186,3226,3238,3252,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers723 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers723 1594 5
  · have he : independentCachedBranchMembers723.erase 1594=independentCachedBranchMembers721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound721
  · have he : independentCachedBranchMembers723.filter (independentCachedEdge 1594)=independentCachedBranchMembers722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound722
def independentCachedBranchMembers724 : Finset ℕ := ([1594,1678,1746,2620,2638,2710,2788,3102,3118,3180,3186,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers724 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers724 5 (fun x => (if x<2788 then (if x<2620 then (if x<1678 then 0 else (if x<1746 then 0 else 0)) else (if x<2638 then 1 else (if x<2710 then 1 else 1))) else (if x<3180 then (if x<3102 then 1 else (if x<3118 then 1 else 0)) else (if x<3226 then (if x<3186 then 1 else 0) else (if x<3252 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers725 : Finset ℕ := ([1590,1594,1626,1642,1652,1678,1692,1708,1714,1746,1776,2620,2638,2674,2710,2730,2740,2776,2788,3102,3118,3180,3186,3226,3238,3252,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers725 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers725 2740 5
  · have he : independentCachedBranchMembers725.erase 2740=independentCachedBranchMembers723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound723
  · have he : independentCachedBranchMembers725.filter (independentCachedEdge 2740)=independentCachedBranchMembers724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound724
def independentCachedBranchMembers726 : Finset ℕ := ([1590,1642,1708,1776,2710,2730,2776,2788,3118,3186,3226,3238,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers726 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers726 5 (fun x => (if x<2788 then (if x<1776 then (if x<1642 then 0 else (if x<1708 then 0 else 0)) else (if x<2730 then (if x<2710 then 0 else 1) else (if x<2776 then 1 else 1))) else (if x<3226 then (if x<3118 then 1 else (if x<3186 then 0 else 0)) else (if x<3252 then (if x<3238 then 1 else 1) else (if x<3284 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers727 : Finset ℕ := ([1590,1594,1626,1642,1652,1678,1692,1708,1714,1746,1776,2620,2638,2674,2710,2714,2730,2740,2776,2788,3102,3118,3180,3186,3226,3238,3252,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers727 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers727 2714 5
  · have he : independentCachedBranchMembers727.erase 2714=independentCachedBranchMembers725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound725
  · have he : independentCachedBranchMembers727.filter (independentCachedEdge 2714)=independentCachedBranchMembers726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound726
def independentCachedBranchMembers728 : Finset ℕ := ([1626,1652,1692,1714,2620,2638,2730,2776,3118,3186,3226,3252,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers728 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers728 5 (fun x => (if x<2776 then (if x<1714 then (if x<1652 then 0 else (if x<1692 then 0 else 0)) else (if x<2638 then (if x<2620 then 0 else 1) else (if x<2730 then 1 else 1))) else (if x<3226 then (if x<3118 then 1 else (if x<3186 then 1 else 0)) else (if x<3256 then (if x<3252 then 0 else 0) else (if x<3274 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers729 : Finset ℕ := ([1590,1594,1626,1642,1652,1678,1692,1708,1714,1746,1776,2606,2620,2638,2674,2710,2714,2730,2740,2776,2788,3102,3118,3180,3186,3226,3238,3252,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers729 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers729 2606 5
  · have he : independentCachedBranchMembers729.erase 2606=independentCachedBranchMembers727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound727
  · have he : independentCachedBranchMembers729.filter (independentCachedEdge 2606)=independentCachedBranchMembers728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound728
def independentCachedBranchMembers730 : Finset ℕ := ([1594,1626,1652,1678,1692,1714,1746,2606,2620,2638,2674,2714,2740,3102,3180,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers730 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers730 5 (fun x => (if x<2620 then (if x<1692 then (if x<1652 then (if x<1626 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<1746 then (if x<1714 then 0 else 1) else (if x<2606 then 0 else 2))) else (if x<2740 then (if x<2674 then (if x<2638 then 0 else 1) else (if x<2714 then 0 else 0)) else (if x<3180 then (if x<3102 then 2 else 3) else (if x<3256 then 3 else (if x<3274 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers731 : Finset ℕ := ([1590,1594,1626,1642,1652,1678,1692,1708,1714,1746,1776,2606,2620,2638,2674,2710,2714,2730,2740,2776,2788,3102,3118,3180,3186,3226,3238,3252,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers731 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers731 3304 5
  · have he : independentCachedBranchMembers731.erase 3304=independentCachedBranchMembers729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound729
  · have he : independentCachedBranchMembers731.filter (independentCachedEdge 3304)=independentCachedBranchMembers730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound730
def independentCachedBranchMembers732 : Finset ℕ := ([1590,1594,1642,1678,1708,1746,1776,2606,2674,2710,2714,2740,2788,3102,3180,3238,3284] : List ℕ).toFinset
theorem independentCachedBranchBound732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers732 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers732 5 (fun x => (if x<2674 then (if x<1708 then (if x<1642 then (if x<1594 then 0 else 1) else (if x<1678 then 0 else 0)) else (if x<1776 then (if x<1746 then 1 else 0) else (if x<2606 then 1 else 0))) else (if x<2788 then (if x<2714 then (if x<2710 then 0 else 0) else (if x<2740 then 2 else 2)) else (if x<3180 then (if x<3102 then 1 else 3) else (if x<3238 then 3 else (if x<3284 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers733 : Finset ℕ := ([1590,1594,1626,1642,1652,1678,1692,1708,1714,1746,1776,2606,2620,2638,2674,2710,2714,2730,2740,2776,2788,3102,3118,3164,3180,3186,3226,3238,3252,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers733 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers733 3164 5
  · have he : independentCachedBranchMembers733.erase 3164=independentCachedBranchMembers731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound731
  · have he : independentCachedBranchMembers733.filter (independentCachedEdge 3164)=independentCachedBranchMembers732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound732
def independentCachedBranchMembers734 : Finset ℕ := ([1590,1594,1678,1692,1708,1714,2606,2620,2710,2714,2730,2740,3102,3118,3226,3238,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers734 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers734 5 (fun x => (if x<2714 then (if x<1708 then (if x<1678 then (if x<1594 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<2606 then (if x<1714 then 2 else 2) else (if x<2620 then 0 else (if x<2710 then 1 else 0)))) else (if x<3118 then (if x<2740 then (if x<2730 then 1 else 2) else (if x<3102 then 2 else 0)) else (if x<3238 then (if x<3226 then 3 else 3) else (if x<3252 then 0 else (if x<3256 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers735 : Finset ℕ := ([1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2674,2710,2714,2730,2740,2776,2788,3102,3118,3164,3180,3186,3226,3238,3252,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers735 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers735 1740 5
  · have he : independentCachedBranchMembers735.erase 1740=independentCachedBranchMembers733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound733
  · have he : independentCachedBranchMembers735.filter (independentCachedEdge 1740)=independentCachedBranchMembers734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound734
def independentCachedBranchMembers736 : Finset ℕ := ([1594,1626,1652,1678,1692,1714,1746,2710,2730,2776,2788,3118,3164,3186,3226,3238,3252,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers736 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers736 5 (fun x => (if x<2776 then (if x<1692 then (if x<1652 then (if x<1626 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<1746 then (if x<1714 then 0 else 1) else (if x<2710 then 0 else (if x<2730 then 2 else 2)))) else (if x<3226 then (if x<3118 then (if x<2788 then 2 else 2) else (if x<3164 then 3 else (if x<3186 then 3 else 0))) else (if x<3252 then (if x<3238 then 0 else 1) else (if x<3284 then 3 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers737 : Finset ℕ := ([1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2674,2710,2714,2730,2740,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers737 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers737 2792 5
  · have he : independentCachedBranchMembers737.erase 2792=independentCachedBranchMembers735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound735
  · have he : independentCachedBranchMembers737.filter (independentCachedEdge 2792)=independentCachedBranchMembers736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound736
def independentCachedBranchMembers738 : Finset ℕ := ([1590,1594,1642,1678,1708,1746,1776,2620,2638,2730,2776,3118,3164,3186,3226,3252,3256,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers738 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers738 5 (fun x => (if x<2730 then (if x<1708 then (if x<1642 then (if x<1594 then 0 else 1) else (if x<1678 then 0 else 0)) else (if x<1776 then (if x<1746 then 1 else 0) else (if x<2620 then 1 else (if x<2638 then 2 else 2)))) else (if x<3226 then (if x<3118 then (if x<2776 then 2 else 2) else (if x<3164 then 0 else (if x<3186 then 2 else 0))) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3274 then 1 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers739 : Finset ℕ := ([1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2674,2710,2714,2730,2740,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers739 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers739 2652 5
  · have he : independentCachedBranchMembers739.erase 2652=independentCachedBranchMembers737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound737
  · have he : independentCachedBranchMembers739.filter (independentCachedEdge 2652)=independentCachedBranchMembers738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound738
def independentCachedBranchMembers740 : Finset ℕ := ([1590,1594,1626,1642,1678,1714,1746,2606,2638,2674,2710,2714,2730,3102,3118,3186,3226,3238,3274] : List ℕ).toFinset
theorem independentCachedBranchBound740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers740 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers740 5 (fun x => (if x<2674 then (if x<1678 then (if x<1626 then (if x<1594 then 0 else 1) else (if x<1642 then 0 else 2)) else (if x<1746 then (if x<1714 then 0 else 2) else (if x<2606 then 1 else (if x<2638 then 1 else 2)))) else (if x<3118 then (if x<2714 then (if x<2710 then 0 else 2) else (if x<2730 then 1 else (if x<3102 then 2 else 3))) else (if x<3226 then (if x<3186 then 4 else 3) else (if x<3238 then 4 else (if x<3274 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers741 : Finset ℕ := ([252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2674,2710,2714,2730,2740,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers741 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers741 252 5
  · have he : independentCachedBranchMembers741.erase 252=independentCachedBranchMembers739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound739
  · have he : independentCachedBranchMembers741.filter (independentCachedEdge 252)=independentCachedBranchMembers740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound740
def independentCachedBranchMembers742 : Finset ℕ := ([1594,1652,1678,1692,1708,1746,1776,2606,2620,2674,2714,2730,2788,3102,3118,3186,3226,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers742 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers742 5 (fun x => (if x<2674 then (if x<1708 then (if x<1678 then (if x<1652 then 0 else 0) else (if x<1692 then 1 else 0)) else (if x<1776 then (if x<1746 then 2 else 0) else (if x<2606 then 2 else (if x<2620 then 1 else 0)))) else (if x<3118 then (if x<2730 then (if x<2714 then 0 else 0) else (if x<2788 then 3 else (if x<3102 then 2 else 1))) else (if x<3226 then (if x<3186 then 3 else 4) else (if x<3256 then 3 else (if x<3284 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers743 : Finset ℕ := ([72,252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2674,2710,2714,2730,2740,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers743 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers743 72 5
  · have he : independentCachedBranchMembers743.erase 72=independentCachedBranchMembers741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound741
  · have he : independentCachedBranchMembers743.filter (independentCachedEdge 72)=independentCachedBranchMembers742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound742
def independentCachedBranchMembers744 : Finset ℕ := ([1594,1642,1652,1678,1708,1714,2620,2638,2674,2710,2730,2740,2776,2788,3118,3164,3226,3238,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers744 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers744 5 (fun x => (if x<2740 then (if x<1714 then (if x<1652 then (if x<1642 then 0 else 1) else (if x<1678 then 0 else (if x<1708 then 1 else 0))) else (if x<2674 then (if x<2620 then 1 else (if x<2638 then 0 else 1)) else (if x<2710 then 0 else (if x<2730 then 1 else 0)))) else (if x<3226 then (if x<2788 then (if x<2776 then 2 else 2) else (if x<3118 then 0 else (if x<3164 then 3 else 3))) else (if x<3274 then (if x<3238 then 3 else (if x<3256 then 2 else 2)) else (if x<3284 then 2 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers745 : Finset ℕ := ([72,252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2674,2710,2714,2730,2740,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3274,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers745 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers745 3288 5
  · have he : independentCachedBranchMembers745.erase 3288=independentCachedBranchMembers743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound743
  · have he : independentCachedBranchMembers745.filter (independentCachedEdge 3288)=independentCachedBranchMembers744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound744
def independentCachedBranchMembers746 : Finset ℕ := ([72,252,1590,1626,1642,1652,1692,1708,1714,1776,2606,2652,2674,2714,2730,2740,2776,2792,3238,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers746 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers746 5 (fun x => (if x<2652 then (if x<1652 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1626 then 1 else (if x<1642 then 1 else 2))) else (if x<1714 then (if x<1692 then 2 else (if x<1708 then 1 else 2)) else (if x<1776 then 2 else (if x<2606 then 1 else 3)))) else (if x<2776 then (if x<2714 then (if x<2674 then 0 else 1) else (if x<2730 then 3 else (if x<2740 then 2 else 0))) else (if x<3256 then (if x<2792 then 1 else (if x<3238 then 0 else 4)) else (if x<3274 then 4 else (if x<3284 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers747 : Finset ℕ := ([72,252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2674,2710,2714,2730,2740,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3270,3274,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers747 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers747 3270 5
  · have he : independentCachedBranchMembers747.erase 3270=independentCachedBranchMembers745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound745
  · have he : independentCachedBranchMembers747.filter (independentCachedEdge 3270)=independentCachedBranchMembers746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound746
def independentCachedBranchMembers748 : Finset ℕ := ([1590,1626,1678,1708,1714,2606,2652,2710,2730,2740,2776,2788,3102,3180,3186,3226,3238,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers748 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers748 5 (fun x => (if x<2776 then (if x<2606 then (if x<1678 then (if x<1626 then 0 else 0) else (if x<1708 then 0 else (if x<1714 then 1 else 1))) else (if x<2710 then (if x<2652 then 2 else 2) else (if x<2730 then 2 else (if x<2740 then 1 else 1)))) else (if x<3226 then (if x<3102 then (if x<2788 then 3 else 2) else (if x<3180 then 0 else (if x<3186 then 2 else 0))) else (if x<3274 then (if x<3238 then 3 else (if x<3256 then 0 else 1)) else (if x<3284 then 0 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers749 : Finset ℕ := ([1678,1708,2606,2730,2788,3102,3186,3226,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers749 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers749 4 (fun x => (if x<3102 then (if x<2606 then (if x<1708 then 0 else 1) else (if x<2730 then 0 else (if x<2788 then 1 else 1))) else (if x<3226 then (if x<3186 then 0 else 2) else (if x<3256 then 2 else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers750 : Finset ℕ := ([72,1590,1626,1678,1708,1714,2606,2652,2710,2730,2740,2776,2788,3102,3180,3186,3226,3238,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers750 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers750 72 4
  · have he : independentCachedBranchMembers750.erase 72=independentCachedBranchMembers748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound748
  · have he : independentCachedBranchMembers750.filter (independentCachedEdge 72)=independentCachedBranchMembers749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound749
def independentCachedBranchMembers751 : Finset ℕ := ([72,252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2674,2710,2714,2730,2740,2772,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3270,3274,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers751 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers751 2772 5
  · have he : independentCachedBranchMembers751.erase 2772=independentCachedBranchMembers747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound747
  · have he : independentCachedBranchMembers751.filter (independentCachedEdge 2772)=independentCachedBranchMembers750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound750
def independentCachedBranchMembers752 : Finset ℕ := ([1594,1692,1708,1714,1776,2620,2638,2714,2730,2740,2776,2792,3102,3118,3164,3180,3186,3238,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers752 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers752 5 (fun x => (if x<2776 then (if x<2620 then (if x<1708 then (if x<1692 then 0 else 0) else (if x<1714 then 1 else (if x<1776 then 1 else 0))) else (if x<2714 then (if x<2638 then 2 else 2) else (if x<2730 then 2 else (if x<2740 then 1 else 1)))) else (if x<3180 then (if x<3102 then (if x<2792 then 3 else 2) else (if x<3118 then 0 else (if x<3164 then 3 else 3))) else (if x<3256 then (if x<3186 then 2 else (if x<3238 then 0 else 1)) else (if x<3274 then 0 else (if x<3284 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers753 : Finset ℕ := ([1594,1714,2638,2714,2730,3102,3118,3186,3238,3274] : List ℕ).toFinset
theorem independentCachedBranchBound753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers753 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers753 4 (fun x => (if x<3102 then (if x<2638 then (if x<1714 then 0 else 1) else (if x<2714 then 1 else (if x<2730 then 0 else 1))) else (if x<3186 then (if x<3118 then 0 else 2) else (if x<3238 then 2 else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers754 : Finset ℕ := ([252,1594,1692,1708,1714,1776,2620,2638,2714,2730,2740,2776,2792,3102,3118,3164,3180,3186,3238,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers754 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers754 252 4
  · have he : independentCachedBranchMembers754.erase 252=independentCachedBranchMembers752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound752
  · have he : independentCachedBranchMembers754.filter (independentCachedEdge 252)=independentCachedBranchMembers753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound753
def independentCachedBranchMembers755 : Finset ℕ := ([72,252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2674,2710,2714,2730,2740,2762,2772,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3270,3274,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers755 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers755 2762 5
  · have he : independentCachedBranchMembers755.erase 2762=independentCachedBranchMembers751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound751
  · have he : independentCachedBranchMembers755.filter (independentCachedEdge 2762)=independentCachedBranchMembers754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound754
def independentCachedBranchMembers756 : Finset ℕ := ([1590,1594,1626,1678,1692,1776,2606,2620,2638,2652,2710,2714,2788,2792,3102,3180,3186,3238,3252,3256,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers756 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers756 5 (fun x => (if x<2788 then (if x<2606 then (if x<1678 then (if x<1594 then 0 else (if x<1626 then 1 else 0)) else (if x<1692 then 0 else (if x<1776 then 1 else 1))) else (if x<2652 then (if x<2620 then 2 else (if x<2638 then 3 else 3)) else (if x<2710 then 2 else (if x<2714 then 2 else 3)))) else (if x<3252 then (if x<3180 then (if x<2792 then 2 else (if x<3102 then 3 else 0)) else (if x<3186 then 2 else (if x<3238 then 0 else 0))) else (if x<3274 then (if x<3256 then 4 else (if x<3270 then 1 else 4)) else (if x<3284 then 0 else (if x<3288 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers757 : Finset ℕ := ([72,252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2668,2674,2710,2714,2730,2740,2762,2772,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3270,3274,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers757 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers757 2668 5
  · have he : independentCachedBranchMembers757.erase 2668=independentCachedBranchMembers755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound755
  · have he : independentCachedBranchMembers757.filter (independentCachedEdge 2668)=independentCachedBranchMembers756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound756
def independentCachedBranchMembers758 : Finset ℕ := ([72,1590,1642,1678,1692,1714,1746,2606,2620,2638,2652,2674,2710,2730,2762,2776,2788,3102,3180,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers758 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers758 5 (fun x => (if x<2710 then (if x<1746 then (if x<1678 then (if x<1590 then 0 else (if x<1642 then 0 else 0)) else (if x<1692 then 1 else (if x<1714 then 2 else 1))) else (if x<2638 then (if x<2606 then 2 else (if x<2620 then 3 else 2)) else (if x<2652 then 1 else (if x<2674 then 3 else 1)))) else (if x<3180 then (if x<2776 then (if x<2730 then 0 else (if x<2762 then 1 else 0)) else (if x<2788 then 2 else (if x<3102 then 3 else 3))) else (if x<3252 then (if x<3226 then 3 else (if x<3238 then 4 else 3)) else (if x<3284 then (if x<3270 then 0 else 4) else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers759 : Finset ℕ := ([72,252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2668,2674,2710,2714,2730,2740,2762,2772,2776,2788,2792,3102,3118,3164,3180,3186,3226,3238,3252,3256,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers759 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers759 3300 5
  · have he : independentCachedBranchMembers759.erase 3300=independentCachedBranchMembers757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound757
  · have he : independentCachedBranchMembers759.filter (independentCachedEdge 3300)=independentCachedBranchMembers758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound758
def independentCachedBranchMembers760 : Finset ℕ := ([1590,1594,1652,1692,1708,1746,2620,2638,2674,2710,2714,2730,2772,2776,2788,2792,3102,3118,3164,3180,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers760 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers760 5 (fun x => (if x<2772 then (if x<2620 then (if x<1692 then (if x<1594 then 0 else (if x<1652 then 1 else 1)) else (if x<1708 then 0 else (if x<1746 then 1 else 0))) else (if x<2710 then (if x<2638 then 0 else (if x<2674 then 2 else 0)) else (if x<2714 then 0 else (if x<2730 then 2 else 1)))) else (if x<3164 then (if x<2792 then (if x<2776 then 2 else (if x<2788 then 0 else 1)) else (if x<3102 then 2 else (if x<3118 then 3 else 4))) else (if x<3256 then (if x<3180 then 4 else (if x<3252 then 3 else 3)) else (if x<3270 then 4 else (if x<3274 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers761 : Finset ℕ := ([1590,1594,1746,2638,2674,2710,2714,2730,3102,3118,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers761 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers761 4 (fun x => (if x<2714 then (if x<2638 then (if x<1594 then 0 else (if x<1746 then 1 else 0)) else (if x<2674 then 2 else (if x<2710 then 0 else 0))) else (if x<3118 then (if x<2730 then 1 else (if x<3102 then 2 else 1)) else (if x<3270 then 2 else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers762 : Finset ℕ := ([252,1590,1594,1652,1692,1708,1746,2620,2638,2674,2710,2714,2730,2772,2776,2788,2792,3102,3118,3164,3180,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers762 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers762 252 4
  · have he : independentCachedBranchMembers762.erase 252=independentCachedBranchMembers760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound760
  · have he : independentCachedBranchMembers762.filter (independentCachedEdge 252)=independentCachedBranchMembers761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound761
def independentCachedBranchMembers763 : Finset ℕ := ([72,252,1590,1594,1626,1642,1652,1678,1692,1708,1714,1740,1746,1776,2606,2620,2638,2652,2668,2674,2710,2714,2730,2740,2762,2772,2776,2788,2792,3102,3118,3150,3164,3180,3186,3226,3238,3252,3256,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers763 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers763 3150 5
  · have he : independentCachedBranchMembers763.erase 3150=independentCachedBranchMembers759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound759
  · have he : independentCachedBranchMembers763.filter (independentCachedEdge 3150)=independentCachedBranchMembers762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound762
def independentCachedBranchMembers764 : Finset ℕ := ([1590,1626,1642,1652,1692,1708,1714,1776,2620,2638,2710,2762,2772,2788,3102,3118,3164,3180,3186,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers764 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers764 5 (fun x => (if x<2772 then (if x<1714 then (if x<1652 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 0 else 1))) else (if x<2638 then (if x<1776 then 1 else (if x<2620 then 0 else 2)) else (if x<2710 then 2 else (if x<2762 then 2 else 3)))) else (if x<3186 then (if x<3118 then (if x<2788 then 3 else (if x<3102 then 2 else 0)) else (if x<3164 then 4 else (if x<3180 then 4 else 1))) else (if x<3270 then (if x<3226 then 0 else (if x<3252 then 4 else 0)) else (if x<3288 then 2 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers765 : Finset ℕ := ([1590,1626,1642,1714,2638,2710,2762,3102,3118,3186,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers765 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers765 4 (fun x => (if x<2762 then (if x<1714 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<2638 then 1 else (if x<2710 then 1 else 1))) else (if x<3186 then (if x<3102 then 0 else (if x<3118 then 2 else 3)) else (if x<3226 then 2 else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers766 : Finset ℕ := ([252,1590,1626,1642,1652,1692,1708,1714,1776,2620,2638,2710,2762,2772,2788,3102,3118,3164,3180,3186,3226,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers766 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers766 252 4
  · have he : independentCachedBranchMembers766.erase 252=independentCachedBranchMembers764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound764
  · have he : independentCachedBranchMembers766.filter (independentCachedEdge 252)=independentCachedBranchMembers765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound765
def independentCachedBranchMembers767 : Finset ℕ := ([1652,1692,1708,1776,2620,2772,2788,3102,3118,3186,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers767 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers767 4 (fun x => (if x<2788 then (if x<1776 then (if x<1692 then 0 else (if x<1708 then 0 else 1)) else (if x<2620 then 1 else (if x<2772 then 0 else 0))) else (if x<3186 then (if x<3102 then 1 else (if x<3118 then 2 else 3)) else (if x<3226 then 2 else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
