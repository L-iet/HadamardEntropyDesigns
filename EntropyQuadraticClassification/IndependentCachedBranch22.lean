/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch21
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers2816 : Finset ℕ := ([1594,1614,1678,1702,1720,1738,1746,1748,1764,2606,2650,2668,2674,2714,2730,2732,2738,2740,2758,2776,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2816 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2816 5 (fun x => (if x<2650 then (if x<1738 then (if x<1678 then (if x<1614 then 0 else 0) else (if x<1702 then 1 else (if x<1720 then 0 else 1))) else (if x<1748 then (if x<1746 then 2 else 0) else (if x<1764 then 1 else (if x<2606 then 2 else 0)))) else (if x<2732 then (if x<2674 then (if x<2668 then 0 else 3) else (if x<2714 then 3 else (if x<2730 then 2 else 1))) else (if x<2758 then (if x<2738 then 4 else (if x<2740 then 0 else 2)) else (if x<2776 then 0 else (if x<2800 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2817 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2817 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2817 1734 5
  · have he : independentCachedBranchMembers2817.erase 1734=independentCachedBranchMembers2815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2815
  · have he : independentCachedBranchMembers2817.filter (independentCachedEdge 1734)=independentCachedBranchMembers2816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2816
def independentCachedBranchMembers2818 : Finset ℕ := ([1590,1594,1642,1652,1678,1692,1708,1714,1746,2606,2620,2668,2674,2710,2714,2730,2740,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound2818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2818 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2818 5 (fun x => (if x<2620 then (if x<1692 then (if x<1642 then (if x<1594 then 0 else 1) else (if x<1652 then 0 else (if x<1678 then 1 else 0))) else (if x<1714 then (if x<1708 then 1 else 2) else (if x<1746 then 2 else (if x<2606 then 0 else 0)))) else (if x<2730 then (if x<2674 then (if x<2668 then 1 else 2) else (if x<2710 then 0 else (if x<2714 then 0 else 1))) else (if x<2762 then (if x<2740 then 2 else (if x<2758 then 2 else 3)) else (if x<2772 then 0 else (if x<2776 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2819 : Finset ℕ := ([1590,1594,1614,1628,1642,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2819 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2819 1650 5
  · have he : independentCachedBranchMembers2819.erase 1650=independentCachedBranchMembers2817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2817
  · have he : independentCachedBranchMembers2819.filter (independentCachedEdge 1650)=independentCachedBranchMembers2818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2818
def independentCachedBranchMembers2820 : Finset ℕ := ([1614,1628,1642,1652,1708,1714,1746,1764,1768,2646,2650,2668,2674,2730,2740,2758,2762,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2820 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2820 5 (fun x => (if x<2650 then (if x<1714 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1652 then 1 else (if x<1708 then 0 else 0))) else (if x<1764 then (if x<1746 then 2 else 1) else (if x<1768 then 1 else (if x<2646 then 2 else 0)))) else (if x<2758 then (if x<2674 then (if x<2668 then 1 else 0) else (if x<2730 then 3 else (if x<2740 then 2 else 0))) else (if x<2776 then (if x<2762 then 3 else (if x<2772 then 4 else 1)) else (if x<2786 then 3 else (if x<2800 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2821 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2821 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2821 1644 5
  · have he : independentCachedBranchMembers2821.erase 1644=independentCachedBranchMembers2819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2819
  · have he : independentCachedBranchMembers2821.filter (independentCachedEdge 1644)=independentCachedBranchMembers2820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2820
def independentCachedBranchMembers2822 : Finset ℕ := ([1594,1614,1628,1650,1652,1678,1692,1702,1714,1734,1746,1748,1768,2646,2668,2680,2710,2730,2732,2762,2764,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2822 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2822 5 (fun x => (if x<1768 then (if x<1692 then (if x<1650 then (if x<1614 then 0 else (if x<1628 then 0 else 1)) else (if x<1652 then 1 else (if x<1678 then 0 else 2))) else (if x<1734 then (if x<1702 then 0 else (if x<1714 then 0 else 2)) else (if x<1746 then 1 else (if x<1748 then 0 else 2)))) else (if x<2732 then (if x<2680 then (if x<2646 then 0 else (if x<2668 then 1 else 3)) else (if x<2710 then 1 else (if x<2730 then 2 else 2))) else (if x<2776 then (if x<2762 then 4 else (if x<2764 then 3 else 1)) else (if x<2786 then 4 else (if x<2800 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2823 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2823 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2823 2792 5
  · have he : independentCachedBranchMembers2823.erase 2792=independentCachedBranchMembers2821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2821
  · have he : independentCachedBranchMembers2823.filter (independentCachedEdge 2792)=independentCachedBranchMembers2822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2822
def independentCachedBranchMembers2824 : Finset ℕ := ([1590,1594,1628,1642,1644,1678,1714,1720,1746,1748,1752,1764,1768,2606,2674,2680,2710,2714,2730,2732,2758,2762,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2824 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2824 5 (fun x => (if x<1768 then (if x<1714 then (if x<1642 then (if x<1594 then 0 else (if x<1628 then 1 else 0)) else (if x<1644 then 0 else (if x<1678 then 1 else 0))) else (if x<1748 then (if x<1720 then 2 else (if x<1746 then 0 else 0)) else (if x<1752 then 2 else (if x<1764 then 1 else 0)))) else (if x<2730 then (if x<2680 then (if x<2606 then 2 else (if x<2674 then 1 else 3)) else (if x<2710 then 1 else (if x<2714 then 2 else 1))) else (if x<2762 then (if x<2732 then 2 else (if x<2758 then 4 else 3)) else (if x<2764 then 4 else (if x<2800 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2825 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2702,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2825 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2825 2702 5
  · have he : independentCachedBranchMembers2825.erase 2702=independentCachedBranchMembers2823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2823
  · have he : independentCachedBranchMembers2825.filter (independentCachedEdge 2702)=independentCachedBranchMembers2824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2824
def independentCachedBranchMembers2826 : Finset ℕ := ([1590,1594,1628,1642,1650,1678,1708,1720,1734,1738,1746,1764,1768,2620,2646,2650,2668,2680,2730,2738,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2826 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2826 5 (fun x => (if x<1768 then (if x<1708 then (if x<1642 then (if x<1594 then 0 else (if x<1628 then 1 else 0)) else (if x<1650 then 0 else (if x<1678 then 2 else 0))) else (if x<1738 then (if x<1720 then 1 else (if x<1734 then 0 else 2)) else (if x<1746 then 1 else (if x<1764 then 0 else 0)))) else (if x<2730 then (if x<2650 then (if x<2620 then 2 else (if x<2646 then 1 else 2)) else (if x<2668 then 1 else (if x<2680 then 3 else 2))) else (if x<2772 then (if x<2738 then 1 else (if x<2764 then 4 else 1)) else (if x<2776 then 3 else (if x<2786 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2827 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2620,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2827 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2827 2652 5
  · have he : independentCachedBranchMembers2827.erase 2652=independentCachedBranchMembers2825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2825
  · have he : independentCachedBranchMembers2827.filter (independentCachedEdge 2652)=independentCachedBranchMembers2826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2826
def independentCachedBranchMembers2828 : Finset ℕ := ([1594,1628,1652,1678,1708,1738,1746,1752,2606,2620,2650,2674,2680,2714,2730,2738,2758,2764,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2828 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2828 5 (fun x => (if x<2620 then (if x<1708 then (if x<1652 then (if x<1628 then 0 else 0) else (if x<1678 then 1 else 0)) else (if x<1746 then (if x<1738 then 1 else 2) else (if x<1752 then 0 else (if x<2606 then 1 else 3)))) else (if x<2730 then (if x<2674 then (if x<2650 then 2 else 2) else (if x<2680 then 3 else (if x<2714 then 4 else 3))) else (if x<2758 then (if x<2738 then 2 else 4) else (if x<2764 then 3 else (if x<2772 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2829 : Finset ℕ := ([1628,1678,1708,1752,2620,2674,2714,2764,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2829 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2829 4 (fun x => (if x<2620 then (if x<1708 then (if x<1678 then 0 else 0) else (if x<1752 then 1 else 1)) else (if x<2714 then (if x<2674 then 2 else 2) else (if x<2764 then 2 else (if x<2772 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2830 : Finset ℕ := ([1594,1628,1652,1678,1702,1708,1738,1746,1752,2606,2620,2650,2674,2680,2714,2730,2738,2758,2764,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2830 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2830 1702 4
  · have he : independentCachedBranchMembers2830.erase 1702=independentCachedBranchMembers2828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2828
  · have he : independentCachedBranchMembers2830.filter (independentCachedEdge 1702)=independentCachedBranchMembers2829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2829
def independentCachedBranchMembers2831 : Finset ℕ := ([1628,1652,1708,1746,2650,2674,2730,2758,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2831 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2831 4 (fun x => (if x<2650 then (if x<1708 then (if x<1652 then 0 else 1) else (if x<1746 then 0 else 1)) else (if x<2730 then (if x<2674 then 0 else 1) else (if x<2758 then 0 else (if x<2772 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2832 : Finset ℕ := ([1594,1628,1644,1652,1678,1702,1708,1738,1746,1752,2606,2620,2650,2674,2680,2714,2730,2738,2758,2764,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2832 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2832 1644 4
  · have he : independentCachedBranchMembers2832.erase 1644=independentCachedBranchMembers2830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2830
  · have he : independentCachedBranchMembers2832.filter (independentCachedEdge 1644)=independentCachedBranchMembers2831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2831
def independentCachedBranchMembers2833 : Finset ℕ := ([1628,1678,1708,1752,2606,2650,2680,2730,2738,2758] : List ℕ).toFinset
theorem independentCachedBranchBound2833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2833 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2833 4 (fun x => (if x<2650 then (if x<1708 then (if x<1678 then 0 else 0) else (if x<1752 then 1 else (if x<2606 then 1 else 1))) else (if x<2730 then (if x<2680 then 1 else 0) else (if x<2738 then 0 else (if x<2758 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2834 : Finset ℕ := ([1594,1628,1644,1652,1678,1692,1702,1708,1738,1746,1752,2606,2620,2650,2674,2680,2714,2730,2738,2758,2764,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2834 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2834 1692 4
  · have he : independentCachedBranchMembers2834.erase 1692=independentCachedBranchMembers2832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2832
  · have he : independentCachedBranchMembers2834.filter (independentCachedEdge 1692)=independentCachedBranchMembers2833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2833
def independentCachedBranchMembers2835 : Finset ℕ := ([1628,1644,1678,1738,2620,2674,2680,2714,2730,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2835 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2835 4 (fun x => (if x<2674 then (if x<1678 then (if x<1644 then 0 else 1) else (if x<1738 then 0 else (if x<2620 then 1 else 1))) else (if x<2714 then (if x<2680 then 2 else 0) else (if x<2730 then 1 else (if x<2772 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2836 : Finset ℕ := ([1594,1614,1628,1644,1652,1678,1692,1702,1708,1738,1746,1752,2606,2620,2650,2674,2680,2714,2730,2738,2758,2764,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2836 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2836 1614 4
  · have he : independentCachedBranchMembers2836.erase 1614=independentCachedBranchMembers2834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2834
  · have he : independentCachedBranchMembers2836.filter (independentCachedEdge 1614)=independentCachedBranchMembers2835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2835
def independentCachedBranchMembers2837 : Finset ℕ := ([1644,1708,1738,1752,2606,2620,2650,2674,2714,2738,2758,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2837 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2837 4 (fun x => (if x<2650 then (if x<1752 then (if x<1708 then 0 else (if x<1738 then 1 else 0)) else (if x<2606 then 1 else (if x<2620 then 1 else 0))) else (if x<2738 then (if x<2674 then 1 else (if x<2714 then 2 else 0)) else (if x<2758 then 3 else (if x<2772 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2838 : Finset ℕ := ([1594,1614,1628,1644,1652,1678,1692,1702,1708,1738,1746,1752,1768,2606,2620,2650,2674,2680,2714,2730,2738,2758,2764,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2838 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2838 1768 4
  · have he : independentCachedBranchMembers2838.erase 1768=independentCachedBranchMembers2836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2836
  · have he : independentCachedBranchMembers2838.filter (independentCachedEdge 1768)=independentCachedBranchMembers2837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2837
def independentCachedBranchMembers2839 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2618,2620,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2839 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2839 2618 5
  · have he : independentCachedBranchMembers2839.erase 2618=independentCachedBranchMembers2827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2827
  · have he : independentCachedBranchMembers2839.filter (independentCachedEdge 2618)=independentCachedBranchMembers2838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2838
def independentCachedBranchMembers2840 : Finset ℕ := ([1642,1678,1714,1720,1738,1746,1752,1764,2618,2650,2662,2668,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2840 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2840 5 (fun x => (if x<2662 then (if x<1746 then (if x<1714 then (if x<1678 then 0 else 0) else (if x<1720 then 0 else (if x<1738 then 1 else 1))) else (if x<1764 then (if x<1752 then 2 else 0) else (if x<2618 then 0 else (if x<2650 then 3 else 2)))) else (if x<2758 then (if x<2714 then (if x<2668 then 3 else 2) else (if x<2732 then 1 else (if x<2740 then 3 else 1))) else (if x<2786 then (if x<2764 then 1 else (if x<2772 then 4 else 2)) else (if x<2792 then 2 else (if x<2800 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2841 : Finset ℕ := ([1642,1678,1714,1746,2668,2714,2740,2758,2772,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2841 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2841 4 (fun x => (if x<2714 then (if x<1714 then (if x<1678 then 0 else 0) else (if x<1746 then 0 else (if x<2668 then 1 else 1))) else (if x<2758 then (if x<2740 then 2 else 2) else (if x<2772 then 1 else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2842 : Finset ℕ := ([1642,1650,1678,1714,1720,1738,1746,1752,1764,2618,2650,2662,2668,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2842 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2842 1650 4
  · have he : independentCachedBranchMembers2842.erase 1650=independentCachedBranchMembers2840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2840
  · have he : independentCachedBranchMembers2842.filter (independentCachedEdge 1650)=independentCachedBranchMembers2841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2841
def independentCachedBranchMembers2843 : Finset ℕ := ([1714,1752,2618,2662,2714,2732,2740,2758,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2843 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2843 4 (fun x => (if x<2732 then (if x<2618 then (if x<1752 then 0 else 0) else (if x<2662 then 1 else (if x<2714 then 1 else 0))) else (if x<2758 then (if x<2740 then 1 else 2) else (if x<2792 then 2 else (if x<2800 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2844 : Finset ℕ := ([1628,1642,1650,1678,1714,1720,1738,1746,1752,1764,2618,2650,2662,2668,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2844 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2844 1628 4
  · have he : independentCachedBranchMembers2844.erase 1628=independentCachedBranchMembers2842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2842
  · have he : independentCachedBranchMembers2844.filter (independentCachedEdge 1628)=independentCachedBranchMembers2843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2843
def independentCachedBranchMembers2845 : Finset ℕ := ([1628,1642,1650,1678,1720,1752,2618,2650,2668,2758,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2845 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2845 4 (fun x => (if x<2618 then (if x<1678 then (if x<1642 then 0 else (if x<1650 then 0 else 1)) else (if x<1720 then 0 else (if x<1752 then 0 else 1))) else (if x<2758 then (if x<2650 then 2 else (if x<2668 then 1 else 2)) else (if x<2792 then 3 else (if x<2800 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2846 : Finset ℕ := ([1628,1642,1650,1678,1692,1714,1720,1738,1746,1752,1764,2618,2650,2662,2668,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2846 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2846 1692 4
  · have he : independentCachedBranchMembers2846.erase 1692=independentCachedBranchMembers2844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2844
  · have he : independentCachedBranchMembers2846.filter (independentCachedEdge 1692)=independentCachedBranchMembers2845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2845
def independentCachedBranchMembers2847 : Finset ℕ := ([1628,1642,1678,1714,1720,1738,2618,2714,2732,2772,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2847 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2847 4 (fun x => (if x<2618 then (if x<1714 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<1720 then 1 else (if x<1738 then 0 else 1))) else (if x<2772 then (if x<2714 then 2 else (if x<2732 then 1 else 2)) else (if x<2786 then 3 else (if x<2792 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2848 : Finset ℕ := ([1614,1628,1642,1650,1678,1692,1714,1720,1738,1746,1752,1764,2618,2650,2662,2668,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2848 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2848 1614 4
  · have he : independentCachedBranchMembers2848.erase 1614=independentCachedBranchMembers2846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2846
  · have he : independentCachedBranchMembers2848.filter (independentCachedEdge 1614)=independentCachedBranchMembers2847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2847
def independentCachedBranchMembers2849 : Finset ℕ := ([1650,1714,1738,1752,2650,2668,2714,2732,2758,2772,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2849 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2849 4 (fun x => (if x<2714 then (if x<1752 then (if x<1714 then 0 else (if x<1738 then 1 else 0)) else (if x<2650 then 1 else (if x<2668 then 0 else 2))) else (if x<2772 then (if x<2732 then 1 else (if x<2758 then 3 else 2)) else (if x<2786 then 3 else (if x<2800 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2850 : Finset ℕ := ([1590,1614,1628,1642,1650,1678,1692,1714,1720,1738,1746,1752,1764,2618,2650,2662,2668,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2850 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2850 1590 4
  · have he : independentCachedBranchMembers2850.erase 1590=independentCachedBranchMembers2848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2848
  · have he : independentCachedBranchMembers2850.filter (independentCachedEdge 1590)=independentCachedBranchMembers2849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2849
def independentCachedBranchMembers2851 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2618,2620,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2851 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2851 2788 5
  · have he : independentCachedBranchMembers2851.erase 2788=independentCachedBranchMembers2839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2839
  · have he : independentCachedBranchMembers2851.filter (independentCachedEdge 2788)=independentCachedBranchMembers2850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2850
def independentCachedBranchMembers2852 : Finset ℕ := ([1652,1692,1702,1714,1734,1746,1768,2620,2652,2662,2674,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2852 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2852 5 (fun x => (if x<2674 then (if x<1746 then (if x<1702 then (if x<1692 then 0 else 0) else (if x<1714 then 0 else (if x<1734 then 1 else 1))) else (if x<2620 then (if x<1768 then 0 else 0) else (if x<2652 then 2 else (if x<2662 then 3 else 2)))) else (if x<2740 then (if x<2710 then (if x<2702 then 3 else 2) else (if x<2714 then 1 else (if x<2732 then 3 else 4))) else (if x<2772 then (if x<2764 then 3 else 1) else (if x<2776 then 2 else (if x<2786 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2853 : Finset ℕ := ([1652,1734,1746,1768,2652,2662,2674,2710,2732,2772] : List ℕ).toFinset
theorem independentCachedBranchBound2853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2853 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2853 4 (fun x => (if x<2662 then (if x<1746 then (if x<1734 then 0 else 0) else (if x<1768 then 1 else (if x<2652 then 0 else 2))) else (if x<2710 then (if x<2674 then 2 else 1) else (if x<2732 then 1 else (if x<2772 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2854 : Finset ℕ := ([1652,1692,1702,1714,1734,1738,1746,1768,2620,2652,2662,2674,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2854 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2854 1738 4
  · have he : independentCachedBranchMembers2854.erase 1738=independentCachedBranchMembers2852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2852
  · have he : independentCachedBranchMembers2854.filter (independentCachedEdge 1738)=independentCachedBranchMembers2853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2853
def independentCachedBranchMembers2855 : Finset ℕ := ([1652,1714,1746,1768,2674,2702,2740,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2855 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2855 4 (fun x => (if x<2702 then (if x<1746 then (if x<1714 then 0 else 0) else (if x<1768 then 1 else (if x<2674 then 0 else 1))) else (if x<2772 then (if x<2740 then 2 else 2) else (if x<2776 then 1 else (if x<2786 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2856 : Finset ℕ := ([1644,1652,1692,1702,1714,1734,1738,1746,1768,2620,2652,2662,2674,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2856 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2856 1644 4
  · have he : independentCachedBranchMembers2856.erase 1644=independentCachedBranchMembers2854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2854
  · have he : independentCachedBranchMembers2856.filter (independentCachedEdge 1644)=independentCachedBranchMembers2855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2855
def independentCachedBranchMembers2857 : Finset ℕ := ([1714,1734,2652,2662,2702,2710,2732,2740,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2857 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2857 4 (fun x => (if x<2710 then (if x<2652 then (if x<1734 then 0 else 0) else (if x<2662 then 1 else (if x<2702 then 1 else 1))) else (if x<2740 then (if x<2732 then 0 else 2) else (if x<2776 then 1 else (if x<2786 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2858 : Finset ℕ := ([1594,1644,1652,1692,1702,1714,1734,1738,1746,1768,2620,2652,2662,2674,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2858 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2858 1594 4
  · have he : independentCachedBranchMembers2858.erase 1594=independentCachedBranchMembers2856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2856
  · have he : independentCachedBranchMembers2858.filter (independentCachedEdge 1594)=independentCachedBranchMembers2857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2857
def independentCachedBranchMembers2859 : Finset ℕ := ([1594,1644,1652,1702,1734,1768,2620,2652,2674,2702,2710,2776] : List ℕ).toFinset
theorem independentCachedBranchBound2859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2859 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2859 4 (fun x => (if x<2620 then (if x<1702 then (if x<1644 then 0 else (if x<1652 then 0 else 1)) else (if x<1734 then 0 else (if x<1768 then 1 else 1))) else (if x<2702 then (if x<2652 then 2 else (if x<2674 then 3 else 2)) else (if x<2710 then 3 else (if x<2776 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2860 : Finset ℕ := ([1594,1644,1652,1692,1702,1714,1734,1738,1746,1764,1768,2620,2652,2662,2674,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2860 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2860 1764 4
  · have he : independentCachedBranchMembers2860.erase 1764=independentCachedBranchMembers2858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2858
  · have he : independentCachedBranchMembers2860.filter (independentCachedEdge 1764)=independentCachedBranchMembers2859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2859
def independentCachedBranchMembers2861 : Finset ℕ := ([1644,1714,1734,1738,2620,2674,2710,2714,2732,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2861 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2861 4 (fun x => (if x<2710 then (if x<1738 then (if x<1714 then 0 else (if x<1734 then 1 else 0)) else (if x<2620 then 1 else (if x<2674 then 0 else 2))) else (if x<2772 then (if x<2714 then 0 else (if x<2732 then 1 else 3)) else (if x<2776 then 2 else (if x<2786 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2862 : Finset ℕ := ([1594,1614,1644,1652,1692,1702,1714,1734,1738,1746,1764,1768,2620,2652,2662,2674,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2862 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2862 1614 4
  · have he : independentCachedBranchMembers2862.erase 1614=independentCachedBranchMembers2860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2860
  · have he : independentCachedBranchMembers2862.filter (independentCachedEdge 1614)=independentCachedBranchMembers2861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2861
def independentCachedBranchMembers2863 : Finset ℕ := ([1594,1652,1702,1714,1738,1768,2652,2702,2714,2732,2772,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2863 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2863 4 (fun x => (if x<2652 then (if x<1714 then (if x<1652 then 0 else (if x<1702 then 0 else 0)) else (if x<1738 then 1 else (if x<1768 then 1 else 0))) else (if x<2732 then (if x<2702 then 2 else (if x<2714 then 2 else 1)) else (if x<2772 then 3 else (if x<2786 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2864 : Finset ℕ := ([1590,1594,1614,1644,1652,1692,1702,1714,1734,1738,1746,1764,1768,2620,2652,2662,2674,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2864 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2864 1590 4
  · have he : independentCachedBranchMembers2864.erase 1590=independentCachedBranchMembers2862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2862
  · have he : independentCachedBranchMembers2864.filter (independentCachedEdge 1590)=independentCachedBranchMembers2863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2863
def independentCachedBranchMembers2865 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2618,2620,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2865 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2865 2716 5
  · have he : independentCachedBranchMembers2865.erase 2716=independentCachedBranchMembers2851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2851
  · have he : independentCachedBranchMembers2865.filter (independentCachedEdge 2716)=independentCachedBranchMembers2864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2864
def independentCachedBranchMembers2866 : Finset ℕ := ([1614,1650,1652,1702,1746,1748,1752,1768,2606,2646,2650,2652,2662,2668,2702,2738,2740,2758,2762,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2866 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2866 5 (fun x => (if x<2650 then (if x<1748 then (if x<1652 then (if x<1650 then 0 else 0) else (if x<1702 then 1 else (if x<1746 then 0 else 1))) else (if x<1768 then (if x<1752 then 0 else 2) else (if x<2606 then 0 else (if x<2646 then 2 else 1)))) else (if x<2738 then (if x<2662 then (if x<2652 then 2 else 3) else (if x<2668 then 3 else (if x<2702 then 1 else 3))) else (if x<2762 then (if x<2740 then 4 else (if x<2758 then 3 else 4)) else (if x<2764 then 1 else (if x<2800 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2867 : Finset ℕ := ([1650,1702,1746,1768,2652,2662,2738,2758,2762,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2867 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2867 4 (fun x => (if x<2662 then (if x<1746 then (if x<1702 then 0 else 0) else (if x<1768 then 1 else (if x<2652 then 0 else 2))) else (if x<2758 then (if x<2738 then 2 else 1) else (if x<2762 then 1 else (if x<2800 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2868 : Finset ℕ := ([1614,1650,1652,1702,1708,1746,1748,1752,1768,2606,2646,2650,2652,2662,2668,2702,2738,2740,2758,2762,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2868 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2868 1708 4
  · have he : independentCachedBranchMembers2868.erase 1708=independentCachedBranchMembers2866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2866
  · have he : independentCachedBranchMembers2868.filter (independentCachedEdge 1708)=independentCachedBranchMembers2867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2867
def independentCachedBranchMembers2869 : Finset ℕ := ([1650,1748,2646,2652,2662,2668,2702,2740,2762,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2869 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2869 4 (fun x => (if x<2668 then (if x<2646 then (if x<1748 then 0 else 0) else (if x<2652 then 0 else (if x<2662 then 1 else 1))) else (if x<2740 then (if x<2702 then 2 else 1) else (if x<2762 then 1 else (if x<2800 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2870 : Finset ℕ := ([1594,1614,1650,1652,1702,1708,1746,1748,1752,1768,2606,2646,2650,2652,2662,2668,2702,2738,2740,2758,2762,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2870 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2870 1594 4
  · have he : independentCachedBranchMembers2870.erase 1594=independentCachedBranchMembers2868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2868
  · have he : independentCachedBranchMembers2870.filter (independentCachedEdge 1594)=independentCachedBranchMembers2869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2869
def independentCachedBranchMembers2871 : Finset ℕ := ([1594,1652,1702,1708,1748,1768,2606,2646,2652,2702,2738,2762] : List ℕ).toFinset
theorem independentCachedBranchBound2871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2871 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2871 4 (fun x => (if x<2606 then (if x<1708 then (if x<1652 then 0 else (if x<1702 then 0 else 0)) else (if x<1748 then 1 else (if x<1768 then 1 else 0))) else (if x<2702 then (if x<2646 then 1 else (if x<2652 then 1 else 2)) else (if x<2738 then 2 else (if x<2762 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2872 : Finset ℕ := ([1594,1614,1650,1652,1702,1708,1746,1748,1752,1764,1768,2606,2646,2650,2652,2662,2668,2702,2738,2740,2758,2762,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2872 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2872 1764 4
  · have he : independentCachedBranchMembers2872.erase 1764=independentCachedBranchMembers2870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2870
  · have he : independentCachedBranchMembers2872.filter (independentCachedEdge 1764)=independentCachedBranchMembers2871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2871
def independentCachedBranchMembers2873 : Finset ℕ := ([1650,1708,1748,1752,2606,2646,2650,2668,2738,2758,2762,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2873 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2873 4 (fun x => (if x<2650 then (if x<1752 then (if x<1708 then 0 else (if x<1748 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 1 else 0))) else (if x<2758 then (if x<2668 then 1 else (if x<2738 then 2 else 3)) else (if x<2762 then 2 else (if x<2800 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2874 : Finset ℕ := ([1594,1614,1650,1652,1692,1702,1708,1746,1748,1752,1764,1768,2606,2646,2650,2652,2662,2668,2702,2738,2740,2758,2762,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2874 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2874 1692 4
  · have he : independentCachedBranchMembers2874.erase 1692=independentCachedBranchMembers2872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2872
  · have he : independentCachedBranchMembers2874.filter (independentCachedEdge 1692)=independentCachedBranchMembers2873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2873
def independentCachedBranchMembers2875 : Finset ℕ := ([1594,1650,1652,1702,1752,1768,2650,2652,2668,2702,2758,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2875 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2875 4 (fun x => (if x<2650 then (if x<1702 then (if x<1650 then 0 else (if x<1652 then 1 else 0)) else (if x<1752 then 0 else (if x<1768 then 1 else 0))) else (if x<2702 then (if x<2652 then 1 else (if x<2668 then 2 else 3)) else (if x<2758 then 2 else (if x<2800 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2876 : Finset ℕ := ([1590,1594,1614,1650,1652,1692,1702,1708,1746,1748,1752,1764,1768,2606,2646,2650,2652,2662,2668,2702,2738,2740,2758,2762,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2876 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2876 1590 4
  · have he : independentCachedBranchMembers2876.erase 1590=independentCachedBranchMembers2874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2874
  · have he : independentCachedBranchMembers2876.filter (independentCachedEdge 1590)=independentCachedBranchMembers2875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2875
def independentCachedBranchMembers2877 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2877 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2877 2638 5
  · have he : independentCachedBranchMembers2877.erase 2638=independentCachedBranchMembers2865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2865
  · have he : independentCachedBranchMembers2877.filter (independentCachedEdge 2638)=independentCachedBranchMembers2876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2876
def independentCachedBranchMembers2878 : Finset ℕ := ([1590,1642,1708,1720,1734,1746,1748,2606,2618,2620,2646,2662,2674,2710,2738,2740,2762,2764,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2878 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2878 5 (fun x => (if x<2646 then (if x<1746 then (if x<1708 then (if x<1642 then 0 else 0) else (if x<1720 then 0 else (if x<1734 then 1 else 0))) else (if x<2606 then (if x<1748 then 1 else 2) else (if x<2618 then 2 else (if x<2620 then 3 else 1)))) else (if x<2740 then (if x<2674 then (if x<2662 then 1 else 3) else (if x<2710 then 4 else (if x<2738 then 2 else 1))) else (if x<2764 then (if x<2762 then 3 else 4) else (if x<2776 then 2 else (if x<2792 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2879 : Finset ℕ := ([1642,1708,1746,2618,2646,2674,2740,2762,2776] : List ℕ).toFinset
theorem independentCachedBranchBound2879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2879 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2879 4 (fun x => (if x<2646 then (if x<1746 then (if x<1708 then 0 else 0) else (if x<2618 then 1 else 2)) else (if x<2740 then (if x<2674 then 1 else 0) else (if x<2762 then 0 else (if x<2776 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2880 : Finset ℕ := ([1590,1642,1644,1708,1720,1734,1746,1748,2606,2618,2620,2646,2662,2674,2710,2738,2740,2762,2764,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2880 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2880 1644 4
  · have he : independentCachedBranchMembers2880.erase 1644=independentCachedBranchMembers2878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2878
  · have he : independentCachedBranchMembers2880.filter (independentCachedEdge 1644)=independentCachedBranchMembers2879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2879
def independentCachedBranchMembers2881 : Finset ℕ := ([1708,1734,2618,2620,2646,2662,2738,2740,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2881 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2881 4 (fun x => (if x<2662 then (if x<2618 then (if x<1734 then 0 else 0) else (if x<2620 then 1 else (if x<2646 then 0 else 0))) else (if x<2740 then (if x<2738 then 1 else 2) else (if x<2776 then 1 else (if x<2792 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2882 : Finset ℕ := ([1590,1642,1644,1678,1708,1720,1734,1746,1748,2606,2618,2620,2646,2662,2674,2710,2738,2740,2762,2764,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2882 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2882 1678 4
  · have he : independentCachedBranchMembers2882.erase 1678=independentCachedBranchMembers2880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2880
  · have he : independentCachedBranchMembers2882.filter (independentCachedEdge 1678)=independentCachedBranchMembers2881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2881
def independentCachedBranchMembers2883 : Finset ℕ := ([1644,1748,2606,2618,2662,2674,2710,2740,2762,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2883 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2883 4 (fun x => (if x<2674 then (if x<2606 then (if x<1748 then 0 else 0) else (if x<2618 then 0 else (if x<2662 then 1 else 1))) else (if x<2740 then (if x<2710 then 2 else 0) else (if x<2762 then 1 else (if x<2792 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2884 : Finset ℕ := ([1590,1628,1642,1644,1678,1708,1720,1734,1746,1748,2606,2618,2620,2646,2662,2674,2710,2738,2740,2762,2764,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2884 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2884 1628 4
  · have he : independentCachedBranchMembers2884.erase 1628=independentCachedBranchMembers2882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2882
  · have he : independentCachedBranchMembers2884.filter (independentCachedEdge 1628)=independentCachedBranchMembers2883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2883
def independentCachedBranchMembers2885 : Finset ℕ := ([1644,1708,1734,1748,2606,2620,2646,2674,2710,2738,2762,2776] : List ℕ).toFinset
theorem independentCachedBranchBound2885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2885 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2885 4 (fun x => (if x<2646 then (if x<1748 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<2606 then 1 else (if x<2620 then 1 else 0))) else (if x<2738 then (if x<2674 then 1 else (if x<2710 then 2 else 0)) else (if x<2762 then 3 else (if x<2776 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2886 : Finset ℕ := ([1590,1628,1642,1644,1678,1708,1720,1734,1746,1748,1764,2606,2618,2620,2646,2662,2674,2710,2738,2740,2762,2764,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2886 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2886 1764 4
  · have he : independentCachedBranchMembers2886.erase 1764=independentCachedBranchMembers2884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2884
  · have he : independentCachedBranchMembers2886.filter (independentCachedEdge 1764)=independentCachedBranchMembers2885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2885
def independentCachedBranchMembers2887 : Finset ℕ := ([1628,1642,1678,1708,1720,1748,2606,2618,2646,2738,2762,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2887 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2887 4 (fun x => (if x<2606 then (if x<1708 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<1720 then 1 else (if x<1748 then 0 else 1))) else (if x<2738 then (if x<2618 then 1 else (if x<2646 then 2 else 1)) else (if x<2762 then 3 else (if x<2792 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2888 : Finset ℕ := ([1590,1628,1642,1644,1678,1692,1708,1720,1734,1746,1748,1764,2606,2618,2620,2646,2662,2674,2710,2738,2740,2762,2764,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2888 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2888 1692 4
  · have he : independentCachedBranchMembers2888.erase 1692=independentCachedBranchMembers2886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2886
  · have he : independentCachedBranchMembers2888.filter (independentCachedEdge 1692)=independentCachedBranchMembers2887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2887
def independentCachedBranchMembers2889 : Finset ℕ := ([1628,1642,1644,1678,1720,1734,2618,2620,2674,2710,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2889 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2889 4 (fun x => (if x<2618 then (if x<1678 then (if x<1642 then 0 else (if x<1644 then 0 else 1)) else (if x<1720 then 0 else (if x<1734 then 0 else 1))) else (if x<2710 then (if x<2620 then 2 else (if x<2674 then 1 else 3)) else (if x<2776 then 1 else (if x<2792 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2890 : Finset ℕ := ([1590,1614,1628,1642,1644,1678,1692,1708,1720,1734,1746,1748,1764,2606,2618,2620,2646,2662,2674,2710,2738,2740,2762,2764,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2890 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2890 1614 4
  · have he : independentCachedBranchMembers2890.erase 1614=independentCachedBranchMembers2888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2888
  · have he : independentCachedBranchMembers2890.filter (independentCachedEdge 1614)=independentCachedBranchMembers2889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2889
def independentCachedBranchMembers2891 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2891 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2891 2614 5
  · have he : independentCachedBranchMembers2891.erase 2614=independentCachedBranchMembers2877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2877
  · have he : independentCachedBranchMembers2891.filter (independentCachedEdge 2614)=independentCachedBranchMembers2890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2890
def independentCachedBranchMembers2892 : Finset ℕ := ([1614,1650,1652,1678,1714,1720,1746,1748,1752,1764,1768,2614,2618,2646,2650,2652,2662,2668,2710,2714,2716,2730,2732,2758,2762,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2892 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2892 5 (fun x => (if x<2646 then (if x<1746 then (if x<1678 then (if x<1650 then 0 else (if x<1652 then 0 else 1)) else (if x<1714 then 2 else (if x<1720 then 1 else 2))) else (if x<1764 then (if x<1748 then 2 else (if x<1752 then 0 else 1)) else (if x<2614 then (if x<1768 then 2 else 0) else (if x<2618 then 1 else 3)))) else (if x<2716 then (if x<2662 then (if x<2650 then 0 else (if x<2652 then 4 else 1)) else (if x<2710 then (if x<2668 then 3 else 4) else (if x<2714 then 3 else 1))) else (if x<2758 then (if x<2730 then 4 else (if x<2732 then 4 else 2)) else (if x<2764 then (if x<2762 then 2 else 3) else (if x<2800 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2893 : Finset ℕ := ([1614,1650,1678,1714,1748,1752,1764,1768,2614,2618,2652,2668,2716,2732,2758,2762] : List ℕ).toFinset
theorem independentCachedBranchBound2893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2893 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2893 4 (fun x => (if x<2614 then (if x<1748 then (if x<1678 then (if x<1650 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1764 then (if x<1752 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<2716 then (if x<2652 then (if x<2618 then 2 else 3) else (if x<2668 then 2 else 3)) else (if x<2758 then (if x<2732 then 3 else 2) else (if x<2762 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2894 : Finset ℕ := ([1614,1650,1652,1678,1714,1720,1746,1748,1752,1764,1768,2614,2618,2620,2646,2650,2652,2662,2668,2710,2714,2716,2730,2732,2758,2762,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2894 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2894 2620 4
  · have he : independentCachedBranchMembers2894.erase 2620=independentCachedBranchMembers2892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2892
  · have he : independentCachedBranchMembers2894.filter (independentCachedEdge 2620)=independentCachedBranchMembers2893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2893
def independentCachedBranchMembers2895 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2895 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2895 1776 5
  · have he : independentCachedBranchMembers2895.erase 1776=independentCachedBranchMembers2891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2891
  · have he : independentCachedBranchMembers2895.filter (independentCachedEdge 1776)=independentCachedBranchMembers2894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2894
def independentCachedBranchMembers2896 : Finset ℕ := ([1590,1642,1678,1692,1702,1714,1734,1746,1748,1768,2618,2620,2638,2662,2674,2710,2730,2732,2762,2764,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2896 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2896 5 (fun x => (if x<2620 then (if x<1714 then (if x<1678 then (if x<1642 then 0 else 0) else (if x<1692 then 0 else (if x<1702 then 1 else 1))) else (if x<1748 then (if x<1734 then 2 else (if x<1746 then 2 else 0)) else (if x<1768 then 3 else (if x<2618 then 1 else 2)))) else (if x<2732 then (if x<2674 then (if x<2638 then 4 else (if x<2662 then 2 else 4)) else (if x<2710 then 0 else (if x<2730 then 0 else 3))) else (if x<2776 then (if x<2762 then 1 else (if x<2764 then 0 else 3)) else (if x<2786 then 1 else (if x<2800 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2897 : Finset ℕ := ([1642,1714,1746,1768,2618,2674,2730,2762,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2897 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2897 4 (fun x => (if x<2674 then (if x<1746 then (if x<1714 then 0 else 0) else (if x<1768 then 1 else (if x<2618 then 1 else 0))) else (if x<2776 then (if x<2730 then 2 else (if x<2762 then 2 else 1)) else (if x<2786 then 2 else (if x<2800 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2898 : Finset ℕ := ([1590,1642,1644,1678,1692,1702,1714,1734,1746,1748,1768,2618,2620,2638,2662,2674,2710,2730,2732,2762,2764,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2898 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2898 1644 4
  · have he : independentCachedBranchMembers2898.erase 1644=independentCachedBranchMembers2896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2896
  · have he : independentCachedBranchMembers2898.filter (independentCachedEdge 1644)=independentCachedBranchMembers2897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2897
def independentCachedBranchMembers2899 : Finset ℕ := ([1590,1642,1678,1692,1714,1746,2618,2662,2732,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2899 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2899 4 (fun x => (if x<2618 then (if x<1692 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<1714 then 1 else (if x<1746 then 1 else 0))) else (if x<2764 then (if x<2662 then 2 else (if x<2732 then 2 else 2)) else (if x<2786 then 1 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2900 : Finset ℕ := ([1590,1642,1644,1678,1692,1702,1714,1734,1746,1748,1768,2618,2620,2638,2662,2674,2710,2730,2732,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2900 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2900 2788 4
  · have he : independentCachedBranchMembers2900.erase 2788=independentCachedBranchMembers2898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2898
  · have he : independentCachedBranchMembers2900.filter (independentCachedEdge 2788)=independentCachedBranchMembers2899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2899
def independentCachedBranchMembers2901 : Finset ℕ := ([1590,1642,1678,1734,1746,1768,2620,2638,2730,2764,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2901 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2901 4 (fun x => (if x<2620 then (if x<1734 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<1746 then 1 else (if x<1768 then 0 else 1))) else (if x<2764 then (if x<2638 then 2 else (if x<2730 then 2 else 2)) else (if x<2776 then 1 else (if x<2786 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2902 : Finset ℕ := ([1590,1642,1644,1678,1692,1702,1714,1734,1746,1748,1768,2618,2620,2638,2652,2662,2674,2710,2730,2732,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2902 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2902 2652 4
  · have he : independentCachedBranchMembers2902.erase 2652=independentCachedBranchMembers2900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2900
  · have he : independentCachedBranchMembers2902.filter (independentCachedEdge 2652)=independentCachedBranchMembers2901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2901
def independentCachedBranchMembers2903 : Finset ℕ := ([1692,1714,1734,1768,2618,2620,2638,2662,2730,2732,2776,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2903 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2903 4 (fun x => (if x<2638 then (if x<1768 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<2618 then 0 else (if x<2620 then 1 else 2))) else (if x<2732 then (if x<2662 then 1 else (if x<2730 then 2 else 2)) else (if x<2776 then 1 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2904 : Finset ℕ := ([1590,1642,1644,1678,1692,1702,1714,1734,1746,1748,1768,2606,2618,2620,2638,2652,2662,2674,2710,2730,2732,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2904 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2904 2606 4
  · have he : independentCachedBranchMembers2904.erase 2606=independentCachedBranchMembers2902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2902
  · have he : independentCachedBranchMembers2904.filter (independentCachedEdge 2606)=independentCachedBranchMembers2903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2903
def independentCachedBranchMembers2905 : Finset ℕ := ([1590,1644,1678,1692,1714,1734,1748,1768,2618,2638,2652,2674,2732,2762,2776,2788] : List ℕ).toFinset
theorem independentCachedBranchBound2905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2905 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2905 4 (fun x => (if x<2618 then (if x<1714 then (if x<1678 then (if x<1644 then 0 else 0) else (if x<1692 then 0 else 1)) else (if x<1748 then (if x<1734 then 1 else 1) else (if x<1768 then 0 else 1))) else (if x<2732 then (if x<2652 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2776 then (if x<2762 then 2 else 3) else (if x<2788 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2906 : Finset ℕ := ([1590,1642,1644,1678,1692,1702,1714,1734,1746,1748,1768,2606,2618,2620,2638,2650,2652,2662,2674,2710,2730,2732,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2906 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2906 2650 4
  · have he : independentCachedBranchMembers2906.erase 2650=independentCachedBranchMembers2904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2904
  · have he : independentCachedBranchMembers2906.filter (independentCachedEdge 2650)=independentCachedBranchMembers2905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2905
def independentCachedBranchMembers2907 : Finset ℕ := ([1590,1594,1614,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2907 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2907 1686 5
  · have he : independentCachedBranchMembers2907.erase 1686=independentCachedBranchMembers2895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2895
  · have he : independentCachedBranchMembers2907.filter (independentCachedEdge 1686)=independentCachedBranchMembers2906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2906
def independentCachedBranchMembers2908 : Finset ℕ := ([1594,1614,1628,1650,1702,1708,1738,1746,1752,1764,2614,2620,2650,2662,2668,2702,2730,2738,2758,2764,2772,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2908 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2908 5 (fun x => (if x<2620 then (if x<1708 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1650 then 1 else (if x<1702 then 1 else 0))) else (if x<1752 then (if x<1738 then 2 else (if x<1746 then 1 else 0)) else (if x<1764 then 2 else (if x<2614 then 1 else 3)))) else (if x<2738 then (if x<2668 then (if x<2650 then 4 else (if x<2662 then 0 else 4)) else (if x<2702 then 3 else (if x<2730 then 3 else 4))) else (if x<2772 then (if x<2758 then 0 else (if x<2764 then 0 else 1)) else (if x<2786 then 3 else (if x<2800 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2909 : Finset ℕ := ([1594,1614,1650,1738,2614,2620,2702,2738,2758,2764,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2909 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2909 4 (fun x => (if x<2620 then (if x<1650 then (if x<1614 then 0 else 0) else (if x<1738 then 1 else (if x<2614 then 1 else 1))) else (if x<2758 then (if x<2702 then 2 else (if x<2738 then 1 else 0)) else (if x<2764 then 0 else (if x<2800 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2910 : Finset ℕ := ([1594,1614,1628,1642,1650,1702,1708,1738,1746,1752,1764,2614,2620,2650,2662,2668,2702,2730,2738,2758,2764,2772,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2910 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2910 1642 4
  · have he : independentCachedBranchMembers2910.erase 1642=independentCachedBranchMembers2908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2908
  · have he : independentCachedBranchMembers2910.filter (independentCachedEdge 1642)=independentCachedBranchMembers2909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2909
def independentCachedBranchMembers2911 : Finset ℕ := ([1594,1614,1628,1650,1702,1746,2614,2668,2730,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2911 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2911 4 (fun x => (if x<2614 then (if x<1650 then (if x<1614 then 0 else (if x<1628 then 0 else 1)) else (if x<1702 then 1 else (if x<1746 then 0 else 0))) else (if x<2764 then (if x<2668 then 2 else (if x<2730 then 2 else 2)) else (if x<2786 then 1 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2912 : Finset ℕ := ([1594,1614,1628,1642,1650,1702,1708,1738,1746,1752,1764,2614,2620,2650,2662,2668,2702,2730,2738,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2912 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2912 2792 4
  · have he : independentCachedBranchMembers2912.erase 2792=independentCachedBranchMembers2910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2910
  · have he : independentCachedBranchMembers2912.filter (independentCachedEdge 2792)=independentCachedBranchMembers2911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2911
def independentCachedBranchMembers2913 : Finset ℕ := ([1594,1614,1702,1738,1746,1764,2620,2662,2702,2764,2772,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2913 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2913 4 (fun x => (if x<2620 then (if x<1738 then (if x<1614 then 0 else (if x<1702 then 0 else 0)) else (if x<1746 then 1 else (if x<1764 then 0 else 1))) else (if x<2764 then (if x<2662 then 2 else (if x<2702 then 2 else 2)) else (if x<2772 then 1 else (if x<2786 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2914 : Finset ℕ := ([1594,1614,1628,1642,1650,1702,1708,1738,1746,1752,1764,2614,2620,2650,2662,2668,2702,2716,2730,2738,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2914 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2914 2716 4
  · have he : independentCachedBranchMembers2914.erase 2716=independentCachedBranchMembers2912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2912
  · have he : independentCachedBranchMembers2914.filter (independentCachedEdge 2716)=independentCachedBranchMembers2913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2913
def independentCachedBranchMembers2915 : Finset ℕ := ([1628,1650,1738,1764,2614,2620,2662,2668,2702,2730,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2915 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2915 4 (fun x => (if x<2662 then (if x<1764 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<2614 then 0 else (if x<2620 then 1 else 2))) else (if x<2730 then (if x<2668 then 2 else (if x<2702 then 1 else 1)) else (if x<2772 then 2 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2916 : Finset ℕ := ([1594,1614,1628,1642,1650,1702,1708,1738,1746,1752,1764,2606,2614,2620,2650,2662,2668,2702,2716,2730,2738,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2916 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2916 2606 4
  · have he : independentCachedBranchMembers2916.erase 2606=independentCachedBranchMembers2914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2914
  · have he : independentCachedBranchMembers2916.filter (independentCachedEdge 2606)=independentCachedBranchMembers2915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2915
def independentCachedBranchMembers2917 : Finset ℕ := ([1594,1614,1628,1650,1708,1738,1752,1764,2614,2668,2702,2716,2738,2758,2772,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2917 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2917 4 (fun x => (if x<2614 then (if x<1708 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1752 then (if x<1738 then 0 else 1) else (if x<1764 then 0 else 1))) else (if x<2738 then (if x<2702 then (if x<2668 then 2 else 2) else (if x<2716 then 2 else 3)) else (if x<2772 then (if x<2758 then 3 else 3) else (if x<2792 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2918 : Finset ℕ := ([1594,1614,1628,1642,1650,1702,1708,1738,1746,1752,1764,2606,2614,2620,2650,2662,2668,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2918 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2918 2710 4
  · have he : independentCachedBranchMembers2918.erase 2710=independentCachedBranchMembers2916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2916
  · have he : independentCachedBranchMembers2918.filter (independentCachedEdge 2710)=independentCachedBranchMembers2917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2917
def independentCachedBranchMembers2919 : Finset ℕ := ([1590,1594,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2919 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2919 1626 5
  · have he : independentCachedBranchMembers2919.erase 1626=independentCachedBranchMembers2907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2907
  · have he : independentCachedBranchMembers2919.filter (independentCachedEdge 1626)=independentCachedBranchMembers2918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2918
def independentCachedBranchMembers2920 : Finset ℕ := ([1590,1594,1628,1644,1652,1692,1708,1720,1734,1738,1746,2620,2638,2646,2650,2662,2674,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2920 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2920 5 (fun x => (if x<2650 then (if x<1720 then (if x<1644 then (if x<1594 then 0 else (if x<1628 then 1 else 0)) else (if x<1692 then (if x<1652 then 1 else 2) else (if x<1708 then 1 else 0))) else (if x<1746 then (if x<1734 then 2 else (if x<1738 then 0 else 1)) else (if x<2638 then (if x<2620 then 2 else 0) else (if x<2646 then 3 else 0)))) else (if x<2738 then (if x<2702 then (if x<2662 then 4 else (if x<2674 then 4 else 3)) else (if x<2714 then (if x<2710 then 4 else 3) else (if x<2730 then 1 else 3))) else (if x<2776 then (if x<2764 then 4 else (if x<2772 then 0 else 4)) else (if x<2792 then (if x<2788 then 3 else 3) else (if x<2800 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2921 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2921 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2921 1596 5
  · have he : independentCachedBranchMembers2921.erase 1596=independentCachedBranchMembers2919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2919
  · have he : independentCachedBranchMembers2921.filter (independentCachedEdge 1596)=independentCachedBranchMembers2920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2920
def independentCachedBranchMembers2922 : Finset ℕ := ([1642,1652,1678,1702,1720,1746,1768,2606,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2922 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2922 5 (fun x => (if x<2668 then (if x<1746 then (if x<1678 then (if x<1652 then 0 else 0) else (if x<1702 then 1 else (if x<1720 then 0 else 0))) else (if x<2620 then (if x<1768 then 0 else (if x<2606 then 1 else 2)) else (if x<2646 then 3 else (if x<2650 then 2 else 3)))) else (if x<2758 then (if x<2714 then (if x<2674 then 4 else (if x<2710 then 4 else 1)) else (if x<2732 then 2 else (if x<2738 then 1 else 3))) else (if x<2776 then (if x<2762 then 4 else (if x<2772 then 1 else 3)) else (if x<2786 then 4 else (if x<2800 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2923 : Finset ℕ := ([1652,1702,2606,2674,2710,2714,2732,2758,2762,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2923 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2923 4 (fun x => (if x<2714 then (if x<2606 then (if x<1702 then 0 else 0) else (if x<2674 then 1 else (if x<2710 then 1 else 1))) else (if x<2758 then (if x<2732 then 2 else 2) else (if x<2762 then 2 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2924 : Finset ℕ := ([1628,1642,1652,1678,1702,1720,1746,1768,2606,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2924 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2924 1628 4
  · have he : independentCachedBranchMembers2924.erase 1628=independentCachedBranchMembers2922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2922
  · have he : independentCachedBranchMembers2924.filter (independentCachedEdge 1628)=independentCachedBranchMembers2923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2923
def independentCachedBranchMembers2925 : Finset ℕ := ([1642,1720,2646,2668,2710,2732,2762,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2925 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2925 4 (fun x => (if x<2732 then (if x<2646 then (if x<1720 then 0 else 0) else (if x<2668 then 1 else (if x<2710 then 1 else 2))) else (if x<2776 then (if x<2762 then 2 else 1) else (if x<2786 then 2 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2926 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1746,1768,2606,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2926 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2926 1594 4
  · have he : independentCachedBranchMembers2926.erase 1594=independentCachedBranchMembers2924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2924
  · have he : independentCachedBranchMembers2926.filter (independentCachedEdge 1594)=independentCachedBranchMembers2925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2925
def independentCachedBranchMembers2927 : Finset ℕ := ([1594,1652,1702,1768,2606,2620,2646,2674,2710,2738,2762,2776] : List ℕ).toFinset
theorem independentCachedBranchBound2927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2927 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2927 4 (fun x => (if x<2646 then (if x<1768 then (if x<1652 then 0 else (if x<1702 then 0 else 0)) else (if x<2606 then 0 else (if x<2620 then 1 else 2))) else (if x<2738 then (if x<2674 then 1 else (if x<2710 then 2 else 2)) else (if x<2762 then 1 else (if x<2776 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2928 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1746,1764,1768,2606,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2928 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2928 1764 4
  · have he : independentCachedBranchMembers2928.erase 1764=independentCachedBranchMembers2926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2926
  · have he : independentCachedBranchMembers2928.filter (independentCachedEdge 1764)=independentCachedBranchMembers2927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2927
def independentCachedBranchMembers2929 : Finset ℕ := ([1628,1642,1678,1720,2606,2646,2650,2668,2738,2758,2762,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2929 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2929 4 (fun x => (if x<2650 then (if x<1720 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<2606 then 0 else (if x<2646 then 1 else 1))) else (if x<2758 then (if x<2668 then 2 else (if x<2738 then 2 else 1)) else (if x<2762 then 2 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2930 : Finset ℕ := ([1594,1628,1642,1652,1678,1692,1702,1720,1746,1764,1768,2606,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2930 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2930 1692 4
  · have he : independentCachedBranchMembers2930.erase 1692=independentCachedBranchMembers2928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2928
  · have he : independentCachedBranchMembers2930.filter (independentCachedEdge 1692)=independentCachedBranchMembers2929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2929
def independentCachedBranchMembers2931 : Finset ℕ := ([1628,1642,1678,1720,2620,2674,2710,2714,2732,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2931 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2931 4 (fun x => (if x<2710 then (if x<1720 then (if x<1642 then 0 else (if x<1678 then 0 else 0)) else (if x<2620 then 0 else (if x<2674 then 1 else 1))) else (if x<2772 then (if x<2714 then 1 else (if x<2732 then 2 else 2)) else (if x<2776 then 2 else (if x<2786 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2932 : Finset ℕ := ([1594,1614,1628,1642,1652,1678,1692,1702,1720,1746,1764,1768,2606,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2932 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2932 1614 4
  · have he : independentCachedBranchMembers2932.erase 1614=independentCachedBranchMembers2930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2930
  · have he : independentCachedBranchMembers2932.filter (independentCachedEdge 1614)=independentCachedBranchMembers2931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2931
def independentCachedBranchMembers2933 : Finset ℕ := ([1594,1652,1702,1768,2650,2668,2714,2732,2758,2772,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2933 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2933 4 (fun x => (if x<2714 then (if x<1768 then (if x<1652 then 0 else (if x<1702 then 0 else 0)) else (if x<2650 then 0 else (if x<2668 then 1 else 1))) else (if x<2772 then (if x<2732 then 2 else (if x<2758 then 2 else 1)) else (if x<2786 then 2 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2934 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1746,1764,1768,2606,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2934 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2934 1590 4
  · have he : independentCachedBranchMembers2934.erase 1590=independentCachedBranchMembers2932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2932
  · have he : independentCachedBranchMembers2934.filter (independentCachedEdge 1590)=independentCachedBranchMembers2933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2933
def independentCachedBranchMembers2935 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2935 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2935 2770 5
  · have he : independentCachedBranchMembers2935.erase 2770=independentCachedBranchMembers2921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2921
  · have he : independentCachedBranchMembers2935.filter (independentCachedEdge 2770)=independentCachedBranchMembers2934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2934
def independentCachedBranchMembers2936 : Finset ℕ := ([1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2936 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2936 5 (fun x => (if x<2638 then (if x<1738 then (if x<1692 then (if x<1642 then 0 else (if x<1650 then 0 else 1)) else (if x<1714 then (if x<1702 then 2 else 1) else (if x<1734 then 2 else 0))) else (if x<1768 then (if x<1746 then 1 else (if x<1764 then 3 else 2)) else (if x<2614 then (if x<1776 then 3 else 0) else (if x<2618 then 1 else 4)))) else (if x<2714 then (if x<2668 then (if x<2646 then 0 else (if x<2650 then 3 else 1)) else (if x<2702 then (if x<2680 then 3 else 0) else (if x<2710 then 1 else 4))) else (if x<2764 then (if x<2732 then 2 else (if x<2740 then 4 else 2)) else (if x<2776 then (if x<2772 then 2 else 0) else (if x<2786 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2937 : Finset ℕ := ([1628,1692,1734,1738,1746,2638,2646,2650,2702,2710,2714,2764,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound2937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2937 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2937 4 (fun x => (if x<2650 then (if x<1738 then (if x<1692 then 0 else (if x<1734 then 1 else 0)) else (if x<2638 then (if x<1746 then 1 else 2) else (if x<2646 then 0 else 2))) else (if x<2714 then (if x<2702 then 3 else (if x<2710 then 1 else 3)) else (if x<2772 then (if x<2764 then 2 else 3) else (if x<2776 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2938 : Finset ℕ := ([1596,1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2938 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2938 1596 4
  · have he : independentCachedBranchMembers2938.erase 1596=independentCachedBranchMembers2936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2936
  · have he : independentCachedBranchMembers2938.filter (independentCachedEdge 1596)=independentCachedBranchMembers2937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2937
def independentCachedBranchMembers2939 : Finset ℕ := ([1628,1650,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2702,2732,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound2939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2939 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2939 4 (fun x => (if x<2614 then (if x<1734 then (if x<1692 then (if x<1650 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1764 then (if x<1738 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<2702 then (if x<2638 then (if x<2618 then 2 else 3) else (if x<2668 then 2 else 3)) else (if x<2772 then (if x<2732 then 3 else 2) else (if x<2776 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2940 : Finset ℕ := ([1596,1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2606,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2940 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2940 2606 4
  · have he : independentCachedBranchMembers2940.erase 2606=independentCachedBranchMembers2938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2938
  · have he : independentCachedBranchMembers2940.filter (independentCachedEdge 2606)=independentCachedBranchMembers2939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2939
def independentCachedBranchMembers2941 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2941 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2941 1762 5
  · have he : independentCachedBranchMembers2941.erase 1762=independentCachedBranchMembers2935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2935
  · have he : independentCachedBranchMembers2941.filter (independentCachedEdge 1762)=independentCachedBranchMembers2940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2940
def independentCachedBranchMembers2942 : Finset ℕ := ([1594,1628,1644,1650,1678,1692,1708,1714,1734,1738,1748,1752,1764,1768,2606,2620,2646,2650,2662,2680,2710,2714,2730,2740,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2942 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2942 5 (fun x => (if x<1768 then (if x<1708 then (if x<1650 then (if x<1628 then 0 else (if x<1644 then 0 else 1)) else (if x<1678 then 1 else (if x<1692 then 0 else 2))) else (if x<1738 then (if x<1714 then 3 else (if x<1734 then 2 else 1)) else (if x<1752 then (if x<1748 then 2 else 3) else (if x<1764 then 1 else 2)))) else (if x<2710 then (if x<2646 then (if x<2606 then 0 else (if x<2620 then 3 else 4)) else (if x<2662 then (if x<2650 then 3 else 4) else (if x<2680 then 1 else 0))) else (if x<2740 then (if x<2714 then 4 else (if x<2730 then 2 else 0)) else (if x<2786 then (if x<2764 then 2 else 0) else (if x<2800 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2943 : Finset ℕ := ([1628,1644,1678,1714,1734,1738,2620,2680,2710,2714,2730,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2943 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2943 4 (fun x => (if x<2620 then (if x<1714 then (if x<1644 then 0 else (if x<1678 then 1 else 0)) else (if x<1734 then 2 else (if x<1738 then 1 else 2))) else (if x<2714 then (if x<2680 then 1 else (if x<2710 then 0 else 1)) else (if x<2730 then 2 else (if x<2786 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
