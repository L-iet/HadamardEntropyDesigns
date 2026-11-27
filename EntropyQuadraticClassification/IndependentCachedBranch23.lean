/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch22
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers2944 : Finset ℕ := ([1594,1614,1628,1644,1650,1678,1692,1708,1714,1734,1738,1748,1752,1764,1768,2606,2620,2646,2650,2662,2680,2710,2714,2730,2740,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2944 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2944 1614 4
  · have he : independentCachedBranchMembers2944.erase 1614=independentCachedBranchMembers2942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2942
  · have he : independentCachedBranchMembers2944.filter (independentCachedEdge 1614)=independentCachedBranchMembers2943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2943
def independentCachedBranchMembers2945 : Finset ℕ := ([1594,1650,1714,1738,1752,1768,2650,2680,2714,2730,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2945 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2945 4 (fun x => (if x<2650 then (if x<1738 then (if x<1650 then 0 else (if x<1714 then 1 else 2)) else (if x<1752 then 0 else (if x<1768 then 1 else 2))) else (if x<2730 then (if x<2680 then 0 else (if x<2714 then 1 else 3)) else (if x<2786 then 0 else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2946 : Finset ℕ := ([1590,1594,1614,1628,1644,1650,1678,1692,1708,1714,1734,1738,1748,1752,1764,1768,2606,2620,2646,2650,2662,2680,2710,2714,2730,2740,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2946 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2946 1590 4
  · have he : independentCachedBranchMembers2946.erase 1590=independentCachedBranchMembers2944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2944
  · have he : independentCachedBranchMembers2946.filter (independentCachedEdge 1590)=independentCachedBranchMembers2945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2945
def independentCachedBranchMembers2947 : Finset ℕ := ([1590,1594,1614,1628,1678,1692,1764,1768,2606,2620,2646,2650,2710,2714,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2947 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2947 4 (fun x => (if x<2606 then (if x<1678 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1764 then (if x<1692 then 1 else 0) else (if x<1768 then 0 else 1))) else (if x<2710 then (if x<2646 then (if x<2620 then 2 else 3) else (if x<2650 then 2 else 3)) else (if x<2786 then (if x<2714 then 3 else 2) else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2948 : Finset ℕ := ([1590,1594,1614,1628,1644,1650,1678,1692,1708,1714,1734,1738,1748,1752,1764,1768,2606,2620,2646,2650,2662,2680,2710,2714,2730,2740,2764,2770,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2948 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2948 2770 4
  · have he : independentCachedBranchMembers2948.erase 2770=independentCachedBranchMembers2946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2946
  · have he : independentCachedBranchMembers2948.filter (independentCachedEdge 2770)=independentCachedBranchMembers2947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2947
def independentCachedBranchMembers2949 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2949 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2949 1740 5
  · have he : independentCachedBranchMembers2949.erase 1740=independentCachedBranchMembers2941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2941
  · have he : independentCachedBranchMembers2949.filter (independentCachedEdge 1740)=independentCachedBranchMembers2948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2948
def independentCachedBranchMembers2950 : Finset ℕ := ([1594,1652,1678,1692,1714,1720,1738,1746,1752,1764,2614,2620,2638,2674,2680,2714,2732,2740,2758,2764,2772,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2950 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2950 5 (fun x => (if x<2620 then (if x<1720 then (if x<1678 then (if x<1652 then 0 else 0) else (if x<1692 then 1 else (if x<1714 then 0 else 1))) else (if x<1752 then (if x<1738 then 2 else (if x<1746 then 2 else 0)) else (if x<1764 then 1 else (if x<2614 then 1 else 3)))) else (if x<2740 then (if x<2680 then (if x<2638 then 0 else (if x<2674 then 2 else 0)) else (if x<2714 then 3 else (if x<2732 then 0 else 3))) else (if x<2772 then (if x<2758 then 4 else (if x<2764 then 4 else 1)) else (if x<2786 then 0 else (if x<2800 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2951 : Finset ℕ := ([1652,1714,1746,1764,2614,2674,2740,2758,2772,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2951 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2951 4 (fun x => (if x<2674 then (if x<1746 then (if x<1714 then 0 else 0) else (if x<1764 then 1 else (if x<2614 then 1 else 0))) else (if x<2772 then (if x<2740 then 2 else (if x<2758 then 2 else 1)) else (if x<2786 then 3 else (if x<2800 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2952 : Finset ℕ := ([1594,1644,1652,1678,1692,1714,1720,1738,1746,1752,1764,2614,2620,2638,2674,2680,2714,2732,2740,2758,2764,2772,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2952 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2952 1644 4
  · have he : independentCachedBranchMembers2952.erase 1644=independentCachedBranchMembers2950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2950
  · have he : independentCachedBranchMembers2952.filter (independentCachedEdge 1644)=independentCachedBranchMembers2951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2951
def independentCachedBranchMembers2953 : Finset ℕ := ([1594,1652,1678,1692,1714,1746,2614,2680,2732,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2953 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2953 4 (fun x => (if x<2614 then (if x<1692 then (if x<1652 then 0 else (if x<1678 then 0 else 1)) else (if x<1714 then 0 else (if x<1746 then 1 else 0))) else (if x<2764 then (if x<2680 then 2 else (if x<2732 then 2 else 2)) else (if x<2786 then 1 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2954 : Finset ℕ := ([1594,1644,1652,1678,1692,1714,1720,1738,1746,1752,1764,2614,2620,2638,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2954 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2954 2792 4
  · have he : independentCachedBranchMembers2954.erase 2792=independentCachedBranchMembers2952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2952
  · have he : independentCachedBranchMembers2954.filter (independentCachedEdge 2792)=independentCachedBranchMembers2953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2953
def independentCachedBranchMembers2955 : Finset ℕ := ([1594,1678,1720,1738,1746,1764,2620,2638,2680,2764,2772,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2955 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2955 4 (fun x => (if x<2620 then (if x<1738 then (if x<1678 then 0 else (if x<1720 then 0 else 1)) else (if x<1746 then 1 else (if x<1764 then 0 else 1))) else (if x<2764 then (if x<2638 then 2 else (if x<2680 then 2 else 3)) else (if x<2772 then 3 else (if x<2786 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2956 : Finset ℕ := ([1594,1644,1652,1678,1692,1714,1720,1738,1746,1752,1764,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2956 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2956 2652 4
  · have he : independentCachedBranchMembers2956.erase 2652=independentCachedBranchMembers2954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2954
  · have he : independentCachedBranchMembers2956.filter (independentCachedEdge 2652)=independentCachedBranchMembers2955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2955
def independentCachedBranchMembers2957 : Finset ℕ := ([1652,1692,1714,1720,1738,1764,2614,2620,2638,2732,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2957 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2957 4 (fun x => (if x<2614 then (if x<1720 then (if x<1692 then 0 else (if x<1714 then 0 else 0)) else (if x<1738 then 1 else (if x<1764 then 1 else 1))) else (if x<2732 then (if x<2620 then 2 else (if x<2638 then 3 else 2)) else (if x<2772 then 2 else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2958 : Finset ℕ := ([1594,1644,1652,1678,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2958 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2958 2606 4
  · have he : independentCachedBranchMembers2958.erase 2606=independentCachedBranchMembers2956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2956
  · have he : independentCachedBranchMembers2958.filter (independentCachedEdge 2606)=independentCachedBranchMembers2957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2957
def independentCachedBranchMembers2959 : Finset ℕ := ([1644,1678,1692,1714,1746,2606,2620,2638,2652,2674,2732,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2959 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2959 4 (fun x => (if x<2638 then (if x<1714 then (if x<1678 then 0 else (if x<1692 then 0 else 1)) else (if x<2606 then (if x<1746 then 1 else 2) else (if x<2620 then 0 else 2))) else (if x<2732 then (if x<2652 then 3 else (if x<2674 then 1 else 1)) else (if x<2786 then (if x<2764 then 3 else 0) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2960 : Finset ℕ := ([1594,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2960 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2960 1686 4
  · have he : independentCachedBranchMembers2960.erase 1686=independentCachedBranchMembers2958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2958
  · have he : independentCachedBranchMembers2960.filter (independentCachedEdge 1686)=independentCachedBranchMembers2959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2959
def independentCachedBranchMembers2961 : Finset ℕ := ([1594,1738,1746,1752,1764,2614,2620,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2961 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2961 4 (fun x => (if x<2620 then (if x<1752 then (if x<1738 then 0 else (if x<1746 then 0 else 1)) else (if x<1764 then 2 else (if x<2614 then 1 else 0))) else (if x<2772 then (if x<2758 then 3 else (if x<2764 then 0 else 2)) else (if x<2792 then (if x<2786 then 1 else 1) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2962 : Finset ℕ := ([1738,1764,2614,2620,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2962 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2962 3 (fun x => (if x<2620 then (if x<1764 then 0 else (if x<2614 then 0 else 1)) else (if x<2772 then 2 else (if x<2800 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2963 : Finset ℕ := ([1594,1738,1746,1752,1764,2606,2614,2620,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2963 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2963 2606 3
  · have he : independentCachedBranchMembers2963.erase 2606=independentCachedBranchMembers2961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2961
  · have he : independentCachedBranchMembers2963.filter (independentCachedEdge 2606)=independentCachedBranchMembers2962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2962
def independentCachedBranchMembers2964 : Finset ℕ := ([1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2964 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2964 1626 4
  · have he : independentCachedBranchMembers2964.erase 1626=independentCachedBranchMembers2960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2960
  · have he : independentCachedBranchMembers2964.filter (independentCachedEdge 1626)=independentCachedBranchMembers2963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2963
def independentCachedBranchMembers2965 : Finset ℕ := ([1594,1644,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2732,2758,2772,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2965 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2965 4 (fun x => (if x<2614 then (if x<1714 then (if x<1678 then (if x<1644 then 0 else 0) else (if x<1692 then 0 else 1)) else (if x<1752 then (if x<1738 then 1 else 1) else (if x<1764 then 0 else 1))) else (if x<2732 then (if x<2652 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2772 then (if x<2758 then 2 else 3) else (if x<2792 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2966 : Finset ℕ := ([1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2646,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2966 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2966 2646 4
  · have he : independentCachedBranchMembers2966.erase 2646=independentCachedBranchMembers2964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2964
  · have he : independentCachedBranchMembers2966.filter (independentCachedEdge 2646)=independentCachedBranchMembers2965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2965
def independentCachedBranchMembers2967 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2967 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2967 1690 5
  · have he : independentCachedBranchMembers2967.erase 1690=independentCachedBranchMembers2949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2949
  · have he : independentCachedBranchMembers2967.filter (independentCachedEdge 1690)=independentCachedBranchMembers2966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2966
def independentCachedBranchMembers2968 : Finset ℕ := ([1590,1614,1628,1650,1652,1720,1734,1746,1768,2618,2620,2646,2668,2680,2702,2738,2740,2762,2764,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2968 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2968 5 (fun x => (if x<2646 then (if x<1720 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1650 then 1 else (if x<1652 then 1 else 2))) else (if x<1768 then (if x<1734 then 1 else (if x<1746 then 2 else 0)) else (if x<2618 then 2 else (if x<2620 then 3 else 4)))) else (if x<2740 then (if x<2680 then (if x<2668 then 0 else 3) else (if x<2702 then 1 else (if x<2738 then 3 else 0))) else (if x<2776 then (if x<2762 then 3 else (if x<2764 then 0 else 4)) else (if x<2786 then 3 else (if x<2800 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2969 : Finset ℕ := ([1628,1652,1734,1746,2620,2668,2680,2702,2738,2762,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2969 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2969 4 (fun x => (if x<2668 then (if x<1734 then (if x<1652 then 0 else 1) else (if x<1746 then 0 else (if x<2620 then 1 else 0))) else (if x<2738 then (if x<2680 then 1 else (if x<2702 then 2 else 3)) else (if x<2762 then 2 else (if x<2786 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2970 : Finset ℕ := ([1590,1614,1628,1650,1652,1720,1734,1746,1748,1768,2618,2620,2646,2668,2680,2702,2738,2740,2762,2764,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2970 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2970 1748 4
  · have he : independentCachedBranchMembers2970.erase 1748=independentCachedBranchMembers2968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2968
  · have he : independentCachedBranchMembers2970.filter (independentCachedEdge 1748)=independentCachedBranchMembers2969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2969
def independentCachedBranchMembers2971 : Finset ℕ := ([1650,1720,1746,1768,2618,2680,2738,2762,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2971 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2971 4 (fun x => (if x<2680 then (if x<1746 then (if x<1720 then 0 else 0) else (if x<1768 then 1 else (if x<2618 then 1 else 0))) else (if x<2776 then (if x<2738 then 2 else (if x<2762 then 2 else 1)) else (if x<2786 then 3 else (if x<2800 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2972 : Finset ℕ := ([1590,1614,1628,1650,1652,1708,1720,1734,1746,1748,1768,2618,2620,2646,2668,2680,2702,2738,2740,2762,2764,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2972 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2972 1708 4
  · have he : independentCachedBranchMembers2972.erase 1708=independentCachedBranchMembers2970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2970
  · have he : independentCachedBranchMembers2972.filter (independentCachedEdge 1708)=independentCachedBranchMembers2971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2971
def independentCachedBranchMembers2973 : Finset ℕ := ([1590,1614,1628,1650,1720,1746,2618,2668,2740,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2973 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2973 4 (fun x => (if x<2618 then (if x<1650 then (if x<1614 then 0 else (if x<1628 then 0 else 1)) else (if x<1720 then 1 else (if x<1746 then 1 else 0))) else (if x<2764 then (if x<2668 then 2 else (if x<2740 then 2 else 2)) else (if x<2786 then 3 else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2974 : Finset ℕ := ([1590,1614,1628,1650,1652,1708,1720,1734,1746,1748,1768,2618,2620,2646,2668,2680,2702,2738,2740,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2974 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2974 2788 4
  · have he : independentCachedBranchMembers2974.erase 2788=independentCachedBranchMembers2972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2972
  · have he : independentCachedBranchMembers2974.filter (independentCachedEdge 2788)=independentCachedBranchMembers2973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2973
def independentCachedBranchMembers2975 : Finset ℕ := ([1590,1614,1652,1734,1746,1768,2620,2702,2740,2764,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2975 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2975 4 (fun x => (if x<2620 then (if x<1734 then (if x<1614 then 0 else (if x<1652 then 0 else 1)) else (if x<1746 then 1 else (if x<1768 then 0 else 1))) else (if x<2764 then (if x<2702 then 2 else (if x<2740 then 2 else 3)) else (if x<2776 then 3 else (if x<2786 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2976 : Finset ℕ := ([1590,1614,1628,1650,1652,1708,1720,1734,1746,1748,1768,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2976 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2976 2716 4
  · have he : independentCachedBranchMembers2976.erase 2716=independentCachedBranchMembers2974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2974
  · have he : independentCachedBranchMembers2976.filter (independentCachedEdge 2716)=independentCachedBranchMembers2975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2975
def independentCachedBranchMembers2977 : Finset ℕ := ([1628,1650,1652,1720,1734,1768,2618,2620,2668,2702,2776,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2977 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2977 4 (fun x => (if x<2618 then (if x<1720 then (if x<1650 then 0 else (if x<1652 then 0 else 1)) else (if x<1734 then 0 else (if x<1768 then 1 else 1))) else (if x<2702 then (if x<2620 then 2 else (if x<2668 then 3 else 2)) else (if x<2776 then 2 else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2978 : Finset ℕ := ([1590,1614,1628,1650,1652,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2978 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2978 2606 4
  · have he : independentCachedBranchMembers2978.erase 2606=independentCachedBranchMembers2976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2976
  · have he : independentCachedBranchMembers2978.filter (independentCachedEdge 2606)=independentCachedBranchMembers2977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2977
def independentCachedBranchMembers2979 : Finset ℕ := ([1590,1734,1746,1748,1768,2618,2620,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2979 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2979 4 (fun x => (if x<2620 then (if x<1748 then (if x<1734 then 0 else (if x<1746 then 0 else 1)) else (if x<1768 then 2 else (if x<2618 then 1 else 0))) else (if x<2776 then (if x<2762 then 3 else (if x<2764 then 0 else 2)) else (if x<2788 then (if x<2786 then 1 else 1) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2980 : Finset ℕ := ([1734,1768,2618,2620,2776,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2980 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2980 3 (fun x => (if x<2620 then (if x<1768 then 0 else (if x<2618 then 0 else 1)) else (if x<2776 then 2 else (if x<2800 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2981 : Finset ℕ := ([1590,1734,1746,1748,1768,2606,2618,2620,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2981 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2981 2606 3
  · have he : independentCachedBranchMembers2981.erase 2606=independentCachedBranchMembers2979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2979
  · have he : independentCachedBranchMembers2981.filter (independentCachedEdge 2606)=independentCachedBranchMembers2980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2980
def independentCachedBranchMembers2982 : Finset ℕ := ([1590,1614,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2982 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2982 1686 4
  · have he : independentCachedBranchMembers2982.erase 1686=independentCachedBranchMembers2978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2978
  · have he : independentCachedBranchMembers2982.filter (independentCachedEdge 1686)=independentCachedBranchMembers2981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2981
def independentCachedBranchMembers2983 : Finset ℕ := ([1614,1628,1650,1708,1746,2606,2620,2668,2702,2716,2738,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2983 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2983 4 (fun x => (if x<2668 then (if x<1708 then (if x<1628 then 0 else (if x<1650 then 1 else 0)) else (if x<2606 then (if x<1746 then 1 else 2) else (if x<2620 then 2 else 1))) else (if x<2738 then (if x<2702 then 3 else (if x<2716 then 0 else 3)) else (if x<2786 then (if x<2764 then 0 else 1) else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2984 : Finset ℕ := ([1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2716,2738,2740,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2984 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2984 1626 4
  · have he : independentCachedBranchMembers2984.erase 1626=independentCachedBranchMembers2982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2982
  · have he : independentCachedBranchMembers2984.filter (independentCachedEdge 1626)=independentCachedBranchMembers2983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2983
def independentCachedBranchMembers2985 : Finset ℕ := ([1590,1614,1628,1650,1708,1734,1748,1768,2618,2668,2702,2716,2738,2762,2776,2788] : List ℕ).toFinset
theorem independentCachedBranchBound2985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2985 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2985 4 (fun x => (if x<2618 then (if x<1708 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1734 then 0 else 1) else (if x<1768 then 0 else 1))) else (if x<2738 then (if x<2702 then (if x<2668 then 2 else 2) else (if x<2716 then 2 else 3)) else (if x<2776 then (if x<2762 then 3 else 3) else (if x<2788 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2986 : Finset ℕ := ([1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1746,1748,1768,2606,2618,2620,2646,2668,2680,2702,2714,2716,2738,2740,2762,2764,2776,2786,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2986 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2986 2714 4
  · have he : independentCachedBranchMembers2986.erase 2714=independentCachedBranchMembers2984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2984
  · have he : independentCachedBranchMembers2986.filter (independentCachedEdge 2714)=independentCachedBranchMembers2985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2985
def independentCachedBranchMembers2987 : Finset ℕ := ([1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2987 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2987 1622 5
  · have he : independentCachedBranchMembers2987.erase 1622=independentCachedBranchMembers2967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2967
  · have he : independentCachedBranchMembers2987.filter (independentCachedEdge 1622)=independentCachedBranchMembers2986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2986
def independentCachedBranchMembers2988 : Finset ℕ := ([1590,1594,1614,1642,1644,1678,1702,1708,1746,1748,1752,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2988 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2988 5 (fun x => (if x<2650 then (if x<1702 then (if x<1642 then (if x<1594 then 0 else (if x<1614 then 1 else 0)) else (if x<1644 then 2 else (if x<1678 then 1 else 1))) else (if x<1748 then (if x<1708 then 2 else (if x<1746 then 0 else 2)) else (if x<2606 then (if x<1752 then 0 else 1) else (if x<2646 then 0 else 0)))) else (if x<2738 then (if x<2680 then (if x<2652 then 2 else (if x<2674 then 3 else 3)) else (if x<2714 then (if x<2710 then 1 else 2) else (if x<2716 then 1 else 4))) else (if x<2762 then (if x<2740 then 4 else (if x<2758 then 0 else 3)) else (if x<2788 then (if x<2764 then 4 else 0) else (if x<2792 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2989 : Finset ℕ := ([1614,1678,1746,1748,1752,2646,2650,2652,2710,2714,2716,2758,2762,2764] : List ℕ).toFinset
theorem independentCachedBranchBound2989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2989 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2989 4 (fun x => (if x<2652 then (if x<1748 then (if x<1678 then 0 else (if x<1746 then 1 else 0)) else (if x<2646 then (if x<1752 then 1 else 2) else (if x<2650 then 0 else 2))) else (if x<2716 then (if x<2710 then 3 else (if x<2714 then 1 else 3)) else (if x<2762 then (if x<2758 then 2 else 3) else (if x<2764 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2990 : Finset ℕ := ([1590,1594,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2990 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2990 1776 4
  · have he : independentCachedBranchMembers2990.erase 1776=independentCachedBranchMembers2988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2988
  · have he : independentCachedBranchMembers2990.filter (independentCachedEdge 1776)=independentCachedBranchMembers2989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2989
def independentCachedBranchMembers2991 : Finset ℕ := ([1590,1594,1644,1708,2650,2674,2710,2738,2764,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2991 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2991 4 (fun x => (if x<2674 then (if x<1644 then (if x<1594 then 0 else 1) else (if x<1708 then 0 else (if x<2650 then 1 else 1))) else (if x<2764 then (if x<2710 then 2 else (if x<2738 then 0 else 3)) else (if x<2788 then 0 else (if x<2792 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2992 : Finset ℕ := ([1644,1708,2764,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2992 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2992 3 (fun x => (if x<2764 then (if x<1708 then 0 else 1) else (if x<2788 then 0 else (if x<2792 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2993 : Finset ℕ := ([1590,1594,1644,1708,1746,2650,2674,2710,2738,2764,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2993 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2993 1746 3
  · have he : independentCachedBranchMembers2993.erase 1746=independentCachedBranchMembers2991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2991
  · have he : independentCachedBranchMembers2993.filter (independentCachedEdge 1746)=independentCachedBranchMembers2992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2992
def independentCachedBranchMembers2994 : Finset ℕ := ([1590,1708,2650,2710,2738,2788] : List ℕ).toFinset
theorem independentCachedBranchBound2994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2994 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2994 3 (fun x => (if x<2710 then (if x<1708 then 0 else (if x<2650 then 0 else 1)) else (if x<2738 then 1 else (if x<2788 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2995 : Finset ℕ := ([1590,1594,1644,1708,1746,2650,2674,2710,2714,2738,2764,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2995 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2995 2714 3
  · have he : independentCachedBranchMembers2995.erase 2714=independentCachedBranchMembers2993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2993
  · have he : independentCachedBranchMembers2995.filter (independentCachedEdge 2714)=independentCachedBranchMembers2994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2994
def independentCachedBranchMembers2996 : Finset ℕ := ([1594,1644,2650,2674,2710,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2996 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2996 3 (fun x => (if x<2674 then (if x<1644 then 0 else (if x<2650 then 0 else 1)) else (if x<2710 then 2 else (if x<2792 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2997 : Finset ℕ := ([1590,1594,1644,1708,1746,2646,2650,2674,2710,2714,2738,2764,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2997 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2997 2646 3
  · have he : independentCachedBranchMembers2997.erase 2646=independentCachedBranchMembers2995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2995
  · have he : independentCachedBranchMembers2997.filter (independentCachedEdge 2646)=independentCachedBranchMembers2996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2996
def independentCachedBranchMembers2998 : Finset ℕ := ([1590,1594,1596,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2998 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2998 1596 4
  · have he : independentCachedBranchMembers2998.erase 1596=independentCachedBranchMembers2990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2990
  · have he : independentCachedBranchMembers2998.filter (independentCachedEdge 1596)=independentCachedBranchMembers2997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2997
def independentCachedBranchMembers2999 : Finset ℕ := ([1590,1594,1614,1644,1678,1708,1748,1752,2652,2674,2716,2738,2758,2762,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound2999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2999 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2999 4 (fun x => (if x<2652 then (if x<1678 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1644 then 0 else 1)) else (if x<1748 then (if x<1708 then 1 else 0) else (if x<1752 then 0 else 1))) else (if x<2758 then (if x<2716 then (if x<2674 then 2 else 2) else (if x<2738 then 3 else 3)) else (if x<2788 then (if x<2762 then 2 else 3) else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3000 : Finset ℕ := ([1590,1594,1596,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2786,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound3000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3000 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3000 2786 4
  · have he : independentCachedBranchMembers3000.erase 2786=independentCachedBranchMembers2998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2998
  · have he : independentCachedBranchMembers3000.filter (independentCachedEdge 2786)=independentCachedBranchMembers2999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2999
def independentCachedBranchMembers3001 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound3001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3001 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3001 1582 5
  · have he : independentCachedBranchMembers3001.erase 1582=independentCachedBranchMembers2987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2987
  · have he : independentCachedBranchMembers3001.filter (independentCachedEdge 1582)=independentCachedBranchMembers3000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3000
def independentCachedBranchMembers3002 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3002 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3002 3072 6
  · have he : independentCachedBranchMembers3002.erase 3072=independentCachedBranchMembers2796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2796
  · have he : independentCachedBranchMembers3002.filter (independentCachedEdge 3072)=independentCachedBranchMembers3001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3001
def independentCachedBranchMembers3003 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1708,1720,1738,1752,1768,2620,2638,2650,2668,2680,2716,2730,2764,2776,2792,3118,3164,3178,3192,3226,3244,3256,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3003 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3003 6 (fun x => (if x<2668 then (if x<1708 then (if x<1594 then (if x<250 then (if x<72 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1642 then (if x<1628 then 0 else 1) else (if x<1644 then 2 else 3))) else (if x<1768 then (if x<1738 then (if x<1720 then 2 else 3) else (if x<1752 then 3 else 2)) else (if x<2638 then (if x<2620 then 0 else 3) else (if x<2650 then 3 else 2)))) else (if x<3164 then (if x<2764 then (if x<2716 then (if x<2680 then 1 else 0) else (if x<2730 then 2 else 0)) else (if x<2792 then (if x<2776 then 4 else 1) else (if x<3118 then 2 else 5))) else (if x<3244 then (if x<3192 then (if x<3178 then 4 else 0) else (if x<3226 then 1 else 5)) else (if x<3274 then (if x<3256 then 4 else 0) else (if x<3276 then 4 else (if x<3304 then 1 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3004 : Finset ℕ := ([40,72,250,252,1708,1738,2620,2650,2668,2776,2792,3164,3178,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3004 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3004 5 (fun x => (if x<2650 then (if x<252 then (if x<72 then 0 else (if x<250 then 1 else 0)) else (if x<1738 then (if x<1708 then 1 else 2) else (if x<2620 then 2 else 2))) else (if x<3164 then (if x<2776 then (if x<2668 then 2 else 1) else (if x<2792 then 1 else 0)) else (if x<3256 then (if x<3178 then 1 else 0) else (if x<3304 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3005 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2620,2638,2650,2668,2680,2716,2730,2764,2776,2792,3118,3164,3178,3192,3226,3244,3256,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3005 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3005 1678 5
  · have he : independentCachedBranchMembers3005.erase 1678=independentCachedBranchMembers3003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3003
  · have he : independentCachedBranchMembers3005.filter (independentCachedEdge 1678)=independentCachedBranchMembers3004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3004
def independentCachedBranchMembers3006 : Finset ℕ := ([40,72,250,252,1642,1644,1708,1720,1738,1752,2668,2680,2730,2764,2776,3118,3164,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3006 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3006 5 (fun x => (if x<1752 then (if x<1642 then (if x<250 then (if x<72 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1708 then (if x<1644 then 0 else 1) else (if x<1720 then 2 else (if x<1738 then 0 else 2)))) else (if x<2776 then (if x<2680 then (if x<2668 then 1 else 3) else (if x<2730 then 0 else (if x<2764 then 0 else 1))) else (if x<3164 then (if x<3118 then 3 else 3) else (if x<3226 then 1 else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3007 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2620,2638,2650,2668,2680,2716,2730,2764,2776,2792,3102,3118,3164,3178,3192,3226,3244,3256,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3007 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3007 3102 5
  · have he : independentCachedBranchMembers3007.erase 3102=independentCachedBranchMembers3005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3005
  · have he : independentCachedBranchMembers3007.filter (independentCachedEdge 3102)=independentCachedBranchMembers3006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3006
def independentCachedBranchMembers3008 : Finset ℕ := ([40,1594,1642,1644,1678,1708,1752,2620,2638,2668,2730,2776,3118,3164,3192,3226,3256,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3008 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3008 5 (fun x => (if x<2730 then (if x<1708 then (if x<1642 then (if x<1594 then 0 else 0) else (if x<1644 then 1 else (if x<1678 then 0 else 1))) else (if x<2620 then (if x<1752 then 2 else 1) else (if x<2638 then 0 else (if x<2668 then 3 else 2)))) else (if x<3226 then (if x<3118 then (if x<2776 then 2 else 3) else (if x<3164 then 0 else (if x<3192 then 3 else 0))) else (if x<3274 then (if x<3256 then 4 else 3) else (if x<3276 then 1 else (if x<3304 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3009 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2620,2638,2650,2668,2680,2716,2730,2764,2776,2792,3102,3118,3164,3178,3192,3226,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3009 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3009 3288 5
  · have he : independentCachedBranchMembers3009.erase 3288=independentCachedBranchMembers3007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3007
  · have he : independentCachedBranchMembers3009.filter (independentCachedEdge 3288)=independentCachedBranchMembers3008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3008
def independentCachedBranchMembers3010 : Finset ℕ := ([250,1594,1644,1678,1720,1738,1752,2650,2668,2716,2730,2776,3118,3164,3178,3192,3226,3244,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3010 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3010 5 (fun x => (if x<2730 then (if x<1738 then (if x<1644 then (if x<1594 then 0 else 0) else (if x<1678 then 1 else (if x<1720 then 1 else 1))) else (if x<2650 then (if x<1752 then 0 else 2) else (if x<2668 then 0 else (if x<2716 then 3 else 2)))) else (if x<3192 then (if x<3118 then (if x<2776 then 0 else 3) else (if x<3164 then 3 else (if x<3178 then 2 else 0))) else (if x<3244 then (if x<3226 then 1 else 0) else (if x<3276 then 1 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3011 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2620,2638,2650,2668,2680,2716,2730,2764,2776,2792,3102,3118,3164,3178,3180,3192,3226,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3011 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3011 3180 5
  · have he : independentCachedBranchMembers3011.erase 3180=independentCachedBranchMembers3009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3009
  · have he : independentCachedBranchMembers3011.filter (independentCachedEdge 3180)=independentCachedBranchMembers3010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3010
def independentCachedBranchMembers3012 : Finset ℕ := ([40,72,252,1628,1642,1708,1768,2650,2668,2716,2730,2776,3118,3164,3178,3192,3226,3244,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3012 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3012 5 (fun x => (if x<2730 then (if x<1708 then (if x<252 then (if x<72 then 0 else 1) else (if x<1628 then 0 else (if x<1642 then 1 else 1))) else (if x<2650 then (if x<1768 then 0 else 2) else (if x<2668 then 1 else (if x<2716 then 0 else 3)))) else (if x<3192 then (if x<3118 then (if x<2776 then 2 else 2) else (if x<3164 then 4 else (if x<3178 then 3 else 3))) else (if x<3244 then (if x<3226 then 1 else 3) else (if x<3276 then 3 else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3013 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2620,2638,2650,2668,2680,2714,2716,2730,2764,2776,2792,3102,3118,3164,3178,3180,3192,3226,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3013 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3013 2714 5
  · have he : independentCachedBranchMembers3013.erase 2714=independentCachedBranchMembers3011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3011
  · have he : independentCachedBranchMembers3013.filter (independentCachedEdge 2714)=independentCachedBranchMembers3012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3012
def independentCachedBranchMembers3014 : Finset ℕ := ([72,250,252,1628,1720,1738,1768,2620,2638,2668,2730,2776,3118,3164,3192,3226,3256,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3014 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3014 5 (fun x => (if x<2730 then (if x<1738 then (if x<252 then (if x<250 then 0 else 0) else (if x<1628 then 1 else (if x<1720 then 1 else 1))) else (if x<2620 then (if x<1768 then 0 else 2) else (if x<2638 then 1 else (if x<2668 then 3 else 2)))) else (if x<3226 then (if x<3118 then (if x<2776 then 2 else 0) else (if x<3164 then 3 else (if x<3192 then 3 else 1))) else (if x<3274 then (if x<3256 then 4 else 3) else (if x<3276 then 3 else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3015 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2620,2638,2650,2668,2680,2714,2716,2730,2764,2776,2792,3102,3118,3164,3178,3180,3192,3226,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3015 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3015 2606 5
  · have he : independentCachedBranchMembers3015.erase 2606=independentCachedBranchMembers3013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3013
  · have he : independentCachedBranchMembers3015.filter (independentCachedEdge 2606)=independentCachedBranchMembers3014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3014
def independentCachedBranchMembers3016 : Finset ℕ := ([72,252,1644,1752,2620,2638,2650,2668,2680,2716,2730,2764,2776,3118,3164,3178,3226,3244,3256,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3016 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3016 5 (fun x => (if x<2730 then (if x<2638 then (if x<1644 then (if x<252 then 0 else 0) else (if x<1752 then 0 else (if x<2620 then 0 else 1))) else (if x<2668 then (if x<2650 then 1 else 2) else (if x<2680 then 2 else (if x<2716 then 0 else 2)))) else (if x<3178 then (if x<2776 then (if x<2764 then 1 else 0) else (if x<3118 then 1 else (if x<3164 then 1 else 0))) else (if x<3256 then (if x<3226 then 2 else (if x<3244 then 2 else 2)) else (if x<3274 then 1 else (if x<3304 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3017 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2620,2638,2650,2668,2680,2714,2716,2730,2764,2776,2792,3102,3118,3164,3178,3180,3192,3226,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3017 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3017 3242 5
  · have he : independentCachedBranchMembers3017.erase 3242=independentCachedBranchMembers3015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3015
  · have he : independentCachedBranchMembers3017.filter (independentCachedEdge 3242)=independentCachedBranchMembers3016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3016
def independentCachedBranchMembers3018 : Finset ℕ := ([40,252,1644,1678,1720,1768,2606,2620,2650,2668,2716,2730,2764,2792,3102,3164,3178,3192,3226,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3018 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3018 5 (fun x => (if x<2730 then (if x<1768 then (if x<1644 then (if x<252 then 0 else 0) else (if x<1678 then 0 else (if x<1720 then 1 else 0))) else (if x<2650 then (if x<2606 then 1 else (if x<2620 then 2 else 0)) else (if x<2668 then 2 else (if x<2716 then 3 else 2)))) else (if x<3178 then (if x<2792 then (if x<2764 then 1 else 1) else (if x<3102 then 0 else (if x<3164 then 2 else 3))) else (if x<3244 then (if x<3192 then 2 else (if x<3226 then 0 else 3)) else (if x<3274 then 0 else (if x<3288 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3019 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2620,2638,2650,2668,2680,2714,2716,2730,2764,2776,2792,3102,3118,3162,3164,3178,3180,3192,3226,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3019 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3019 3162 5
  · have he : independentCachedBranchMembers3019.erase 3162=independentCachedBranchMembers3017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3017
  · have he : independentCachedBranchMembers3019.filter (independentCachedEdge 3162)=independentCachedBranchMembers3018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3018
def independentCachedBranchMembers3020 : Finset ℕ := ([72,250,1642,1678,1752,1768,2620,2638,2650,2714,2730,2764,2776,2792,3102,3118,3164,3180,3192,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3020 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3020 5 (fun x => (if x<2764 then (if x<1768 then (if x<1642 then (if x<250 then 0 else 0) else (if x<1678 then 0 else (if x<1752 then 1 else 0))) else (if x<2650 then (if x<2620 then 1 else (if x<2638 then 2 else 2)) else (if x<2714 then 0 else (if x<2730 then 2 else 1)))) else (if x<3164 then (if x<2792 then (if x<2776 then 1 else 3) else (if x<3102 then 0 else (if x<3118 then 2 else 3))) else (if x<3244 then (if x<3180 then 3 else (if x<3192 then 2 else 0)) else (if x<3256 then 1 else (if x<3274 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3021 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2620,2638,2650,2668,2680,2714,2716,2730,2764,2776,2792,3102,3118,3132,3162,3164,3178,3180,3192,3226,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3021 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3021 3132 5
  · have he : independentCachedBranchMembers3021.erase 3132=independentCachedBranchMembers3019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3019
  · have he : independentCachedBranchMembers3021.filter (independentCachedEdge 3132)=independentCachedBranchMembers3020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3020
def independentCachedBranchMembers3022 : Finset ℕ := ([72,252,1594,1628,1644,1678,1708,1738,1752,1768,2606,2620,2650,2680,2714,2730,2764,3164,3180,3244,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3022 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3022 5 (fun x => (if x<2620 then (if x<1678 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1628 then 1 else (if x<1644 then 0 else 1))) else (if x<1752 then (if x<1708 then 1 else (if x<1738 then 2 else 2)) else (if x<1768 then 1 else (if x<2606 then 0 else 1)))) else (if x<3164 then (if x<2714 then (if x<2650 then 2 else (if x<2680 then 2 else 0)) else (if x<2730 then 1 else (if x<2764 then 2 else 0))) else (if x<3274 then (if x<3180 then 3 else (if x<3244 then 0 else 3)) else (if x<3288 then 3 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3023 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2618,2620,2638,2650,2668,2680,2714,2716,2730,2764,2776,2792,3102,3118,3132,3162,3164,3178,3180,3192,3226,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3023 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3023 2618 5
  · have he : independentCachedBranchMembers3023.erase 2618=independentCachedBranchMembers3021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3021
  · have he : independentCachedBranchMembers3023.filter (independentCachedEdge 2618)=independentCachedBranchMembers3022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3022
def independentCachedBranchMembers3024 : Finset ℕ := ([40,252,1594,1628,1644,1708,1720,1738,2620,2638,2650,2714,2730,2764,2776,2792,3102,3118,3164,3180,3192,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3024 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3024 5 (fun x => (if x<2730 then (if x<1720 then (if x<1628 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 1 else (if x<1708 then 0 else 1))) else (if x<2638 then (if x<1738 then 0 else (if x<2620 then 1 else 0)) else (if x<2650 then 2 else (if x<2714 then 1 else 2)))) else (if x<3164 then (if x<2792 then (if x<2764 then 1 else (if x<2776 then 1 else 3)) else (if x<3102 then 0 else (if x<3118 then 2 else 3))) else (if x<3244 then (if x<3180 then 3 else (if x<3192 then 2 else 0)) else (if x<3256 then 0 else (if x<3274 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3025 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2618,2620,2638,2650,2668,2680,2714,2716,2730,2762,2764,2776,2792,3102,3118,3132,3162,3164,3178,3180,3192,3226,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3025 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3025 2762 5
  · have he : independentCachedBranchMembers3025.erase 2762=independentCachedBranchMembers3023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3023
  · have he : independentCachedBranchMembers3025.filter (independentCachedEdge 2762)=independentCachedBranchMembers3024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3024
def independentCachedBranchMembers3026 : Finset ℕ := ([72,250,1594,1628,1642,1708,1738,1752,2606,2620,2650,2668,2716,2730,2764,2792,3102,3164,3178,3192,3226,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3026 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3026 5 (fun x => (if x<2716 then (if x<1738 then (if x<1628 then (if x<250 then 0 else (if x<1594 then 0 else 1)) else (if x<1642 then 1 else (if x<1708 then 0 else 1))) else (if x<2620 then (if x<1752 then 1 else (if x<2606 then 0 else 2)) else (if x<2650 then 1 else (if x<2668 then 0 else 3)))) else (if x<3178 then (if x<2792 then (if x<2730 then 2 else (if x<2764 then 1 else 1)) else (if x<3102 then 0 else (if x<3164 then 2 else 3))) else (if x<3244 then (if x<3192 then 2 else (if x<3226 then 0 else 3)) else (if x<3274 then 2 else (if x<3288 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3027 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2618,2620,2638,2650,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3162,3164,3178,3180,3192,3226,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3027 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3027 2732 5
  · have he : independentCachedBranchMembers3027.erase 2732=independentCachedBranchMembers3025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3025
  · have he : independentCachedBranchMembers3027.filter (independentCachedEdge 2732)=independentCachedBranchMembers3026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3026
def independentCachedBranchMembers3028 : Finset ℕ := ([40,252,1594,1628,1642,1708,1738,1752,2620,2650,2668,2716,2730,2792,3118,3132,3162,3256,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3028 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3028 5 (fun x => (if x<2668 then (if x<1708 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1628 then 1 else (if x<1642 then 1 else 2))) else (if x<1752 then (if x<1738 then 0 else 1) else (if x<2620 then 2 else (if x<2650 then 0 else 1)))) else (if x<3132 then (if x<2730 then (if x<2716 then 3 else 2) else (if x<2792 then 1 else (if x<3118 then 0 else 3))) else (if x<3256 then (if x<3162 then 4 else 4) else (if x<3276 then 0 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3029 : Finset ℕ := ([252,1752,2620,2650,2668,2716,2730,3118,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3029 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3029 4 (fun x => (if x<2716 then (if x<2620 then (if x<1752 then 0 else 0) else (if x<2650 then 1 else (if x<2668 then 1 else 2))) else (if x<3118 then (if x<2730 then 0 else 1) else (if x<3256 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3030 : Finset ℕ := ([40,252,1594,1628,1642,1708,1738,1752,2620,2650,2668,2716,2730,2792,3118,3132,3162,3242,3256,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3030 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3030 3242 4
  · have he : independentCachedBranchMembers3030.erase 3242=independentCachedBranchMembers3028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3028
  · have he : independentCachedBranchMembers3030.filter (independentCachedEdge 3242)=independentCachedBranchMembers3029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3029
def independentCachedBranchMembers3031 : Finset ℕ := ([1594,1738,1752,2650,2668,2716,2730,3118,3132,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3031 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3031 4 (fun x => (if x<2716 then (if x<1752 then (if x<1738 then 0 else 0) else (if x<2650 then 1 else (if x<2668 then 0 else 2))) else (if x<3132 then (if x<2730 then 1 else (if x<3118 then 0 else 2)) else (if x<3276 then 3 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3032 : Finset ℕ := ([40,252,1594,1628,1642,1708,1738,1752,2620,2650,2668,2716,2730,2792,3118,3132,3162,3180,3242,3256,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3032 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3032 3180 4
  · have he : independentCachedBranchMembers3032.erase 3180=independentCachedBranchMembers3030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3030
  · have he : independentCachedBranchMembers3032.filter (independentCachedEdge 3180)=independentCachedBranchMembers3031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3031
def independentCachedBranchMembers3033 : Finset ℕ := ([40,1642,2668,2716,2792,3118,3132,3162,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3033 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3033 4 (fun x => (if x<3118 then (if x<2668 then (if x<1642 then 0 else 0) else (if x<2716 then 0 else (if x<2792 then 1 else 1))) else (if x<3242 then (if x<3132 then 0 else (if x<3162 then 2 else 2)) else (if x<3256 then 2 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3034 : Finset ℕ := ([40,252,1594,1628,1642,1708,1738,1752,2620,2650,2668,2716,2730,2764,2792,3118,3132,3162,3180,3242,3256,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3034 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3034 2764 4
  · have he : independentCachedBranchMembers3034.erase 2764=independentCachedBranchMembers3032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3032
  · have he : independentCachedBranchMembers3034.filter (independentCachedEdge 2764)=independentCachedBranchMembers3033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3033
def independentCachedBranchMembers3035 : Finset ℕ := ([252,1628,1738,2620,2668,2730,3118,3162,3256,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3035 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3035 4 (fun x => (if x<2730 then (if x<1738 then (if x<1628 then 0 else 0) else (if x<2620 then 1 else (if x<2668 then 0 else 2))) else (if x<3256 then (if x<3118 then 1 else (if x<3162 then 2 else 3)) else (if x<3276 then 3 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3036 : Finset ℕ := ([40,252,1594,1628,1642,1708,1738,1752,2606,2620,2650,2668,2716,2730,2764,2792,3118,3132,3162,3180,3242,3256,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3036 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3036 2606 4
  · have he : independentCachedBranchMembers3036.erase 2606=independentCachedBranchMembers3034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3034
  · have he : independentCachedBranchMembers3036.filter (independentCachedEdge 2606)=independentCachedBranchMembers3035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3035
def independentCachedBranchMembers3037 : Finset ℕ := ([40,72,250,252,1594,1626,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2618,2620,2638,2650,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3162,3164,3178,3180,3192,3226,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3037 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3037 1626 5
  · have he : independentCachedBranchMembers3037.erase 1626=independentCachedBranchMembers3027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3027
  · have he : independentCachedBranchMembers3037.filter (independentCachedEdge 1626)=independentCachedBranchMembers3036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3036
def independentCachedBranchMembers3038 : Finset ℕ := ([72,250,1594,1628,1644,1708,1720,1738,2620,2638,2650,2730,2776,2792,3132,3162,3178,3226,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3038 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3038 5 (fun x => (if x<2650 then (if x<1708 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 1 else (if x<1644 then 1 else 2))) else (if x<1738 then (if x<1720 then 1 else 2) else (if x<2620 then 0 else (if x<2638 then 1 else 2)))) else (if x<3162 then (if x<2776 then (if x<2730 then 0 else 1) else (if x<2792 then 3 else (if x<3132 then 0 else 4))) else (if x<3226 then (if x<3178 then 3 else 0) else (if x<3276 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3039 : Finset ℕ := ([72,1644,2620,2638,2650,2730,2776,3178,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3039 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3039 4 (fun x => (if x<2730 then (if x<2620 then (if x<1644 then 0 else 0) else (if x<2638 then 1 else (if x<2650 then 0 else 1))) else (if x<3178 then (if x<2776 then 1 else 2) else (if x<3226 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3040 : Finset ℕ := ([72,250,1594,1628,1644,1708,1720,1738,2620,2638,2650,2730,2776,2792,3132,3162,3178,3226,3242,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3040 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3040 3242 4
  · have he : independentCachedBranchMembers3040.erase 3242=independentCachedBranchMembers3038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3038
  · have he : independentCachedBranchMembers3040.filter (independentCachedEdge 3242)=independentCachedBranchMembers3039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3039
def independentCachedBranchMembers3041 : Finset ℕ := ([1594,1644,1708,2620,2638,2730,2776,3162,3226,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3041 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3041 4 (fun x => (if x<2730 then (if x<1708 then (if x<1644 then 0 else 0) else (if x<2620 then 1 else (if x<2638 then 0 else 2))) else (if x<3226 then (if x<2776 then 1 else (if x<3162 then 2 else 2)) else (if x<3276 then 3 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3042 : Finset ℕ := ([72,250,1594,1628,1644,1708,1720,1738,2620,2638,2650,2730,2776,2792,3132,3162,3178,3226,3242,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3042 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3042 3288 4
  · have he : independentCachedBranchMembers3042.erase 3288=independentCachedBranchMembers3040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3040
  · have he : independentCachedBranchMembers3042.filter (independentCachedEdge 3288)=independentCachedBranchMembers3041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3041
def independentCachedBranchMembers3043 : Finset ℕ := ([250,1720,2638,2776,2792,3132,3162,3178,3226,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3043 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3043 4 (fun x => (if x<3132 then (if x<2638 then (if x<1720 then 0 else 0) else (if x<2776 then 1 else (if x<2792 then 0 else 1))) else (if x<3226 then (if x<3162 then 2 else (if x<3178 then 2 else 1)) else (if x<3242 then 0 else (if x<3276 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3044 : Finset ℕ := ([72,250,1594,1628,1644,1708,1720,1738,2620,2638,2650,2730,2764,2776,2792,3132,3162,3178,3226,3242,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3044 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3044 2764 4
  · have he : independentCachedBranchMembers3044.erase 2764=independentCachedBranchMembers3042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3042
  · have he : independentCachedBranchMembers3044.filter (independentCachedEdge 2764)=independentCachedBranchMembers3043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3043
def independentCachedBranchMembers3045 : Finset ℕ := ([72,1628,1708,2650,2730,2776,3132,3178,3226,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3045 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3045 4 (fun x => (if x<2776 then (if x<1708 then (if x<1628 then 0 else 0) else (if x<2650 then 1 else (if x<2730 then 0 else 1))) else (if x<3226 then (if x<3132 then 2 else (if x<3178 then 3 else 3)) else (if x<3276 then 2 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3046 : Finset ℕ := ([72,250,1594,1628,1644,1708,1720,1738,2620,2638,2650,2714,2730,2764,2776,2792,3132,3162,3178,3226,3242,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3046 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3046 2714 4
  · have he : independentCachedBranchMembers3046.erase 2714=independentCachedBranchMembers3044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3044
  · have he : independentCachedBranchMembers3046.filter (independentCachedEdge 2714)=independentCachedBranchMembers3045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3045
def independentCachedBranchMembers3047 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2618,2620,2638,2650,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3162,3164,3178,3180,3192,3226,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3047 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3047 1596 5
  · have he : independentCachedBranchMembers3047.erase 1596=independentCachedBranchMembers3037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3037
  · have he : independentCachedBranchMembers3047.filter (independentCachedEdge 1596)=independentCachedBranchMembers3046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3046
def independentCachedBranchMembers3048 : Finset ℕ := ([40,72,250,1594,1626,1644,1768,2606,2618,2638,2650,2668,2680,2716,2730,2762,2792,3102,3132,3164,3178,3226,3244,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3048 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3048 5 (fun x => (if x<2716 then (if x<1768 then (if x<1594 then (if x<72 then 0 else (if x<250 then 1 else 0)) else (if x<1626 then 0 else (if x<1644 then 1 else 1))) else (if x<2638 then (if x<2606 then 0 else (if x<2618 then 2 else 3)) else (if x<2668 then (if x<2650 then 1 else 2) else (if x<2680 then 3 else 0)))) else (if x<3164 then (if x<2792 then (if x<2730 then 2 else (if x<2762 then 0 else 3)) else (if x<3102 then 2 else (if x<3132 then 2 else 3))) else (if x<3244 then (if x<3178 then 1 else (if x<3226 then 0 else 3)) else (if x<3276 then (if x<3256 then 2 else 0) else (if x<3288 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3049 : Finset ℕ := ([40,1626,1768,2618,2668,2680,2716,2762,3102,3164,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3049 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3049 4 (fun x => (if x<2716 then (if x<2618 then (if x<1626 then 0 else (if x<1768 then 1 else 0)) else (if x<2668 then 1 else (if x<2680 then 0 else 2))) else (if x<3164 then (if x<2762 then 2 else (if x<3102 then 1 else 3)) else (if x<3244 then 2 else (if x<3256 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3050 : Finset ℕ := ([1626,1768,2618,2668,3164,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3050 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3050 3 (fun x => (if x<2668 then (if x<1768 then 0 else (if x<2618 then 0 else 1)) else (if x<3164 then 1 else (if x<3256 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3051 : Finset ℕ := ([40,1626,1768,2606,2618,2668,2680,2716,2762,3102,3164,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3051 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3051 2606 3
  · have he : independentCachedBranchMembers3051.erase 2606=independentCachedBranchMembers3049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3049
  · have he : independentCachedBranchMembers3051.filter (independentCachedEdge 2606)=independentCachedBranchMembers3050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3050
def independentCachedBranchMembers3052 : Finset ℕ := ([40,72,250,1594,1626,1644,1738,1768,2606,2618,2638,2650,2668,2680,2716,2730,2762,2792,3102,3132,3164,3178,3226,3244,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3052 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3052 1738 4
  · have he : independentCachedBranchMembers3052.erase 1738=independentCachedBranchMembers3048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3048
  · have he : independentCachedBranchMembers3052.filter (independentCachedEdge 1738)=independentCachedBranchMembers3051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3051
def independentCachedBranchMembers3053 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2618,2620,2638,2650,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3162,3164,3178,3180,3192,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3053 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3053 3228 5
  · have he : independentCachedBranchMembers3053.erase 3228=independentCachedBranchMembers3047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3047
  · have he : independentCachedBranchMembers3053.filter (independentCachedEdge 3228)=independentCachedBranchMembers3052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3052
def independentCachedBranchMembers3054 : Finset ℕ := ([40,250,252,1594,1596,1708,1752,1768,2618,2620,2638,2680,2714,2716,2730,2732,2776,2792,3102,3118,3162,3164,3178,3180,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3054 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3054 5 (fun x => (if x<2716 then (if x<1752 then (if x<1594 then (if x<250 then 0 else (if x<252 then 0 else 1)) else (if x<1596 then 0 else (if x<1708 then 1 else 2))) else (if x<2620 then (if x<1768 then 1 else (if x<2618 then 0 else 3)) else (if x<2680 then (if x<2638 then 2 else 3) else (if x<2714 then 0 else 4)))) else (if x<3162 then (if x<2776 then (if x<2730 then 1 else (if x<2732 then 0 else 3)) else (if x<3102 then (if x<2792 then 3 else 2) else (if x<3118 then 4 else 3))) else (if x<3180 then (if x<3164 then 3 else (if x<3178 then 1 else 0)) else (if x<3274 then (if x<3256 then 2 else 0) else (if x<3276 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3055 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2618,2620,2638,2650,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3055 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3055 3150 5
  · have he : independentCachedBranchMembers3055.erase 3150=independentCachedBranchMembers3053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3053
  · have he : independentCachedBranchMembers3055.filter (independentCachedEdge 3150)=independentCachedBranchMembers3054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3054
def independentCachedBranchMembers3056 : Finset ℕ := ([40,250,1594,1628,1642,1678,1708,1720,1738,1768,2620,2638,2650,2668,2680,2716,2730,2764,2776,3118,3164,3178,3226,3244,3256,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3056 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3056 5 (fun x => (if x<2668 then (if x<1708 then (if x<1628 then (if x<250 then 0 else (if x<1594 then 0 else 0)) else (if x<1642 then 1 else (if x<1678 then 1 else 1))) else (if x<1768 then (if x<1720 then 2 else (if x<1738 then 1 else 2)) else (if x<2638 then (if x<2620 then 0 else 2) else (if x<2650 then 1 else 2)))) else (if x<3164 then (if x<2730 then (if x<2680 then 3 else (if x<2716 then 0 else 1)) else (if x<2776 then (if x<2764 then 0 else 2) else (if x<3118 then 3 else 3))) else (if x<3244 then (if x<3178 then 3 else (if x<3226 then 0 else 3)) else (if x<3274 then (if x<3256 then 4 else 0) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3057 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1708,1720,1738,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3057 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3057 2652 5
  · have he : independentCachedBranchMembers3057.erase 2652=independentCachedBranchMembers3055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3055
  · have he : independentCachedBranchMembers3057.filter (independentCachedEdge 2652)=independentCachedBranchMembers3056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3056
def independentCachedBranchMembers3058 : Finset ℕ := ([40,250,1594,1628,1644,1678,1708,1738,1752,2620,2680,2714,2730,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3058 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3058 5 (fun x => (if x<2714 then (if x<1678 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 0 else (if x<1644 then 1 else 2))) else (if x<1752 then (if x<1708 then 1 else (if x<1738 then 3 else 2)) else (if x<2620 then 3 else (if x<2680 then 2 else 0)))) else (if x<3178 then (if x<3118 then (if x<2730 then 2 else 0) else (if x<3132 then 3 else (if x<3162 then 4 else 3))) else (if x<3242 then (if x<3192 then 0 else (if x<3226 then 1 else 4)) else (if x<3256 then 1 else (if x<3276 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3059 : Finset ℕ := ([40,250,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3059 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3059 4 (fun x => (if x<3178 then (if x<3118 then (if x<250 then 0 else 0) else (if x<3132 then 1 else (if x<3162 then 2 else 1))) else (if x<3242 then (if x<3192 then 0 else (if x<3226 then 3 else 2)) else (if x<3256 then 3 else (if x<3276 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3060 : Finset ℕ := ([40,250,1594,1628,1644,1678,1708,1738,1752,2620,2680,2714,2730,2764,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3060 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3060 2764 4
  · have he : independentCachedBranchMembers3060.erase 2764=independentCachedBranchMembers3058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3058
  · have he : independentCachedBranchMembers3060.filter (independentCachedEdge 2764)=independentCachedBranchMembers3059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3059
def independentCachedBranchMembers3061 : Finset ℕ := ([40,1644,1678,2680,2714,3118,3132,3162,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3061 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3061 4 (fun x => (if x<3118 then (if x<1678 then (if x<1644 then 0 else 0) else (if x<2680 then 1 else (if x<2714 then 0 else 1))) else (if x<3242 then (if x<3132 then 2 else (if x<3162 then 0 else 2)) else (if x<3256 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3062 : Finset ℕ := ([40,250,1594,1628,1644,1678,1708,1738,1752,2620,2650,2680,2714,2730,2764,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3062 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3062 2650 4
  · have he : independentCachedBranchMembers3062.erase 2650=independentCachedBranchMembers3060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3060
  · have he : independentCachedBranchMembers3062.filter (independentCachedEdge 2650)=independentCachedBranchMembers3061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3061
def independentCachedBranchMembers3063 : Finset ℕ := ([250,1628,1738,2620,2730,3118,3162,3192,3226,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3063 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3063 4 (fun x => (if x<3118 then (if x<1738 then (if x<1628 then 0 else 1) else (if x<2620 then 0 else (if x<2730 then 1 else 0))) else (if x<3226 then (if x<3162 then 2 else (if x<3192 then 2 else 1)) else (if x<3256 then 0 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3064 : Finset ℕ := ([40,250,1594,1628,1644,1678,1708,1738,1752,2606,2620,2650,2680,2714,2730,2764,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3064 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3064 2606 4
  · have he : independentCachedBranchMembers3064.erase 2606=independentCachedBranchMembers3062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3062
  · have he : independentCachedBranchMembers3064.filter (independentCachedEdge 2606)=independentCachedBranchMembers3063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3063
def independentCachedBranchMembers3065 : Finset ℕ := ([1644,1708,1738,1752,2606,2620,2650,2714,3118,3132,3162,3226] : List ℕ).toFinset
theorem independentCachedBranchBound3065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3065 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3065 4 (fun x => (if x<2650 then (if x<1752 then (if x<1708 then 0 else (if x<1738 then 1 else 0)) else (if x<2606 then 1 else (if x<2620 then 1 else 0))) else (if x<3132 then (if x<2714 then 1 else (if x<3118 then 0 else 2)) else (if x<3162 then 3 else (if x<3226 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3066 : Finset ℕ := ([40,250,1594,1628,1644,1678,1708,1738,1752,1768,2606,2620,2650,2680,2714,2730,2764,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3066 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3066 1768 4
  · have he : independentCachedBranchMembers3066.erase 1768=independentCachedBranchMembers3064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3064
  · have he : independentCachedBranchMembers3066.filter (independentCachedEdge 1768)=independentCachedBranchMembers3065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3065
def independentCachedBranchMembers3067 : Finset ℕ := ([40,250,1644,1708,1738,1752,2680,2730,2764,3118,3132,3162,3226] : List ℕ).toFinset
theorem independentCachedBranchBound3067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3067 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3067 4 (fun x => (if x<2680 then (if x<1708 then (if x<250 then 0 else (if x<1644 then 0 else 1)) else (if x<1738 then 2 else (if x<1752 then 1 else 2))) else (if x<3118 then (if x<2730 then 0 else (if x<2764 then 0 else 1)) else (if x<3162 then (if x<3132 then 2 else 3) else (if x<3226 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3068 : Finset ℕ := ([40,250,1594,1628,1644,1678,1708,1738,1752,1768,2606,2620,2650,2680,2714,2730,2764,3102,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3068 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3068 3102 4
  · have he : independentCachedBranchMembers3068.erase 3102=independentCachedBranchMembers3066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3066
  · have he : independentCachedBranchMembers3068.filter (independentCachedEdge 3102)=independentCachedBranchMembers3067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3067
def independentCachedBranchMembers3069 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3069 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3069 1740 5
  · have he : independentCachedBranchMembers3069.erase 1740=independentCachedBranchMembers3057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3057
  · have he : independentCachedBranchMembers3069.filter (independentCachedEdge 1740)=independentCachedBranchMembers3068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3068
def independentCachedBranchMembers3070 : Finset ℕ := ([40,250,252,1594,1642,1644,1708,1720,1768,2618,2620,2668,2680,2730,2732,2792,3118,3132,3178,3192,3242,3244,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3070 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3070 5 (fun x => (if x<2680 then (if x<1708 then (if x<1594 then (if x<250 then 0 else (if x<252 then 0 else 1)) else (if x<1642 then 0 else (if x<1644 then 2 else 1))) else (if x<2618 then (if x<1720 then 2 else (if x<1768 then 1 else 0)) else (if x<2620 then 3 else (if x<2668 then 1 else 2)))) else (if x<3178 then (if x<2792 then (if x<2730 then 0 else (if x<2732 then 0 else 3)) else (if x<3118 then 1 else (if x<3132 then 2 else 3))) else (if x<3244 then (if x<3192 then 0 else (if x<3242 then 1 else 3)) else (if x<3256 then 1 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3071 : Finset ℕ := ([250,1594,1644,1708,1720,2620,2730,2792,3132,3178,3242,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3071 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3071 4 (fun x => (if x<2730 then (if x<1708 then (if x<1594 then 0 else (if x<1644 then 0 else 1)) else (if x<1720 then 2 else (if x<2620 then 1 else 1))) else (if x<3178 then (if x<2792 then 0 else (if x<3132 then 1 else 2)) else (if x<3242 then 0 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
