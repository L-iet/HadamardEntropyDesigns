/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch20
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers2688 : Finset ℕ := ([132,252,1596,1628,1678,1686,1708,1748,2620,2652,2662,2702,2710,2740,2764,3118,3126,3150,3158,3180,3188,3228,3238,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2688 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2688 1596 4
  · have he : independentCachedBranchMembers2688.erase 1596=independentCachedBranchMembers2686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2686
  · have he : independentCachedBranchMembers2688.filter (independentCachedEdge 1596)=independentCachedBranchMembers2687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2687
def independentCachedBranchMembers2689 : Finset ℕ := ([48,72,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2689 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2689 250 5
  · have he : independentCachedBranchMembers2689.erase 250=independentCachedBranchMembers2683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2683
  · have he : independentCachedBranchMembers2689.filter (independentCachedEdge 250)=independentCachedBranchMembers2688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2688
def independentCachedBranchMembers2690 : Finset ℕ := ([132,252,1626,1708,1748,1776,2618,2650,2662,2740,2764,2792,2800,3118,3126,3150,3158,3178,3186,3228,3256,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2690 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2690 5 (fun x => (if x<2792 then (if x<1776 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1708 then 1 else (if x<1748 then 0 else 0))) else (if x<2662 then (if x<2618 then 1 else (if x<2650 then 2 else 3)) else (if x<2740 then 2 else (if x<2764 then 0 else 0)))) else (if x<3178 then (if x<3126 then (if x<2800 then 2 else (if x<3118 then 3 else 4)) else (if x<3150 then 2 else (if x<3158 then 1 else 4))) else (if x<3256 then (if x<3186 then 2 else (if x<3228 then 1 else 0)) else (if x<3288 then 2 else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2691 : Finset ℕ := ([132,1708,1776,2618,2650,2662,2740,2792,3118,3150,3186,3228] : List ℕ).toFinset
theorem independentCachedBranchBound2691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2691 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2691 4 (fun x => (if x<2740 then (if x<2618 then (if x<1708 then 0 else (if x<1776 then 0 else 1)) else (if x<2650 then 2 else (if x<2662 then 0 else 2))) else (if x<3150 then (if x<2792 then 1 else (if x<3118 then 1 else 2)) else (if x<3186 then 3 else (if x<3228 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2692 : Finset ℕ := ([132,252,1626,1708,1748,1768,1776,2618,2650,2662,2740,2764,2792,2800,3118,3126,3150,3158,3178,3186,3228,3256,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2692 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2692 1768 4
  · have he : independentCachedBranchMembers2692.erase 1768=independentCachedBranchMembers2690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2690
  · have he : independentCachedBranchMembers2692.filter (independentCachedEdge 1768)=independentCachedBranchMembers2691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2691
def independentCachedBranchMembers2693 : Finset ℕ := ([252,1626,1748,2618,2662,2740,2792,2800,3150,3158,3228,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2693 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2693 4 (fun x => (if x<2792 then (if x<2618 then (if x<1626 then 0 else (if x<1748 then 1 else 0)) else (if x<2662 then 1 else (if x<2740 then 2 else 0))) else (if x<3158 then (if x<2800 then 2 else (if x<3150 then 3 else 3)) else (if x<3228 then 2 else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2694 : Finset ℕ := ([132,252,1594,1626,1708,1748,1768,1776,2618,2650,2662,2740,2764,2792,2800,3118,3126,3150,3158,3178,3186,3228,3256,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2694 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2694 1594 4
  · have he : independentCachedBranchMembers2694.erase 1594=independentCachedBranchMembers2692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2692
  · have he : independentCachedBranchMembers2694.filter (independentCachedEdge 1594)=independentCachedBranchMembers2693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2693
def independentCachedBranchMembers2695 : Finset ℕ := ([48,72,130,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2695 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2695 130 5
  · have he : independentCachedBranchMembers2695.erase 130=independentCachedBranchMembers2689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2689
  · have he : independentCachedBranchMembers2695.filter (independentCachedEdge 130)=independentCachedBranchMembers2694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2694
def independentCachedBranchMembers2696 : Finset ℕ := ([48,72,1596,1714,1738,1768,2618,2620,2662,2710,2740,2764,2792,3126,3150,3178,3180,3226,3228,3256,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2696 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2696 5 (fun x => (if x<2764 then (if x<1768 then (if x<1596 then (if x<72 then 0 else 0) else (if x<1714 then 1 else (if x<1738 then 0 else 0))) else (if x<2662 then (if x<2618 then 1 else (if x<2620 then 2 else 3)) else (if x<2710 then 2 else (if x<2740 then 2 else 0)))) else (if x<3226 then (if x<3150 then (if x<2792 then 0 else (if x<3126 then 3 else 0)) else (if x<3178 then 0 else (if x<3180 then 2 else 1))) else (if x<3270 then (if x<3228 then 2 else (if x<3256 then 4 else 1)) else (if x<3298 then 2 else (if x<3300 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2697 : Finset ℕ := ([48,1714,1768,2618,2620,2662,2710,2764,3150,3256,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2697 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2697 4 (fun x => (if x<2710 then (if x<2618 then (if x<1714 then 0 else (if x<1768 then 0 else 1)) else (if x<2620 then 0 else (if x<2662 then 2 else 2))) else (if x<3256 then (if x<2764 then 1 else (if x<3150 then 1 else 3)) else (if x<3298 then 0 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2698 : Finset ℕ := ([48,72,1596,1686,1714,1738,1768,2618,2620,2662,2710,2740,2764,2792,3126,3150,3178,3180,3226,3228,3256,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2698 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2698 1686 4
  · have he : independentCachedBranchMembers2698.erase 1686=independentCachedBranchMembers2696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2696
  · have he : independentCachedBranchMembers2698.filter (independentCachedEdge 1686)=independentCachedBranchMembers2697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2697
def independentCachedBranchMembers2699 : Finset ℕ := ([72,1596,1714,2618,2662,2710,2740,2792,3150,3180,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2699 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2699 4 (fun x => (if x<2740 then (if x<2618 then (if x<1596 then 0 else (if x<1714 then 1 else 0)) else (if x<2662 then 1 else (if x<2710 then 2 else 0))) else (if x<3180 then (if x<2792 then 1 else (if x<3150 then 2 else 3)) else (if x<3228 then 0 else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2700 : Finset ℕ := ([48,72,1594,1596,1686,1714,1738,1768,2618,2620,2662,2710,2740,2764,2792,3126,3150,3178,3180,3226,3228,3256,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2700 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2700 1594 4
  · have he : independentCachedBranchMembers2700.erase 1594=independentCachedBranchMembers2698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2698
  · have he : independentCachedBranchMembers2700.filter (independentCachedEdge 1594)=independentCachedBranchMembers2699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2699
def independentCachedBranchMembers2701 : Finset ℕ := ([48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2701 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2701 80 5
  · have he : independentCachedBranchMembers2701.erase 80=independentCachedBranchMembers2695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2695
  · have he : independentCachedBranchMembers2701.filter (independentCachedEdge 80)=independentCachedBranchMembers2700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2700
def independentCachedBranchMembers2702 : Finset ℕ := ([48,72,1628,1714,1738,1776,2650,2652,2662,2702,2740,2764,2800,3126,3150,3186,3188,3226,3228,3238,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2702 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2702 5 (fun x => (if x<2764 then (if x<1776 then (if x<1628 then (if x<72 then 0 else 0) else (if x<1714 then 1 else (if x<1738 then 0 else 0))) else (if x<2662 then (if x<2650 then 1 else (if x<2652 then 2 else 3)) else (if x<2702 then 2 else (if x<2740 then 2 else 0)))) else (if x<3226 then (if x<3150 then (if x<2800 then 0 else (if x<3126 then 3 else 0)) else (if x<3186 then 0 else (if x<3188 then 2 else 1))) else (if x<3288 then (if x<3228 then 2 else (if x<3238 then 4 else 2)) else (if x<3298 then 1 else (if x<3300 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2703 : Finset ℕ := ([72,1738,1776,2650,2652,2662,2702,2740,3126,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2703 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2703 4 (fun x => (if x<2702 then (if x<2650 then (if x<1738 then 0 else (if x<1776 then 0 else 1)) else (if x<2652 then 0 else (if x<2662 then 2 else 2))) else (if x<3288 then (if x<2740 then 1 else (if x<3126 then 1 else 3)) else (if x<3298 then 0 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2704 : Finset ℕ := ([48,72,1628,1678,1714,1738,1776,2650,2652,2662,2702,2740,2764,2800,3126,3150,3186,3188,3226,3228,3238,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2704 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2704 1678 4
  · have he : independentCachedBranchMembers2704.erase 1678=independentCachedBranchMembers2702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2702
  · have he : independentCachedBranchMembers2704.filter (independentCachedEdge 1678)=independentCachedBranchMembers2703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2703
def independentCachedBranchMembers2705 : Finset ℕ := ([48,1628,1738,2650,2662,2702,2764,2800,3126,3188,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2705 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2705 4 (fun x => (if x<2764 then (if x<2650 then (if x<1628 then 0 else (if x<1738 then 1 else 0)) else (if x<2662 then 1 else (if x<2702 then 2 else 0))) else (if x<3188 then (if x<2800 then 1 else (if x<3126 then 2 else 3)) else (if x<3228 then 0 else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2706 : Finset ℕ := ([48,72,1626,1628,1678,1714,1738,1776,2650,2652,2662,2702,2740,2764,2800,3126,3150,3186,3188,3226,3228,3238,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2706 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2706 1626 4
  · have he : independentCachedBranchMembers2706.erase 1626=independentCachedBranchMembers2704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2704
  · have he : independentCachedBranchMembers2706.filter (independentCachedEdge 1626)=independentCachedBranchMembers2705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2705
def independentCachedBranchMembers2707 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2707 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2707 40 5
  · have he : independentCachedBranchMembers2707.erase 40=independentCachedBranchMembers2701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2701
  · have he : independentCachedBranchMembers2707.filter (independentCachedEdge 40)=independentCachedBranchMembers2706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2706
def independentCachedBranchMembers2708 : Finset ℕ := ([130,250,1596,1626,1678,1714,1768,2618,2652,2710,2730,2740,2764,2770,2800,3126,3150,3180,3186,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2708 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2708 5 (fun x => (if x<2740 then (if x<1714 then (if x<1596 then (if x<250 then 0 else 0) else (if x<1626 then 1 else (if x<1678 then 1 else 1))) else (if x<2652 then (if x<1768 then 0 else (if x<2618 then 1 else 2)) else (if x<2710 then 2 else (if x<2730 then 2 else 0)))) else (if x<3180 then (if x<2800 then (if x<2764 then 3 else (if x<2770 then 3 else 0)) else (if x<3126 then 2 else (if x<3150 then 3 else 3))) else (if x<3238 then (if x<3186 then 4 else (if x<3226 then 4 else 0)) else (if x<3256 then 4 else (if x<3298 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2709 : Finset ℕ := ([1596,1678,2618,2730,2770,2800,3186,3226,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2709 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2709 4 (fun x => (if x<2800 then (if x<2618 then (if x<1678 then 0 else 0) else (if x<2730 then 1 else (if x<2770 then 2 else 1))) else (if x<3226 then (if x<3186 then 2 else 1) else (if x<3256 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2710 : Finset ℕ := ([72,130,250,1596,1626,1678,1714,1768,2618,2652,2710,2730,2740,2764,2770,2800,3126,3150,3180,3186,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2710 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2710 72 4
  · have he : independentCachedBranchMembers2710.erase 72=independentCachedBranchMembers2708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2708
  · have he : independentCachedBranchMembers2710.filter (independentCachedEdge 72)=independentCachedBranchMembers2709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2709
def independentCachedBranchMembers2711 : Finset ℕ := ([1626,1768,2652,2710,2730,2770,3180,3226,3238,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2711 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2711 4 (fun x => (if x<2770 then (if x<2652 then (if x<1768 then 0 else 0) else (if x<2710 then 1 else (if x<2730 then 1 else 2))) else (if x<3226 then (if x<3180 then 2 else 1) else (if x<3238 then 2 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2712 : Finset ℕ := ([48,72,130,250,1596,1626,1678,1714,1768,2618,2652,2710,2730,2740,2764,2770,2800,3126,3150,3180,3186,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2712 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2712 48 4
  · have he : independentCachedBranchMembers2712.erase 48=independentCachedBranchMembers2710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2710
  · have he : independentCachedBranchMembers2712.filter (independentCachedEdge 48)=independentCachedBranchMembers2711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2711
def independentCachedBranchMembers2713 : Finset ℕ := ([48,72,130,250,3126,3150,3180,3186,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2713 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2713 4 (fun x => (if x<3180 then (if x<250 then (if x<72 then 0 else (if x<130 then 0 else 0)) else (if x<3126 then 0 else (if x<3150 then 1 else 1))) else (if x<3238 then (if x<3186 then 2 else (if x<3226 then 2 else 1)) else (if x<3256 then 2 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2714 : Finset ℕ := ([48,72,130,250,1596,1626,1678,1714,1748,1768,2618,2652,2710,2730,2740,2764,2770,2800,3126,3150,3180,3186,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2714 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2714 1748 4
  · have he : independentCachedBranchMembers2714.erase 1748=independentCachedBranchMembers2712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2712
  · have he : independentCachedBranchMembers2714.filter (independentCachedEdge 1748)=independentCachedBranchMembers2713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2713
def independentCachedBranchMembers2715 : Finset ℕ := ([1596,1626,1678,1768,2618,2652,2710,2800,3180,3186,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2715 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2715 4 (fun x => (if x<2710 then (if x<1768 then (if x<1626 then 0 else (if x<1678 then 0 else 0)) else (if x<2618 then 0 else (if x<2652 then 1 else 1))) else (if x<3186 then (if x<2800 then 1 else (if x<3180 then 1 else 2)) else (if x<3238 then 2 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2716 : Finset ℕ := ([48,72,130,250,1596,1626,1678,1714,1738,1748,1768,2618,2652,2710,2730,2740,2764,2770,2800,3126,3150,3180,3186,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2716 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2716 1738 4
  · have he : independentCachedBranchMembers2716.erase 1738=independentCachedBranchMembers2714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2714
  · have he : independentCachedBranchMembers2716.filter (independentCachedEdge 1738)=independentCachedBranchMembers2715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2715
def independentCachedBranchMembers2717 : Finset ℕ := ([48,72,130,250,1596,1626,1678,1768,2618,2652,2710,2800,3126,3150,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2717 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2717 4 (fun x => (if x<2618 then (if x<1596 then (if x<130 then (if x<72 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1678 then (if x<1626 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2652 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3226 then (if x<3150 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2718 : Finset ℕ := ([48,72,130,250,1596,1626,1678,1708,1714,1738,1748,1768,2618,2652,2710,2730,2740,2764,2770,2800,3126,3150,3180,3186,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2718 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2718 1708 4
  · have he : independentCachedBranchMembers2718.erase 1708=independentCachedBranchMembers2716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2716
  · have he : independentCachedBranchMembers2718.filter (independentCachedEdge 1708)=independentCachedBranchMembers2717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2717
def independentCachedBranchMembers2719 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2719 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2719 2772 5
  · have he : independentCachedBranchMembers2719.erase 2772=independentCachedBranchMembers2707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2707
  · have he : independentCachedBranchMembers2719.filter (independentCachedEdge 2772)=independentCachedBranchMembers2718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2718
def independentCachedBranchMembers2720 : Finset ℕ := ([132,252,1594,1628,1686,1708,1776,2620,2650,2702,2730,2740,2764,2770,2792,3118,3158,3180,3186,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2720 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2720 5 (fun x => (if x<2740 then (if x<1708 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1628 then 1 else (if x<1686 then 1 else 1))) else (if x<2650 then (if x<1776 then 0 else (if x<2620 then 1 else 2)) else (if x<2702 then 2 else (if x<2730 then 2 else 3)))) else (if x<3180 then (if x<2792 then (if x<2764 then 0 else (if x<2770 then 0 else 3)) else (if x<3118 then 2 else (if x<3158 then 3 else 3))) else (if x<3238 then (if x<3186 then 4 else (if x<3228 then 4 else 0)) else (if x<3256 then 4 else (if x<3300 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2721 : Finset ℕ := ([1594,1686,2620,2740,2764,2792,3180,3228,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2721 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2721 4 (fun x => (if x<2792 then (if x<2620 then (if x<1686 then 0 else 0) else (if x<2740 then 1 else (if x<2764 then 2 else 1))) else (if x<3228 then (if x<3180 then 2 else 1) else (if x<3256 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2722 : Finset ℕ := ([80,132,252,1594,1628,1686,1708,1776,2620,2650,2702,2730,2740,2764,2770,2792,3118,3158,3180,3186,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2722 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2722 80 4
  · have he : independentCachedBranchMembers2722.erase 80=independentCachedBranchMembers2720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2720
  · have he : independentCachedBranchMembers2722.filter (independentCachedEdge 80)=independentCachedBranchMembers2721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2721
def independentCachedBranchMembers2723 : Finset ℕ := ([1628,1776,2650,2702,2740,2764,3186,3228,3238,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2723 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2723 4 (fun x => (if x<2764 then (if x<2650 then (if x<1776 then 0 else 0) else (if x<2702 then 1 else (if x<2740 then 1 else 2))) else (if x<3228 then (if x<3186 then 2 else 1) else (if x<3238 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2724 : Finset ℕ := ([40,80,132,252,1594,1628,1686,1708,1776,2620,2650,2702,2730,2740,2764,2770,2792,3118,3158,3180,3186,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2724 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2724 40 4
  · have he : independentCachedBranchMembers2724.erase 40=independentCachedBranchMembers2722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2722
  · have he : independentCachedBranchMembers2724.filter (independentCachedEdge 40)=independentCachedBranchMembers2723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2723
def independentCachedBranchMembers2725 : Finset ℕ := ([1594,1628,1686,1776,2620,2650,2702,2792,3180,3186,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2725 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2725 4 (fun x => (if x<2702 then (if x<1776 then (if x<1628 then 0 else (if x<1686 then 0 else 0)) else (if x<2620 then 0 else (if x<2650 then 1 else 1))) else (if x<3186 then (if x<2792 then 1 else (if x<3180 then 1 else 2)) else (if x<3238 then 2 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2726 : Finset ℕ := ([40,80,132,252,1594,1628,1686,1708,1748,1776,2620,2650,2702,2730,2740,2764,2770,2792,3118,3158,3180,3186,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2726 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2726 1748 4
  · have he : independentCachedBranchMembers2726.erase 1748=independentCachedBranchMembers2724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2724
  · have he : independentCachedBranchMembers2726.filter (independentCachedEdge 1748)=independentCachedBranchMembers2725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2725
def independentCachedBranchMembers2727 : Finset ℕ := ([40,80,132,252,3118,3158,3180,3186,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2727 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2727 4 (fun x => (if x<3180 then (if x<252 then (if x<80 then 0 else (if x<132 then 0 else 0)) else (if x<3118 then 0 else (if x<3158 then 1 else 1))) else (if x<3238 then (if x<3186 then 2 else (if x<3228 then 2 else 1)) else (if x<3256 then 2 else (if x<3300 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2728 : Finset ℕ := ([40,80,132,252,1594,1628,1686,1708,1738,1748,1776,2620,2650,2702,2730,2740,2764,2770,2792,3118,3158,3180,3186,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2728 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2728 1738 4
  · have he : independentCachedBranchMembers2728.erase 1738=independentCachedBranchMembers2726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2726
  · have he : independentCachedBranchMembers2728.filter (independentCachedEdge 1738)=independentCachedBranchMembers2727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2727
def independentCachedBranchMembers2729 : Finset ℕ := ([40,80,132,252,1594,1628,1686,1776,2620,2650,2702,2792,3118,3158,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2729 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2729 4 (fun x => (if x<2620 then (if x<1594 then (if x<132 then (if x<80 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1686 then (if x<1628 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3118 then (if x<2702 then (if x<2650 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3228 then (if x<3158 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2730 : Finset ℕ := ([40,80,132,252,1594,1628,1686,1708,1714,1738,1748,1776,2620,2650,2702,2730,2740,2764,2770,2792,3118,3158,3180,3186,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2730 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2730 1714 4
  · have he : independentCachedBranchMembers2730.erase 1714=independentCachedBranchMembers2728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2728
  · have he : independentCachedBranchMembers2730.filter (independentCachedEdge 1714)=independentCachedBranchMembers2729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2729
def independentCachedBranchMembers2731 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2731 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2731 2762 5
  · have he : independentCachedBranchMembers2731.erase 2762=independentCachedBranchMembers2719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2719
  · have he : independentCachedBranchMembers2731.filter (independentCachedEdge 2762)=independentCachedBranchMembers2730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2730
def independentCachedBranchMembers2732 : Finset ℕ := ([132,252,1596,1626,1678,1748,1768,2618,2652,2710,2730,2740,2764,2770,2800,3118,3158,3178,3188,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2732 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2732 5 (fun x => (if x<2740 then (if x<1748 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1626 then 1 else (if x<1678 then 1 else 1))) else (if x<2652 then (if x<1768 then 0 else (if x<2618 then 1 else 2)) else (if x<2710 then 2 else (if x<2730 then 2 else 3)))) else (if x<3178 then (if x<2800 then (if x<2764 then 0 else (if x<2770 then 0 else 3)) else (if x<3118 then 2 else (if x<3158 then 3 else 3))) else (if x<3270 then (if x<3188 then 4 else (if x<3228 then 4 else 0)) else (if x<3288 then 4 else (if x<3300 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2733 : Finset ℕ := ([1596,1768,2618,2710,2740,2764,3178,3228,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2733 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2733 4 (fun x => (if x<2764 then (if x<2618 then (if x<1768 then 0 else 0) else (if x<2710 then 1 else (if x<2740 then 1 else 2))) else (if x<3228 then (if x<3178 then 2 else 1) else (if x<3270 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2734 : Finset ℕ := ([80,132,252,1596,1626,1678,1748,1768,2618,2652,2710,2730,2740,2764,2770,2800,3118,3158,3178,3188,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2734 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2734 80 4
  · have he : independentCachedBranchMembers2734.erase 80=independentCachedBranchMembers2732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2732
  · have he : independentCachedBranchMembers2734.filter (independentCachedEdge 80)=independentCachedBranchMembers2733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2733
def independentCachedBranchMembers2735 : Finset ℕ := ([1626,1678,2652,2740,2764,2800,3188,3228,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2735 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2735 4 (fun x => (if x<2800 then (if x<2652 then (if x<1678 then 0 else 0) else (if x<2740 then 1 else (if x<2764 then 1 else 2))) else (if x<3228 then (if x<3188 then 2 else 1) else (if x<3288 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2736 : Finset ℕ := ([40,80,132,252,1596,1626,1678,1748,1768,2618,2652,2710,2730,2740,2764,2770,2800,3118,3158,3178,3188,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2736 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2736 40 4
  · have he : independentCachedBranchMembers2736.erase 40=independentCachedBranchMembers2734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2734
  · have he : independentCachedBranchMembers2736.filter (independentCachedEdge 40)=independentCachedBranchMembers2735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2735
def independentCachedBranchMembers2737 : Finset ℕ := ([40,80,132,252,3118,3158,3178,3188,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2737 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2737 4 (fun x => (if x<3178 then (if x<252 then (if x<80 then 0 else (if x<132 then 0 else 0)) else (if x<3118 then 0 else (if x<3158 then 1 else 1))) else (if x<3270 then (if x<3188 then 2 else (if x<3228 then 2 else 1)) else (if x<3288 then 2 else (if x<3300 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2738 : Finset ℕ := ([40,80,132,252,1596,1626,1678,1714,1748,1768,2618,2652,2710,2730,2740,2764,2770,2800,3118,3158,3178,3188,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2738 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2738 1714 4
  · have he : independentCachedBranchMembers2738.erase 1714=independentCachedBranchMembers2736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2736
  · have he : independentCachedBranchMembers2738.filter (independentCachedEdge 1714)=independentCachedBranchMembers2737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2737
def independentCachedBranchMembers2739 : Finset ℕ := ([1596,1626,1678,1768,2618,2652,2710,2800,3178,3188,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2739 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2739 4 (fun x => (if x<2710 then (if x<1768 then (if x<1626 then 0 else (if x<1678 then 0 else 0)) else (if x<2618 then 0 else (if x<2652 then 1 else 1))) else (if x<3188 then (if x<2800 then 1 else (if x<3178 then 1 else 2)) else (if x<3270 then 2 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2740 : Finset ℕ := ([40,80,132,252,1596,1626,1678,1708,1714,1748,1768,2618,2652,2710,2730,2740,2764,2770,2800,3118,3158,3178,3188,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2740 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2740 1708 4
  · have he : independentCachedBranchMembers2740.erase 1708=independentCachedBranchMembers2738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2738
  · have he : independentCachedBranchMembers2740.filter (independentCachedEdge 1708)=independentCachedBranchMembers2739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2739
def independentCachedBranchMembers2741 : Finset ℕ := ([40,80,132,252,1596,1626,1678,1768,2618,2652,2710,2800,3118,3158,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2741 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2741 4 (fun x => (if x<2618 then (if x<1596 then (if x<132 then (if x<80 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1626 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3118 then (if x<2710 then (if x<2652 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3228 then (if x<3158 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2742 : Finset ℕ := ([40,80,132,252,1596,1626,1678,1708,1714,1738,1748,1768,2618,2652,2710,2730,2740,2764,2770,2800,3118,3158,3178,3188,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2742 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2742 1738 4
  · have he : independentCachedBranchMembers2742.erase 1738=independentCachedBranchMembers2740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2740
  · have he : independentCachedBranchMembers2742.filter (independentCachedEdge 1738)=independentCachedBranchMembers2741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2741
def independentCachedBranchMembers2743 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2743 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2743 2738 5
  · have he : independentCachedBranchMembers2743.erase 2738=independentCachedBranchMembers2731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2731
  · have he : independentCachedBranchMembers2743.filter (independentCachedEdge 2738)=independentCachedBranchMembers2742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2742
def independentCachedBranchMembers2744 : Finset ℕ := ([130,250,1594,1628,1686,1738,1776,2620,2650,2702,2730,2740,2764,2770,2792,3126,3150,3178,3188,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2744 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2744 5 (fun x => (if x<2740 then (if x<1738 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 1 else (if x<1686 then 1 else 1))) else (if x<2650 then (if x<1776 then 0 else (if x<2620 then 1 else 2)) else (if x<2702 then 2 else (if x<2730 then 2 else 0)))) else (if x<3178 then (if x<2792 then (if x<2764 then 3 else (if x<2770 then 3 else 0)) else (if x<3126 then 2 else (if x<3150 then 3 else 3))) else (if x<3270 then (if x<3188 then 4 else (if x<3226 then 4 else 0)) else (if x<3288 then 4 else (if x<3298 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2745 : Finset ℕ := ([1594,1776,2620,2702,2730,2770,3188,3226,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2745 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2745 4 (fun x => (if x<2770 then (if x<2620 then (if x<1776 then 0 else 0) else (if x<2702 then 1 else (if x<2730 then 1 else 2))) else (if x<3226 then (if x<3188 then 2 else 1) else (if x<3270 then 2 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2746 : Finset ℕ := ([72,130,250,1594,1628,1686,1738,1776,2620,2650,2702,2730,2740,2764,2770,2792,3126,3150,3178,3188,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2746 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2746 72 4
  · have he : independentCachedBranchMembers2746.erase 72=independentCachedBranchMembers2744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2744
  · have he : independentCachedBranchMembers2746.filter (independentCachedEdge 72)=independentCachedBranchMembers2745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2745
def independentCachedBranchMembers2747 : Finset ℕ := ([1628,1686,2650,2730,2770,2792,3178,3226,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2747 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2747 4 (fun x => (if x<2792 then (if x<2650 then (if x<1686 then 0 else 0) else (if x<2730 then 1 else (if x<2770 then 1 else 2))) else (if x<3226 then (if x<3178 then 2 else 1) else (if x<3288 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2748 : Finset ℕ := ([48,72,130,250,1594,1628,1686,1738,1776,2620,2650,2702,2730,2740,2764,2770,2792,3126,3150,3178,3188,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2748 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2748 48 4
  · have he : independentCachedBranchMembers2748.erase 48=independentCachedBranchMembers2746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2746
  · have he : independentCachedBranchMembers2748.filter (independentCachedEdge 48)=independentCachedBranchMembers2747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2747
def independentCachedBranchMembers2749 : Finset ℕ := ([1594,1628,1686,1776,2620,2650,2702,2792,3178,3188,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2749 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2749 4 (fun x => (if x<2702 then (if x<1776 then (if x<1628 then 0 else (if x<1686 then 0 else 0)) else (if x<2620 then 0 else (if x<2650 then 1 else 1))) else (if x<3188 then (if x<2792 then 1 else (if x<3178 then 1 else 2)) else (if x<3270 then 2 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2750 : Finset ℕ := ([48,72,130,250,1594,1628,1686,1714,1738,1776,2620,2650,2702,2730,2740,2764,2770,2792,3126,3150,3178,3188,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2750 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2750 1714 4
  · have he : independentCachedBranchMembers2750.erase 1714=independentCachedBranchMembers2748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2748
  · have he : independentCachedBranchMembers2750.filter (independentCachedEdge 1714)=independentCachedBranchMembers2749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2749
def independentCachedBranchMembers2751 : Finset ℕ := ([48,72,130,250,3126,3150,3178,3188,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2751 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2751 4 (fun x => (if x<3178 then (if x<250 then (if x<72 then 0 else (if x<130 then 0 else 0)) else (if x<3126 then 0 else (if x<3150 then 1 else 1))) else (if x<3270 then (if x<3188 then 2 else (if x<3226 then 2 else 1)) else (if x<3288 then 2 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2752 : Finset ℕ := ([48,72,130,250,1594,1628,1686,1708,1714,1738,1776,2620,2650,2702,2730,2740,2764,2770,2792,3126,3150,3178,3188,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2752 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2752 1708 4
  · have he : independentCachedBranchMembers2752.erase 1708=independentCachedBranchMembers2750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2750
  · have he : independentCachedBranchMembers2752.filter (independentCachedEdge 1708)=independentCachedBranchMembers2751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2751
def independentCachedBranchMembers2753 : Finset ℕ := ([48,72,130,250,1594,1628,1686,1776,2620,2650,2702,2792,3126,3150,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2753 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2753 4 (fun x => (if x<2620 then (if x<1594 then (if x<130 then (if x<72 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1686 then (if x<1628 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3126 then (if x<2702 then (if x<2650 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3226 then (if x<3150 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2754 : Finset ℕ := ([48,72,130,250,1594,1628,1686,1708,1714,1738,1748,1776,2620,2650,2702,2730,2740,2764,2770,2792,3126,3150,3178,3188,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2754 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2754 1748 4
  · have he : independentCachedBranchMembers2754.erase 1748=independentCachedBranchMembers2752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2752
  · have he : independentCachedBranchMembers2754.filter (independentCachedEdge 1748)=independentCachedBranchMembers2753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2753
def independentCachedBranchMembers2755 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2755 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2755 2732 5
  · have he : independentCachedBranchMembers2755.erase 2732=independentCachedBranchMembers2743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2743
  · have he : independentCachedBranchMembers2755.filter (independentCachedEdge 2732)=independentCachedBranchMembers2754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2754
def independentCachedBranchMembers2756 : Finset ℕ := ([132,252,1596,1626,1686,1708,1714,1738,1748,1776,2618,2652,2662,2680,2702,2740,2764,2770,2792,3126,3150,3178,3188,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2756 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2756 5 (fun x => (if x<2680 then (if x<1714 then (if x<1626 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 1 else 0))) else (if x<1776 then (if x<1738 then 2 else (if x<1748 then 2 else 0)) else (if x<2652 then (if x<2618 then 1 else 3) else (if x<2662 then 3 else 3)))) else (if x<3150 then (if x<2764 then (if x<2702 then 1 else (if x<2740 then 3 else 0)) else (if x<2792 then (if x<2770 then 0 else 1) else (if x<3126 then 3 else 2))) else (if x<3228 then (if x<3178 then 2 else (if x<3188 then 4 else 4)) else (if x<3256 then (if x<3238 then 0 else 4) else (if x<3300 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2757 : Finset ℕ := ([1596,1708,1748,1776,2618,2662,2702,2770,3188,3228,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2757 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2757 4 (fun x => (if x<2702 then (if x<1776 then (if x<1708 then 0 else (if x<1748 then 1 else 0)) else (if x<2618 then 1 else (if x<2662 then 0 else 2))) else (if x<3228 then (if x<2770 then 1 else (if x<3188 then 0 else 2)) else (if x<3256 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2758 : Finset ℕ := ([72,132,252,1596,1626,1686,1708,1714,1738,1748,1776,2618,2652,2662,2680,2702,2740,2764,2770,2792,3126,3150,3178,3188,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2758 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2758 72 4
  · have he : independentCachedBranchMembers2758.erase 72=independentCachedBranchMembers2756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2756
  · have he : independentCachedBranchMembers2758.filter (independentCachedEdge 72)=independentCachedBranchMembers2757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2757
def independentCachedBranchMembers2759 : Finset ℕ := ([1626,1686,1708,1748,2652,2662,2770,2792,3178,3228,3238,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2759 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2759 4 (fun x => (if x<2770 then (if x<1748 then (if x<1686 then 0 else (if x<1708 then 0 else 1)) else (if x<2652 then 1 else (if x<2662 then 2 else 2))) else (if x<3228 then (if x<2792 then 0 else (if x<3178 then 2 else 3)) else (if x<3238 then 1 else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2760 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1708,1714,1738,1748,1776,2618,2652,2662,2680,2702,2740,2764,2770,2792,3126,3150,3178,3188,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2760 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2760 48 4
  · have he : independentCachedBranchMembers2760.erase 48=independentCachedBranchMembers2758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2758
  · have he : independentCachedBranchMembers2760.filter (independentCachedEdge 48)=independentCachedBranchMembers2759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2759
def independentCachedBranchMembers2761 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1776,2618,2652,2702,2792,3126,3150,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2761 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2761 4 (fun x => (if x<2618 then (if x<1596 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3126 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2762 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1708,1714,1738,1748,1776,2618,2652,2662,2680,2702,2730,2740,2764,2770,2792,3126,3150,3178,3188,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2762 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2762 2730 4
  · have he : independentCachedBranchMembers2762.erase 2730=independentCachedBranchMembers2760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2760
  · have he : independentCachedBranchMembers2762.filter (independentCachedEdge 2730)=independentCachedBranchMembers2761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2761
def independentCachedBranchMembers2763 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1746,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2763 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2763 1746 5
  · have he : independentCachedBranchMembers2763.erase 1746=independentCachedBranchMembers2755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2755
  · have he : independentCachedBranchMembers2763.filter (independentCachedEdge 1746)=independentCachedBranchMembers2762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2762
def independentCachedBranchMembers2764 : Finset ℕ := ([130,250,1594,1628,1678,1708,1714,1738,1748,1768,2620,2650,2662,2680,2710,2730,2764,2770,2800,3118,3158,3178,3188,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2764 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2764 5 (fun x => (if x<2680 then (if x<1714 then (if x<1628 then (if x<250 then 0 else (if x<1594 then 0 else 1)) else (if x<1678 then 1 else (if x<1708 then 1 else 2))) else (if x<1768 then (if x<1738 then 0 else (if x<1748 then 0 else 2)) else (if x<2650 then (if x<2620 then 1 else 3) else (if x<2662 then 3 else 3)))) else (if x<3158 then (if x<2764 then (if x<2710 then 1 else (if x<2730 then 3 else 0)) else (if x<2800 then (if x<2770 then 1 else 0) else (if x<3118 then 3 else 2))) else (if x<3226 then (if x<3178 then 2 else (if x<3188 then 4 else 4)) else (if x<3256 then (if x<3238 then 0 else 4) else (if x<3298 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2765 : Finset ℕ := ([1594,1714,1738,1768,2620,2662,2710,2764,3178,3226,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2765 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2765 4 (fun x => (if x<2710 then (if x<1768 then (if x<1714 then 0 else (if x<1738 then 1 else 0)) else (if x<2620 then 1 else (if x<2662 then 0 else 2))) else (if x<3226 then (if x<2764 then 1 else (if x<3178 then 0 else 2)) else (if x<3256 then 2 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2766 : Finset ℕ := ([80,130,250,1594,1628,1678,1708,1714,1738,1748,1768,2620,2650,2662,2680,2710,2730,2764,2770,2800,3118,3158,3178,3188,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2766 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2766 80 4
  · have he : independentCachedBranchMembers2766.erase 80=independentCachedBranchMembers2764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2764
  · have he : independentCachedBranchMembers2766.filter (independentCachedEdge 80)=independentCachedBranchMembers2765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2765
def independentCachedBranchMembers2767 : Finset ℕ := ([1628,1678,1714,1738,2650,2662,2764,2800,3188,3226,3238,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2767 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2767 4 (fun x => (if x<2764 then (if x<1738 then (if x<1678 then 0 else (if x<1714 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 2 else 2))) else (if x<3226 then (if x<2800 then 0 else (if x<3188 then 2 else 3)) else (if x<3238 then 1 else (if x<3298 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2768 : Finset ℕ := ([40,80,130,250,1594,1628,1678,1708,1714,1738,1748,1768,2620,2650,2662,2680,2710,2730,2764,2770,2800,3118,3158,3178,3188,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2768 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2768 40 4
  · have he : independentCachedBranchMembers2768.erase 40=independentCachedBranchMembers2766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2766
  · have he : independentCachedBranchMembers2768.filter (independentCachedEdge 40)=independentCachedBranchMembers2767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2767
def independentCachedBranchMembers2769 : Finset ℕ := ([40,80,130,250,1594,1628,1678,1768,2620,2650,2710,2800,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2769 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2769 4 (fun x => (if x<2620 then (if x<1594 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3118 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2770 : Finset ℕ := ([40,80,130,250,1594,1628,1678,1708,1714,1738,1748,1768,2620,2650,2662,2680,2710,2730,2740,2764,2770,2800,3118,3158,3178,3188,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2770 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2770 2740 4
  · have he : independentCachedBranchMembers2770.erase 2740=independentCachedBranchMembers2768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2768
  · have he : independentCachedBranchMembers2770.filter (independentCachedEdge 2740)=independentCachedBranchMembers2769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2769
def independentCachedBranchMembers2771 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1740,1746,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2771 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2771 1740 5
  · have he : independentCachedBranchMembers2771.erase 1740=independentCachedBranchMembers2763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2763
  · have he : independentCachedBranchMembers2771.filter (independentCachedEdge 1740)=independentCachedBranchMembers2770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2770
def independentCachedBranchMembers2772 : Finset ℕ := ([40,48,250,252,1594,1596,1708,1714,1768,1776,2618,2620,2662,2680,2730,2732,2738,2740,2792,2800,3118,3126,3178,3180,3186,3188,3238,3256,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2772 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2772 5 (fun x => (if x<2732 then (if x<1714 then (if x<252 then (if x<48 then 0 else (if x<250 then 1 else 0)) else (if x<1596 then (if x<1594 then 1 else 0) else (if x<1708 then 1 else 2))) else (if x<2620 then (if x<1776 then (if x<1768 then 2 else 0) else (if x<2618 then 1 else 3)) else (if x<2680 then (if x<2662 then 4 else 3) else (if x<2730 then 0 else 0)))) else (if x<3178 then (if x<2792 then (if x<2738 then 3 else (if x<2740 then 4 else 1)) else (if x<3118 then (if x<2800 then 4 else 3) else (if x<3126 then 3 else 4))) else (if x<3238 then (if x<3186 then (if x<3180 then 0 else 2) else (if x<3188 then 2 else 1)) else (if x<3298 then (if x<3256 then 2 else 0) else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2773 : Finset ℕ := ([40,48,72,80,130,132,222,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1740,1746,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2773 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2773 222 5
  · have he : independentCachedBranchMembers2773.erase 222=independentCachedBranchMembers2771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2771
  · have he : independentCachedBranchMembers2773.filter (independentCachedEdge 222)=independentCachedBranchMembers2772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2772
def independentCachedBranchMembers2774 : Finset ℕ := ([72,80,130,132,1626,1628,1678,1686,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,3150,3158,3178,3180,3186,3188,3226,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2774 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2774 5 (fun x => (if x<2710 then (if x<1678 then (if x<132 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1626 then 1 else (if x<1628 then 1 else 0))) else (if x<2652 then (if x<1686 then 1 else (if x<2650 then 0 else 2)) else (if x<2680 then (if x<2662 then 3 else 2) else (if x<2702 then 0 else 2)))) else (if x<3178 then (if x<2738 then (if x<2730 then 3 else (if x<2732 then 4 else 1)) else (if x<3150 then (if x<2740 then 0 else 4) else (if x<3158 then 2 else 3))) else (if x<3188 then (if x<3180 then 4 else (if x<3186 then 0 else 1)) else (if x<3228 then (if x<3226 then 4 else 2) else (if x<3238 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2775 : Finset ℕ := ([80,132,1628,1686,2650,2662,2680,2702,2732,2738,3158,3178,3188,3228] : List ℕ).toFinset
theorem independentCachedBranchBound2775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2775 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2775 4 (fun x => (if x<2702 then (if x<1686 then (if x<132 then 0 else (if x<1628 then 0 else 1)) else (if x<2662 then (if x<2650 then 1 else 0) else (if x<2680 then 2 else 1))) else (if x<3158 then (if x<2732 then 0 else (if x<2738 then 2 else 1)) else (if x<3188 then (if x<3178 then 2 else 3) else (if x<3228 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2776 : Finset ℕ := ([72,80,130,132,1626,1628,1678,1686,1714,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,3150,3158,3178,3180,3186,3188,3226,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2776 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2776 1714 4
  · have he : independentCachedBranchMembers2776.erase 1714=independentCachedBranchMembers2774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2774
  · have he : independentCachedBranchMembers2776.filter (independentCachedEdge 1714)=independentCachedBranchMembers2775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2775
def independentCachedBranchMembers2777 : Finset ℕ := ([72,130,1626,1678,2652,2662,2680,2710,2732,2738,3150,3178,3188,3226] : List ℕ).toFinset
theorem independentCachedBranchBound2777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2777 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2777 4 (fun x => (if x<2710 then (if x<1678 then (if x<130 then 0 else (if x<1626 then 0 else 1)) else (if x<2662 then (if x<2652 then 1 else 0) else (if x<2680 then 2 else 1))) else (if x<3150 then (if x<2732 then 0 else (if x<2738 then 1 else 2)) else (if x<3188 then (if x<3178 then 2 else 3) else (if x<3226 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2778 : Finset ℕ := ([72,80,130,132,1626,1628,1678,1686,1708,1714,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,3150,3158,3178,3180,3186,3188,3226,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2778 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2778 1708 4
  · have he : independentCachedBranchMembers2778.erase 1708=independentCachedBranchMembers2776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2776
  · have he : independentCachedBranchMembers2778.filter (independentCachedEdge 1708)=independentCachedBranchMembers2777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2777
def independentCachedBranchMembers2779 : Finset ℕ := ([72,80,130,132,1626,1628,1678,1686,2650,2652,2702,2710,3150,3158,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound2779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2779 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2779 4 (fun x => (if x<2650 then (if x<1626 then (if x<130 then (if x<80 then 0 else 1) else (if x<132 then 0 else 1)) else (if x<1678 then (if x<1628 then 1 else 0) else (if x<1686 then 1 else 0))) else (if x<3150 then (if x<2702 then (if x<2652 then 2 else 3) else (if x<2710 then 2 else 3)) else (if x<3226 then (if x<3158 then 2 else 3) else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2780 : Finset ℕ := ([72,80,130,132,1626,1628,1678,1686,1708,1714,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2780 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2780 3256 4
  · have he : independentCachedBranchMembers2780.erase 3256=independentCachedBranchMembers2778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2778
  · have he : independentCachedBranchMembers2780.filter (independentCachedEdge 3256)=independentCachedBranchMembers2779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2779
def independentCachedBranchMembers2781 : Finset ℕ := ([40,48,72,80,130,132,192,222,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1740,1746,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2781 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2781 192 5
  · have he : independentCachedBranchMembers2781.erase 192=independentCachedBranchMembers2773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2773
  · have he : independentCachedBranchMembers2781.filter (independentCachedEdge 192)=independentCachedBranchMembers2780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2780
def independentCachedBranchMembers2782 : Finset ℕ := ([48,80,130,252,1596,1628,1678,1776,2620,2652,2662,2680,2702,2730,2740,2762,2772,2800,3118,3150,3188,3228,3238,3256,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2782 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2782 5 (fun x => (if x<2730 then (if x<1678 then (if x<252 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1596 then 1 else (if x<1628 then 0 else 1))) else (if x<2652 then (if x<1776 then 0 else (if x<2620 then 1 else 2)) else (if x<2680 then (if x<2662 then 3 else 2) else (if x<2702 then 0 else 2)))) else (if x<3188 then (if x<2772 then (if x<2740 then 4 else (if x<2762 then 3 else 0)) else (if x<3118 then (if x<2800 then 1 else 4) else (if x<3150 then 2 else 3))) else (if x<3256 then (if x<3228 then 0 else (if x<3238 then 2 else 3)) else (if x<3288 then (if x<3270 then 4 else 0) else (if x<3298 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2783 : Finset ℕ := ([48,130,1628,1776,2620,2662,2680,2702,2762,2772,3150,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2783 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2783 4 (fun x => (if x<2702 then (if x<1776 then (if x<130 then 0 else (if x<1628 then 0 else 1)) else (if x<2662 then (if x<2620 then 1 else 0) else (if x<2680 then 2 else 1))) else (if x<3150 then (if x<2762 then 0 else (if x<2772 then 2 else 1)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2784 : Finset ℕ := ([48,80,130,252,1596,1628,1678,1748,1776,2620,2652,2662,2680,2702,2730,2740,2762,2772,2800,3118,3150,3188,3228,3238,3256,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2784 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2784 1748 4
  · have he : independentCachedBranchMembers2784.erase 1748=independentCachedBranchMembers2782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2782
  · have he : independentCachedBranchMembers2784.filter (independentCachedEdge 1748)=independentCachedBranchMembers2783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2783
def independentCachedBranchMembers2785 : Finset ℕ := ([80,252,1596,1678,2652,2662,2680,2762,2772,2800,3118,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2785 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2785 4 (fun x => (if x<2762 then (if x<1678 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<2662 then (if x<2652 then 1 else 0) else (if x<2680 then 2 else 1))) else (if x<3118 then (if x<2772 then 1 else (if x<2800 then 2 else 0)) else (if x<3238 then (if x<3228 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2786 : Finset ℕ := ([48,80,130,252,1596,1628,1678,1738,1748,1776,2620,2652,2662,2680,2702,2730,2740,2762,2772,2800,3118,3150,3188,3228,3238,3256,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2786 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2786 1738 4
  · have he : independentCachedBranchMembers2786.erase 1738=independentCachedBranchMembers2784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2784
  · have he : independentCachedBranchMembers2786.filter (independentCachedEdge 1738)=independentCachedBranchMembers2785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2785
def independentCachedBranchMembers2787 : Finset ℕ := ([48,80,130,252,1596,1628,1678,1776,2620,2652,2702,2800,3118,3150,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2787 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2787 4 (fun x => (if x<2620 then (if x<1596 then (if x<130 then (if x<80 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1678 then (if x<1628 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3118 then (if x<2702 then (if x<2652 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3228 then (if x<3150 then 2 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2788 : Finset ℕ := ([48,80,130,252,1596,1628,1678,1738,1748,1776,2620,2652,2662,2680,2702,2730,2740,2762,2772,2800,3118,3150,3178,3188,3228,3238,3256,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2788 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2788 3178 4
  · have he : independentCachedBranchMembers2788.erase 3178=independentCachedBranchMembers2786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2786
  · have he : independentCachedBranchMembers2788.filter (independentCachedEdge 3178)=independentCachedBranchMembers2787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2787
def independentCachedBranchMembers2789 : Finset ℕ := ([18,40,48,72,80,130,132,192,222,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1740,1746,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2789 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2789 18 5
  · have he : independentCachedBranchMembers2789.erase 18=independentCachedBranchMembers2781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2781
  · have he : independentCachedBranchMembers2789.filter (independentCachedEdge 18)=independentCachedBranchMembers2788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2788
def independentCachedBranchMembers2790 : Finset ℕ := ([40,72,132,250,1594,1626,1686,1748,1768,2618,2650,2662,2680,2710,2730,2740,2762,2772,2792,3126,3158,3178,3226,3238,3256,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2790 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2790 5 (fun x => (if x<2730 then (if x<1748 then (if x<250 then (if x<72 then 0 else (if x<132 then 1 else 0)) else (if x<1626 then (if x<1594 then 1 else 0) else (if x<1686 then 1 else 0))) else (if x<2650 then (if x<1768 then 2 else (if x<2618 then 1 else 2)) else (if x<2680 then (if x<2662 then 3 else 3) else (if x<2710 then 0 else 2)))) else (if x<3178 then (if x<2772 then (if x<2740 then 3 else (if x<2762 then 4 else 1)) else (if x<3126 then (if x<2792 then 0 else 4) else (if x<3158 then 4 else 3))) else (if x<3256 then (if x<3226 then 0 else (if x<3238 then 3 else 3)) else (if x<3288 then (if x<3270 then 4 else 0) else (if x<3300 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2791 : Finset ℕ := ([40,132,1626,1768,2618,2662,2680,2710,2762,2772,3158,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2791 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2791 4 (fun x => (if x<2710 then (if x<1768 then (if x<132 then 0 else (if x<1626 then 0 else 1)) else (if x<2662 then (if x<2618 then 1 else 0) else (if x<2680 then 2 else 1))) else (if x<3158 then (if x<2762 then 0 else (if x<2772 then 1 else 2)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2792 : Finset ℕ := ([40,72,132,250,1594,1626,1686,1738,1748,1768,2618,2650,2662,2680,2710,2730,2740,2762,2772,2792,3126,3158,3178,3226,3238,3256,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2792 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2792 1738 4
  · have he : independentCachedBranchMembers2792.erase 1738=independentCachedBranchMembers2790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2790
  · have he : independentCachedBranchMembers2792.filter (independentCachedEdge 1738)=independentCachedBranchMembers2791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2791
def independentCachedBranchMembers2793 : Finset ℕ := ([40,72,132,250,1594,1626,1686,1768,2618,2650,2710,2792,3126,3158,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2793 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2793 4 (fun x => (if x<2618 then (if x<1594 then (if x<132 then (if x<72 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1686 then (if x<1626 then 0 else 1) else (if x<1768 then 0 else 1))) else (if x<3126 then (if x<2710 then (if x<2650 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3226 then (if x<3158 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2794 : Finset ℕ := ([40,72,132,250,1594,1626,1686,1738,1748,1768,2618,2650,2662,2680,2710,2730,2740,2762,2772,2792,3126,3158,3178,3188,3226,3238,3256,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2794 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2794 3188 4
  · have he : independentCachedBranchMembers2794.erase 3188=independentCachedBranchMembers2792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2792
  · have he : independentCachedBranchMembers2794.filter (independentCachedEdge 3188)=independentCachedBranchMembers2793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2793
def independentCachedBranchMembers2795 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,250,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1740,1746,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2795 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2795 12 5
  · have he : independentCachedBranchMembers2795.erase 12=independentCachedBranchMembers2789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2789
  · have he : independentCachedBranchMembers2795.filter (independentCachedEdge 12)=independentCachedBranchMembers2794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2794
def independentCachedBranchMembers2796 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2796 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2796 3174 6
  · have he : independentCachedBranchMembers2796.erase 3174=independentCachedBranchMembers2648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2648
  · have he : independentCachedBranchMembers2796.filter (independentCachedEdge 3174)=independentCachedBranchMembers2795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2795
def independentCachedBranchMembers2797 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1746,1764,1768,2606,2620,2646,2650,2662,2680,2710,2714,2730,2732,2738,2740,2762,2764,2772,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2797 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2797 6 (fun x => (if x<2646 then (if x<1692 then (if x<1628 then (if x<1594 then 0 else (if x<1614 then 1 else 0)) else (if x<1652 then (if x<1642 then 1 else 2) else (if x<1678 then 2 else 1))) else (if x<1764 then (if x<1720 then (if x<1702 then 0 else 2) else (if x<1746 then 2 else 0)) else (if x<2606 then (if x<1768 then 0 else 1) else (if x<2620 then 3 else 4)))) else (if x<2732 then (if x<2680 then (if x<2650 then 3 else (if x<2662 then 4 else 2)) else (if x<2714 then (if x<2710 then 1 else 4) else (if x<2730 then 3 else 1))) else (if x<2764 then (if x<2740 then (if x<2738 then 5 else 5) else (if x<2762 then 2 else 5)) else (if x<2786 then (if x<2772 then 1 else 5) else (if x<2800 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2798 : Finset ℕ := ([1594,1614,1642,1652,1678,1764,2606,2650,2662,2680,2714,2762,2764,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2798 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2798 5 (fun x => (if x<2650 then (if x<1652 then (if x<1614 then 0 else (if x<1642 then 0 else 1)) else (if x<1764 then (if x<1678 then 0 else 1) else (if x<2606 then 1 else 2))) else (if x<2762 then (if x<2680 then (if x<2662 then 2 else 3) else (if x<2714 then 3 else 4)) else (if x<2772 then (if x<2764 then 3 else 2) else (if x<2800 then 3 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2799 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1746,1764,1768,2606,2620,2646,2650,2662,2680,2710,2714,2730,2732,2738,2740,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2799 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2799 2776 5
  · have he : independentCachedBranchMembers2799.erase 2776=independentCachedBranchMembers2797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2797
  · have he : independentCachedBranchMembers2799.filter (independentCachedEdge 2776)=independentCachedBranchMembers2798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2798
def independentCachedBranchMembers2800 : Finset ℕ := ([1590,1628,1642,1652,1692,1768,2620,2646,2662,2680,2710,2762,2764,2772,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2800 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2800 5 (fun x => (if x<2646 then (if x<1652 then (if x<1628 then 0 else (if x<1642 then 0 else 0)) else (if x<1768 then (if x<1692 then 1 else 1) else (if x<2620 then 1 else 2))) else (if x<2762 then (if x<2680 then (if x<2662 then 2 else 3) else (if x<2710 then 3 else 4)) else (if x<2772 then (if x<2764 then 3 else 2) else (if x<2786 then 3 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2801 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1746,1764,1768,2606,2620,2646,2650,2662,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2801 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2801 2758 5
  · have he : independentCachedBranchMembers2801.erase 2758=independentCachedBranchMembers2799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2799
  · have he : independentCachedBranchMembers2801.filter (independentCachedEdge 2758)=independentCachedBranchMembers2800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2800
def independentCachedBranchMembers2802 : Finset ℕ := ([1614,1628,1702,1720,1764,1768,2646,2650,2662,2680,2732,2738,2764,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2802 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2802 5 (fun x => (if x<2650 then (if x<1720 then (if x<1628 then 0 else (if x<1702 then 1 else 0)) else (if x<1768 then (if x<1764 then 1 else 1) else (if x<2646 then 0 else 2))) else (if x<2738 then (if x<2680 then (if x<2662 then 3 else 3) else (if x<2732 then 2 else 4)) else (if x<2786 then (if x<2764 then 2 else 3) else (if x<2800 then 4 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2803 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1746,1764,1768,2606,2620,2646,2650,2662,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2803 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2803 2674 5
  · have he : independentCachedBranchMembers2803.erase 2674=independentCachedBranchMembers2801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2801
  · have he : independentCachedBranchMembers2803.filter (independentCachedEdge 2674)=independentCachedBranchMembers2802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2802
def independentCachedBranchMembers2804 : Finset ℕ := ([1590,1594,1678,1692,1702,1720,2606,2620,2662,2680,2710,2714,2732,2738,2764] : List ℕ).toFinset
theorem independentCachedBranchBound2804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2804 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2804 5 (fun x => (if x<2620 then (if x<1692 then (if x<1594 then 0 else (if x<1678 then 1 else 0)) else (if x<1720 then (if x<1702 then 1 else 1) else (if x<2606 then 0 else 2))) else (if x<2714 then (if x<2680 then (if x<2662 then 3 else 3) else (if x<2710 then 2 else 3)) else (if x<2738 then (if x<2732 then 2 else 4) else (if x<2764 then 4 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2805 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1746,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2805 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2805 2668 5
  · have he : independentCachedBranchMembers2805.erase 2668=independentCachedBranchMembers2803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2803
  · have he : independentCachedBranchMembers2805.filter (independentCachedEdge 2668)=independentCachedBranchMembers2804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2804
def independentCachedBranchMembers2806 : Finset ℕ := ([1594,1628,1642,1652,1692,1746,1764,2620,2650,2662,2668,2674,2680,2714,2732,2738,2762,2772,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2806 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2806 5 (fun x => (if x<2662 then (if x<1692 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1764 then (if x<1746 then 2 else 0) else (if x<2620 then 2 else (if x<2650 then 0 else 0)))) else (if x<2732 then (if x<2674 then (if x<2668 then 1 else 3) else (if x<2680 then 3 else (if x<2714 then 1 else 2))) else (if x<2762 then (if x<2738 then 2 else 0) else (if x<2772 then 1 else (if x<2786 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2807 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1746,1748,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2807 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2807 1748 5
  · have he : independentCachedBranchMembers2807.erase 1748=independentCachedBranchMembers2805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2805
  · have he : independentCachedBranchMembers2807.filter (independentCachedEdge 1748)=independentCachedBranchMembers2806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2806
def independentCachedBranchMembers2808 : Finset ℕ := ([1590,1614,1642,1652,1678,1746,1768,2606,2646,2662,2668,2674,2680,2710,2732,2738,2762,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2808 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2808 5 (fun x => (if x<2662 then (if x<1678 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1768 then (if x<1746 then 2 else 0) else (if x<2606 then 2 else (if x<2646 then 0 else 0)))) else (if x<2732 then (if x<2674 then (if x<2668 then 1 else 3) else (if x<2680 then 3 else (if x<2710 then 1 else 2))) else (if x<2762 then (if x<2738 then 2 else 0) else (if x<2772 then 0 else (if x<2800 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2809 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1738,1746,1748,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2809 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2809 1738 5
  · have he : independentCachedBranchMembers2809.erase 1738=independentCachedBranchMembers2807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2807
  · have he : independentCachedBranchMembers2809.filter (independentCachedEdge 1738)=independentCachedBranchMembers2808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2808
def independentCachedBranchMembers2810 : Finset ℕ := ([1590,1594,1614,1628,1702,1720,1746,2606,2620,2646,2650,2662,2680,2732,2738,2758,2762,2772,2776] : List ℕ).toFinset
theorem independentCachedBranchBound2810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2810 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2810 5 (fun x => (if x<2646 then (if x<1702 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1746 then (if x<1720 then 2 else 2) else (if x<2606 then 0 else (if x<2620 then 0 else 1)))) else (if x<2738 then (if x<2662 then (if x<2650 then 0 else 1) else (if x<2680 then 2 else (if x<2732 then 2 else 2))) else (if x<2762 then (if x<2758 then 0 else 3) else (if x<2772 then 0 else (if x<2776 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2811 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1714,1720,1738,1746,1748,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2811 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2811 1714 5
  · have he : independentCachedBranchMembers2811.erase 1714=independentCachedBranchMembers2809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2809
  · have he : independentCachedBranchMembers2811.filter (independentCachedEdge 1714)=independentCachedBranchMembers2810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2810
def independentCachedBranchMembers2812 : Finset ℕ := ([1678,1692,1702,1720,1746,1764,1768,2662,2680,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2812 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2812 5 (fun x => (if x<2710 then (if x<1746 then (if x<1702 then (if x<1692 then 0 else 1) else (if x<1720 then 1 else 0)) else (if x<1768 then (if x<1764 then 0 else 0) else (if x<2662 then 1 else (if x<2680 then 2 else 2)))) else (if x<2762 then (if x<2732 then (if x<2714 then 1 else 0) else (if x<2738 then 0 else (if x<2758 then 2 else 0))) else (if x<2776 then (if x<2772 then 2 else 2) else (if x<2786 then 1 else (if x<2800 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2813 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1708,1714,1720,1738,1746,1748,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2813 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2813 1708 5
  · have he : independentCachedBranchMembers2813.erase 1708=independentCachedBranchMembers2811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2811
  · have he : independentCachedBranchMembers2813.filter (independentCachedEdge 1708)=independentCachedBranchMembers2812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2812
def independentCachedBranchMembers2814 : Finset ℕ := ([1590,1628,1692,1702,1720,1738,1746,1748,1768,2620,2646,2668,2674,2710,2730,2732,2738,2740,2758,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound2814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2814 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2814 5 (fun x => (if x<2646 then (if x<1738 then (if x<1692 then (if x<1628 then 0 else 0) else (if x<1702 then 1 else (if x<1720 then 1 else 0))) else (if x<1748 then (if x<1746 then 1 else 0) else (if x<1768 then 2 else (if x<2620 then 2 else 0)))) else (if x<2732 then (if x<2674 then (if x<2668 then 0 else 3) else (if x<2710 then 3 else (if x<2730 then 2 else 2))) else (if x<2758 then (if x<2738 then 4 else (if x<2740 then 0 else 1)) else (if x<2776 then 3 else (if x<2786 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2815 : Finset ℕ := ([1590,1594,1614,1628,1642,1652,1678,1692,1702,1708,1714,1720,1738,1746,1748,1752,1764,1768,2606,2620,2646,2650,2662,2668,2674,2680,2710,2714,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound2815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2815 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2815 1752 5
  · have he : independentCachedBranchMembers2815.erase 1752=independentCachedBranchMembers2813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2813
  · have he : independentCachedBranchMembers2815.filter (independentCachedEdge 1752)=independentCachedBranchMembers2814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2814
end EntropyDesigns.QuadraticRefinement
