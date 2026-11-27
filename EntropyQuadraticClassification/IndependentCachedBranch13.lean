/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch12
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers1664 : Finset ℕ := ([48,72,132,252,1596,1642,1692,1702,1714,1738,1764,1776,2618,2646,2668,2680,2702,2740,2764,2776,2786,3126,3150,3162,3188,3222,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1664 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1664 48 4
  · have he : independentCachedBranchMembers1664.erase 48=independentCachedBranchMembers1662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1662
  · have he : independentCachedBranchMembers1664.filter (independentCachedEdge 48)=independentCachedBranchMembers1663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1663
def independentCachedBranchMembers1665 : Finset ℕ := ([48,72,132,252,1596,1642,1702,1776,2618,2668,2702,2776,3126,3150,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1665 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1665 4 (fun x => (if x<2618 then (if x<1596 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1702 then (if x<1642 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3126 then (if x<2702 then (if x<2668 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3244 then (if x<3150 then 3 else 3) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1666 : Finset ℕ := ([48,72,132,252,1596,1642,1692,1702,1714,1738,1764,1776,2618,2646,2668,2680,2702,2714,2740,2764,2776,2786,3126,3150,3162,3188,3222,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1666 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1666 2714 4
  · have he : independentCachedBranchMembers1666.erase 2714=independentCachedBranchMembers1664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1664
  · have he : independentCachedBranchMembers1666.filter (independentCachedEdge 2714)=independentCachedBranchMembers1665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1665
def independentCachedBranchMembers1667 : Finset ℕ := ([18,48,72,132,222,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786,3126,3130,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1667 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1667 3158 5
  · have he : independentCachedBranchMembers1667.erase 3158=independentCachedBranchMembers1659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1659
  · have he : independentCachedBranchMembers1667.filter (independentCachedEdge 3158)=independentCachedBranchMembers1666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1666
def independentCachedBranchMembers1668 : Finset ℕ := ([18,72,132,222,1628,1650,1692,1714,1734,1738,1764,1768,2646,2650,2680,2710,2714,2740,2764,2786,3126,3130,3150,3180,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1668 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1668 5 (fun x => (if x<2680 then (if x<1714 then (if x<222 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1650 then (if x<1628 then 0 else 1) else (if x<1692 then 1 else 2))) else (if x<1764 then (if x<1734 then 2 else (if x<1738 then 1 else 2)) else (if x<2646 then (if x<1768 then 2 else 1) else (if x<2650 then 1 else 0)))) else (if x<3130 then (if x<2740 then (if x<2710 then 1 else (if x<2714 then 0 else 2)) else (if x<2786 then (if x<2764 then 2 else 0) else (if x<3126 then 1 else 3))) else (if x<3214 then (if x<3150 then 4 else (if x<3180 then 3 else 4)) else (if x<3284 then (if x<3244 then 4 else 3) else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1669 : Finset ℕ := ([18,222,1650,1714,1734,1738,2650,2710,2786,3126,3130,3150,3214] : List ℕ).toFinset
theorem independentCachedBranchBound1669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1669 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1669 4 (fun x => (if x<2650 then (if x<1714 then (if x<222 then 0 else (if x<1650 then 0 else 1)) else (if x<1734 then 2 else (if x<1738 then 1 else 2))) else (if x<3126 then (if x<2710 then 0 else (if x<2786 then 0 else 1)) else (if x<3150 then (if x<3130 then 2 else 3) else (if x<3214 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1670 : Finset ℕ := ([1650,1734,2650,2710,3126,3150] : List ℕ).toFinset
theorem independentCachedBranchBound1670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1670 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1670 3 (fun x => (if x<2710 then (if x<1734 then 0 else (if x<2650 then 0 else 1)) else (if x<3126 then 1 else (if x<3150 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1671 : Finset ℕ := ([18,222,1650,1714,1734,1738,2650,2710,2714,2786,3126,3130,3150,3214] : List ℕ).toFinset
theorem independentCachedBranchBound1671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1671 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1671 2714 3
  · have he : independentCachedBranchMembers1671.erase 2714=independentCachedBranchMembers1669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1669
  · have he : independentCachedBranchMembers1671.filter (independentCachedEdge 2714)=independentCachedBranchMembers1670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1670
def independentCachedBranchMembers1672 : Finset ℕ := ([1714,1738,2650,2710,3130,3214] : List ℕ).toFinset
theorem independentCachedBranchBound1672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1672 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1672 3 (fun x => (if x<2710 then (if x<1738 then 0 else (if x<2650 then 0 else 1)) else (if x<3130 then 1 else (if x<3214 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1673 : Finset ℕ := ([18,222,1650,1714,1734,1738,2646,2650,2710,2714,2786,3126,3130,3150,3214] : List ℕ).toFinset
theorem independentCachedBranchBound1673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1673 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1673 2646 3
  · have he : independentCachedBranchMembers1673.erase 2646=independentCachedBranchMembers1671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1671
  · have he : independentCachedBranchMembers1673.filter (independentCachedEdge 2646)=independentCachedBranchMembers1672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1672
def independentCachedBranchMembers1674 : Finset ℕ := ([18,72,132,222,252,1628,1650,1692,1714,1734,1738,1764,1768,2646,2650,2680,2710,2714,2740,2764,2786,3126,3130,3150,3180,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1674 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1674 252 4
  · have he : independentCachedBranchMembers1674.erase 252=independentCachedBranchMembers1668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1668
  · have he : independentCachedBranchMembers1674.filter (independentCachedEdge 252)=independentCachedBranchMembers1673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1673
def independentCachedBranchMembers1675 : Finset ℕ := ([18,222,1628,1692,1764,1768,2650,2710,2786,3180,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1675 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1675 4 (fun x => (if x<2650 then (if x<1692 then (if x<222 then 0 else (if x<1628 then 0 else 1)) else (if x<1764 then 2 else (if x<1768 then 1 else 2))) else (if x<3180 then (if x<2710 then 0 else (if x<2786 then 0 else 1)) else (if x<3284 then (if x<3244 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1676 : Finset ℕ := ([1628,1768,2650,2710,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1676 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1676 3 (fun x => (if x<2710 then (if x<1768 then 0 else (if x<2650 then 0 else 1)) else (if x<3244 then 1 else (if x<3284 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1677 : Finset ℕ := ([18,222,1628,1692,1764,1768,2650,2710,2714,2786,3180,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1677 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1677 2714 3
  · have he : independentCachedBranchMembers1677.erase 2714=independentCachedBranchMembers1675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1675
  · have he : independentCachedBranchMembers1677.filter (independentCachedEdge 2714)=independentCachedBranchMembers1676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1676
def independentCachedBranchMembers1678 : Finset ℕ := ([1692,1764,2650,2710,3180,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1678 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1678 3 (fun x => (if x<2710 then (if x<1764 then 0 else (if x<2650 then 0 else 1)) else (if x<3180 then 1 else (if x<3288 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1679 : Finset ℕ := ([18,222,1628,1692,1764,1768,2646,2650,2710,2714,2786,3180,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1679 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1679 2646 3
  · have he : independentCachedBranchMembers1679.erase 2646=independentCachedBranchMembers1677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1677
  · have he : independentCachedBranchMembers1679.filter (independentCachedEdge 2646)=independentCachedBranchMembers1678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1678
def independentCachedBranchMembers1680 : Finset ℕ := ([18,48,72,132,222,252,1628,1650,1692,1714,1734,1738,1764,1768,2646,2650,2680,2710,2714,2740,2764,2786,3126,3130,3150,3180,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1680 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1680 48 4
  · have he : independentCachedBranchMembers1680.erase 48=independentCachedBranchMembers1674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1674
  · have he : independentCachedBranchMembers1680.filter (independentCachedEdge 48)=independentCachedBranchMembers1679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1679
def independentCachedBranchMembers1681 : Finset ℕ := ([18,48,72,132,222,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786,3118,3126,3130,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1681 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1681 3118 5
  · have he : independentCachedBranchMembers1681.erase 3118=independentCachedBranchMembers1667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1667
  · have he : independentCachedBranchMembers1681.filter (independentCachedEdge 3118)=independentCachedBranchMembers1680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1680
def independentCachedBranchMembers1682 : Finset ℕ := ([132,252,1628,1650,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2702,2732,2772,2776,3118,3162,3188,3192,3222,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1682 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1682 5 (fun x => (if x<2668 then (if x<1734 then (if x<1650 then (if x<252 then 0 else (if x<1628 then 0 else 1)) else (if x<1692 then 1 else (if x<1714 then 0 else 2))) else (if x<1768 then (if x<1738 then 1 else (if x<1764 then 2 else 0)) else (if x<2618 then (if x<2614 then 1 else 2) else (if x<2638 then 3 else 2)))) else (if x<3188 then (if x<2772 then (if x<2702 then 3 else (if x<2732 then 3 else 0)) else (if x<3118 then (if x<2776 then 0 else 3) else (if x<3162 then 3 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3222 then 1 else 4)) else (if x<3276 then (if x<3256 then 0 else 4) else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1683 : Finset ℕ := ([1650,1692,1734,1764,2618,2702,2732,2772,3118,3188,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1683 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1683 4 (fun x => (if x<2732 then (if x<1764 then (if x<1692 then 0 else (if x<1734 then 1 else 0)) else (if x<2618 then 1 else (if x<2702 then 0 else 0))) else (if x<3188 then (if x<2772 then 1 else (if x<3118 then 1 else 2)) else (if x<3256 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1684 : Finset ℕ := ([72,132,252,1628,1650,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2702,2732,2772,2776,3118,3162,3188,3192,3222,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1684 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1684 72 4
  · have he : independentCachedBranchMembers1684.erase 72=independentCachedBranchMembers1682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1682
  · have he : independentCachedBranchMembers1684.filter (independentCachedEdge 72)=independentCachedBranchMembers1683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1683
def independentCachedBranchMembers1685 : Finset ℕ := ([1628,1692,1764,1768,2668,2732,2772,2776,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1685 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1685 4 (fun x => (if x<2772 then (if x<1768 then (if x<1692 then 0 else (if x<1764 then 1 else 0)) else (if x<2668 then 1 else (if x<2732 then 0 else 1))) else (if x<3162 then (if x<2776 then 0 else (if x<3118 then 1 else 2)) else (if x<3222 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1686 : Finset ℕ := ([48,72,132,252,1628,1650,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2702,2732,2772,2776,3118,3162,3188,3192,3222,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1686 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1686 48 4
  · have he : independentCachedBranchMembers1686.erase 48=independentCachedBranchMembers1684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1684
  · have he : independentCachedBranchMembers1686.filter (independentCachedEdge 48)=independentCachedBranchMembers1685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1685
def independentCachedBranchMembers1687 : Finset ℕ := ([48,72,132,252,1628,1650,1734,1768,2614,2638,2732,2772,3162,3188,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound1687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1687 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1687 4 (fun x => (if x<2614 then (if x<1628 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3162 then (if x<2732 then (if x<2638 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3222 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1688 : Finset ℕ := ([48,72,132,252,1628,1650,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2702,2732,2772,2776,3118,3162,3188,3192,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1688 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1688 3226 4
  · have he : independentCachedBranchMembers1688.erase 3226=independentCachedBranchMembers1686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1686
  · have he : independentCachedBranchMembers1688.filter (independentCachedEdge 3226)=independentCachedBranchMembers1687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1687
def independentCachedBranchMembers1689 : Finset ℕ := ([48,72,132,252,1692,1714,1738,1764,2618,2668,2702,2776,3162,3188,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound1689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1689 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1689 4 (fun x => (if x<2618 then (if x<1692 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3162 then (if x<2702 then (if x<2668 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3222 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1690 : Finset ℕ := ([48,72,132,252,1628,1650,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2702,2732,2772,2776,3118,3158,3162,3188,3192,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1690 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1690 3158 4
  · have he : independentCachedBranchMembers1690.erase 3158=independentCachedBranchMembers1688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1688
  · have he : independentCachedBranchMembers1690.filter (independentCachedEdge 3158)=independentCachedBranchMembers1689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1689
def independentCachedBranchMembers1691 : Finset ℕ := ([48,252,1650,1714,1764,1768,2614,2618,2668,2732,3118,3188,3192,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1691 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1691 4 (fun x => (if x<2668 then (if x<1764 then (if x<1650 then (if x<252 then 0 else 0) else (if x<1714 then 1 else 2)) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2618 then 2 else 1))) else (if x<3192 then (if x<3118 then (if x<2732 then 2 else 1) else (if x<3188 then 3 else 0)) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1692 : Finset ℕ := ([48,72,132,222,252,1628,1650,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2702,2732,2772,2776,3118,3158,3162,3188,3192,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1692 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1692 222 4
  · have he : independentCachedBranchMembers1692.erase 222=independentCachedBranchMembers1690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1690
  · have he : independentCachedBranchMembers1692.filter (independentCachedEdge 222)=independentCachedBranchMembers1691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1691
def independentCachedBranchMembers1693 : Finset ℕ := ([48,252,1628,1692,1734,1738,2638,2702,2772,2776,3118,3188,3192,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1693 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1693 4 (fun x => (if x<2772 then (if x<1734 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1692 then 1 else 2)) else (if x<2638 then (if x<1738 then 1 else 2) else (if x<2702 then 1 else 2))) else (if x<3192 then (if x<3118 then (if x<2776 then 1 else 2) else (if x<3188 then 3 else 0)) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1694 : Finset ℕ := ([18,48,72,132,222,252,1628,1650,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2702,2732,2772,2776,3118,3158,3162,3188,3192,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1694 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1694 18 4
  · have he : independentCachedBranchMembers1694.erase 18=independentCachedBranchMembers1692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1692
  · have he : independentCachedBranchMembers1694.filter (independentCachedEdge 18)=independentCachedBranchMembers1693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1693
def independentCachedBranchMembers1695 : Finset ℕ := ([18,48,72,132,222,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2606,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786,3118,3126,3130,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1695 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1695 2606 5
  · have he : independentCachedBranchMembers1695.erase 2606=independentCachedBranchMembers1681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1681
  · have he : independentCachedBranchMembers1695.filter (independentCachedEdge 2606)=independentCachedBranchMembers1694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1694
def independentCachedBranchMembers1696 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1696 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1696 1762 6
  · have he : independentCachedBranchMembers1696.erase 1762=independentCachedBranchMembers1592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1592
  · have he : independentCachedBranchMembers1696.filter (independentCachedEdge 1762)=independentCachedBranchMembers1695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1695
def independentCachedBranchMembers1697 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2680,2740,2764,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1697 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1697 6 (fun x => (if x<2740 then (if x<1678 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1644 then (if x<1626 then 1 else 2) else (if x<1652 then 1 else 2))) else (if x<1720 then (if x<1692 then (if x<1686 then 1 else 2) else (if x<1714 then 3 else 3)) else (if x<1752 then (if x<1738 then 2 else 3) else (if x<1764 then 1 else (if x<2680 then 3 else 0))))) else (if x<3226 then (if x<3164 then (if x<3132 then (if x<2764 then 0 else 0) else (if x<3150 then 4 else 4)) else (if x<3186 then (if x<3178 then 5 else 5) else (if x<3192 then 4 else 1))) else (if x<3270 then (if x<3244 then (if x<3238 then 1 else 4) else (if x<3252 then 5 else 2)) else (if x<3284 then (if x<3276 then 5 else 1) else (if x<3304 then 4 else (if x<3312 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1698 : Finset ℕ := ([132,252,1626,1644,1678,1692,1720,1764,2680,3132,3186,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1698 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1698 5 (fun x => (if x<1764 then (if x<1644 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1692 then (if x<1678 then 1 else 1) else (if x<1720 then 0 else 1))) else (if x<3238 then (if x<3132 then (if x<2680 then 0 else 1) else (if x<3186 then 2 else 2)) else (if x<3276 then (if x<3252 then 2 else 0) else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1699 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2680,2740,2764,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1699 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1699 3126 5
  · have he : independentCachedBranchMembers1699.erase 3126=independentCachedBranchMembers1697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1697
  · have he : independentCachedBranchMembers1699.filter (independentCachedEdge 3126)=independentCachedBranchMembers1698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1698
def independentCachedBranchMembers1700 : Finset ℕ := ([48,132,1594,1626,1652,1678,1692,1714,2680,2764,3132,3150,3164,3186,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1700 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1700 5 (fun x => (if x<3132 then (if x<1678 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1626 then 0 else (if x<1652 then 1 else 1))) else (if x<1714 then (if x<1692 then 0 else 1) else (if x<2680 then 1 else (if x<2764 then 0 else 0)))) else (if x<3238 then (if x<3164 then (if x<3150 then 2 else 2) else (if x<3186 then 1 else (if x<3226 then 0 else 1))) else (if x<3270 then (if x<3252 then 2 else 1) else (if x<3284 then 0 else (if x<3304 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1701 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2680,2740,2764,2792,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1701 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1701 2792 5
  · have he : independentCachedBranchMembers1701.erase 2792=independentCachedBranchMembers1699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1699
  · have he : independentCachedBranchMembers1701.filter (independentCachedEdge 2792)=independentCachedBranchMembers1700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1700
def independentCachedBranchMembers1702 : Finset ℕ := ([72,252,1626,1644,1652,1692,1714,1752,2680,2764,3126,3164,3178,3186,3226,3244,3252,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1702 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1702 5 (fun x => (if x<3126 then (if x<1692 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1644 then 1 else (if x<1652 then 0 else 1))) else (if x<1752 then (if x<1714 then 1 else 1) else (if x<2680 then 0 else (if x<2764 then 0 else 0)))) else (if x<3244 then (if x<3178 then (if x<3164 then 2 else 0) else (if x<3186 then 2 else (if x<3226 then 1 else 1))) else (if x<3270 then (if x<3252 then 2 else 1) else (if x<3304 then 2 else (if x<3312 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1703 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2680,2740,2758,2764,2792,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1703 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1703 2758 5
  · have he : independentCachedBranchMembers1703.erase 2758=independentCachedBranchMembers1701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1701
  · have he : independentCachedBranchMembers1703.filter (independentCachedEdge 2758)=independentCachedBranchMembers1702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1702
def independentCachedBranchMembers1704 : Finset ℕ := ([48,72,132,252,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1704 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1704 5 (fun x => (if x<3192 then (if x<3132 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else (if x<3126 then 0 else 1))) else (if x<3164 then (if x<3150 then 2 else 1) else (if x<3178 then 3 else (if x<3186 then 2 else 3)))) else (if x<3270 then (if x<3238 then (if x<3226 then 0 else 1) else (if x<3244 then 2 else (if x<3252 then 1 else 0))) else (if x<3284 then (if x<3276 then 3 else 0) else (if x<3304 then 1 else (if x<3312 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1705 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2680,2714,2740,2758,2764,2792,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1705 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1705 2714 5
  · have he : independentCachedBranchMembers1705.erase 2714=independentCachedBranchMembers1703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1703
  · have he : independentCachedBranchMembers1705.filter (independentCachedEdge 2714)=independentCachedBranchMembers1704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1704
def independentCachedBranchMembers1706 : Finset ℕ := ([72,252,1644,1686,1720,1738,1752,1764,2680,2764,3132,3150,3164,3186,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1706 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1706 5 (fun x => (if x<3132 then (if x<1738 then (if x<1644 then (if x<252 then 0 else 0) else (if x<1686 then 0 else (if x<1720 then 1 else 1))) else (if x<1764 then (if x<1752 then 1 else 0) else (if x<2680 then 1 else (if x<2764 then 0 else 0)))) else (if x<3238 then (if x<3164 then (if x<3150 then 2 else 2) else (if x<3186 then 0 else (if x<3226 then 2 else 1))) else (if x<3270 then (if x<3252 then 2 else 1) else (if x<3284 then 1 else (if x<3304 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1707 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2674,2680,2714,2740,2758,2764,2792,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1707 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1707 2674 5
  · have he : independentCachedBranchMembers1707.erase 2674=independentCachedBranchMembers1705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1705
  · have he : independentCachedBranchMembers1707.filter (independentCachedEdge 2674)=independentCachedBranchMembers1706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1706
def independentCachedBranchMembers1708 : Finset ℕ := ([48,132,1594,1678,1686,1720,1738,1764,2680,2764,3126,3164,3178,3186,3226,3244,3252,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1708 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1708 5 (fun x => (if x<3126 then (if x<1720 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1678 then 0 else (if x<1686 then 0 else 1))) else (if x<1764 then (if x<1738 then 1 else 1) else (if x<2680 then 1 else (if x<2764 then 0 else 0)))) else (if x<3244 then (if x<3178 then (if x<3164 then 2 else 2) else (if x<3186 then 2 else (if x<3226 then 0 else 1))) else (if x<3270 then (if x<3252 then 2 else 1) else (if x<3304 then 0 else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1709 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2652,2674,2680,2714,2740,2758,2764,2792,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1709 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1709 2652 5
  · have he : independentCachedBranchMembers1709.erase 2652=independentCachedBranchMembers1707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1707
  · have he : independentCachedBranchMembers1709.filter (independentCachedEdge 2652)=independentCachedBranchMembers1708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1708
def independentCachedBranchMembers1710 : Finset ℕ := ([48,72,1626,1644,1678,1714,1720,1738,2652,2740,2758,2764,3126,3132,3150,3186,3192,3226,3238,3244,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1710 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1710 5 (fun x => (if x<2764 then (if x<1714 then (if x<1626 then (if x<72 then 0 else 0) else (if x<1644 then 1 else (if x<1678 then 1 else 1))) else (if x<2652 then (if x<1720 then 0 else (if x<1738 then 1 else 0)) else (if x<2740 then 2 else (if x<2758 then 0 else 2)))) else (if x<3192 then (if x<3132 then (if x<3126 then 0 else 0) else (if x<3150 then 2 else (if x<3186 then 0 else 3))) else (if x<3244 then (if x<3226 then 1 else (if x<3238 then 1 else 2)) else (if x<3284 then 1 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1711 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2652,2674,2680,2714,2740,2758,2764,2772,2792,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1711 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1711 2772 5
  · have he : independentCachedBranchMembers1711.erase 2772=independentCachedBranchMembers1709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1709
  · have he : independentCachedBranchMembers1711.filter (independentCachedEdge 2772)=independentCachedBranchMembers1710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1710
def independentCachedBranchMembers1712 : Finset ℕ := ([48,72,1594,1652,1686,1714,1738,1752,2674,2740,2764,2792,3126,3150,3164,3178,3192,3226,3244,3270,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1712 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1712 5 (fun x => (if x<2792 then (if x<1714 then (if x<1594 then (if x<72 then 0 else 0) else (if x<1652 then 1 else (if x<1686 then 1 else 1))) else (if x<2674 then (if x<1738 then 0 else (if x<1752 then 0 else 1)) else (if x<2740 then 2 else (if x<2764 then 0 else 0)))) else (if x<3192 then (if x<3150 then (if x<3126 then 2 else 0) else (if x<3164 then 0 else (if x<3178 then 3 else 2))) else (if x<3270 then (if x<3226 then 1 else (if x<3244 then 1 else 2)) else (if x<3284 then 3 else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1713 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2652,2674,2680,2714,2732,2740,2758,2764,2772,2792,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1713 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1713 2732 5
  · have he : independentCachedBranchMembers1713.erase 2732=independentCachedBranchMembers1711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1711
  · have he : independentCachedBranchMembers1713.filter (independentCachedEdge 2732)=independentCachedBranchMembers1712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1712
def independentCachedBranchMembers1714 : Finset ℕ := ([132,252,1594,1652,1686,1692,1752,1764,2652,2740,2758,2764,3126,3132,3150,3186,3192,3226,3238,3244,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1714 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1714 5 (fun x => (if x<2764 then (if x<1692 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1686 then 1 else 1))) else (if x<2652 then (if x<1752 then 0 else (if x<1764 then 1 else 0)) else (if x<2740 then 2 else (if x<2758 then 0 else 2)))) else (if x<3192 then (if x<3132 then (if x<3126 then 0 else 1) else (if x<3150 then 2 else (if x<3186 then 2 else 3))) else (if x<3244 then (if x<3226 then 1 else (if x<3238 then 1 else 2)) else (if x<3284 then 0 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1715 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2792,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1715 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1715 2638 5
  · have he : independentCachedBranchMembers1715.erase 2638=independentCachedBranchMembers1713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1713
  · have he : independentCachedBranchMembers1715.filter (independentCachedEdge 2638)=independentCachedBranchMembers1714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1714
def independentCachedBranchMembers1716 : Finset ℕ := ([132,252,1626,1644,1678,1692,1720,1764,2674,2740,2764,2792,3126,3150,3164,3178,3192,3226,3244,3270,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1716 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1716 5 (fun x => (if x<2792 then (if x<1692 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1644 then 1 else (if x<1678 then 1 else 1))) else (if x<2674 then (if x<1720 then 0 else (if x<1764 then 1 else 0)) else (if x<2740 then 2 else (if x<2764 then 0 else 0)))) else (if x<3192 then (if x<3150 then (if x<3126 then 2 else 2) else (if x<3164 then 1 else (if x<3178 then 3 else 2))) else (if x<3270 then (if x<3226 then 1 else (if x<3244 then 1 else 0)) else (if x<3284 then 3 else (if x<3312 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1717 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2614,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2792,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1717 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1717 2614 5
  · have he : independentCachedBranchMembers1717.erase 2614=independentCachedBranchMembers1715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1715
  · have he : independentCachedBranchMembers1717.filter (independentCachedEdge 2614)=independentCachedBranchMembers1716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1716
def independentCachedBranchMembers1718 : Finset ℕ := ([72,132,1594,1626,1644,1686,1692,1738,2638,2674,2680,2740,2772,2792,3126,3132,3164,3178,3226,3238,3244,3270,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1718 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1718 5 (fun x => (if x<2772 then (if x<1692 then (if x<1626 then (if x<132 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 0 else (if x<1686 then 1 else 0))) else (if x<2674 then (if x<1738 then 1 else (if x<2638 then 1 else 2)) else (if x<2680 then 2 else (if x<2740 then 0 else 0)))) else (if x<3226 then (if x<3132 then (if x<2792 then 2 else (if x<3126 then 2 else 3)) else (if x<3164 then 1 else (if x<3178 then 3 else 0))) else (if x<3270 then (if x<3238 then 1 else (if x<3244 then 0 else 3)) else (if x<3276 then 3 else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1719 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2614,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2792,2800,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1719 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1719 2800 5
  · have he : independentCachedBranchMembers1719.erase 2800=independentCachedBranchMembers1717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1717
  · have he : independentCachedBranchMembers1719.filter (independentCachedEdge 2800)=independentCachedBranchMembers1718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1718
def independentCachedBranchMembers1720 : Finset ℕ := ([72,132,1626,1678,1686,1714,1752,1764,2614,2652,2680,2732,2740,2758,3132,3150,3178,3186,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1720 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1720 5 (fun x => (if x<2740 then (if x<1752 then (if x<1678 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1686 then 1 else (if x<1714 then 0 else 1))) else (if x<2652 then (if x<1764 then 1 else (if x<2614 then 1 else 2)) else (if x<2680 then 2 else (if x<2732 then 0 else 2)))) else (if x<3226 then (if x<3150 then (if x<2758 then 0 else (if x<3132 then 2 else 2)) else (if x<3178 then 3 else (if x<3186 then 0 else 3))) else (if x<3284 then (if x<3238 then 1 else (if x<3276 then 0 else 1)) else (if x<3304 then 3 else (if x<3312 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1721 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2792,2800,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1721 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1721 2620 5
  · have he : independentCachedBranchMembers1721.erase 2620=independentCachedBranchMembers1719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1719
  · have he : independentCachedBranchMembers1721.filter (independentCachedEdge 2620)=independentCachedBranchMembers1720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1720
def independentCachedBranchMembers1722 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1720,1752,2620,2652,2674,2758,2792,2800,3126,3150,3192,3226,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1722 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1722 5 (fun x => (if x<2652 then (if x<1644 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1594 then 0 else (if x<1626 then 1 else 2))) else (if x<1686 then (if x<1652 then 1 else (if x<1678 then 2 else 1)) else (if x<1752 then (if x<1720 then 2 else 2) else (if x<2620 then 1 else 3)))) else (if x<3150 then (if x<2792 then (if x<2674 then 4 else (if x<2758 then 3 else 4)) else (if x<2800 then 3 else (if x<3126 then 4 else 3))) else (if x<3244 then (if x<3192 then 4 else (if x<3226 then 0 else 1)) else (if x<3276 then (if x<3252 then 3 else 0) else (if x<3284 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1723 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1723 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1723 2786 5
  · have he : independentCachedBranchMembers1723.erase 2786=independentCachedBranchMembers1721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1721
  · have he : independentCachedBranchMembers1723.filter (independentCachedEdge 2786)=independentCachedBranchMembers1722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1722
def independentCachedBranchMembers1724 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1692,1714,1720,1738,1764,2614,2638,2732,2772,3164,3186,3192,3226,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1724 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1724 5 (fun x => (if x<2614 then (if x<1686 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1626 then 0 else (if x<1652 then 1 else 1))) else (if x<1720 then (if x<1692 then 1 else (if x<1714 then 2 else 2)) else (if x<1738 then 1 else (if x<1764 then 2 else 2)))) else (if x<3192 then (if x<2772 then (if x<2638 then 3 else (if x<2732 then 3 else 3)) else (if x<3164 then 3 else (if x<3186 then 4 else 4))) else (if x<3270 then (if x<3226 then 0 else (if x<3252 then 1 else 0)) else (if x<3276 then 4 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1725 : Finset ℕ := ([72,132,1626,1686,1692,1738,2638,2772,3164,3226,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound1725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1725 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1725 4 (fun x => (if x<2638 then (if x<1686 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1692 then 0 else (if x<1738 then 1 else 1))) else (if x<3226 then (if x<2772 then 2 else (if x<3164 then 2 else 2)) else (if x<3270 then 1 else (if x<3276 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1726 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1692,1714,1720,1738,1764,2614,2638,2732,2772,2800,3164,3186,3192,3226,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1726 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1726 2800 4
  · have he : independentCachedBranchMembers1726.erase 2800=independentCachedBranchMembers1724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1724
  · have he : independentCachedBranchMembers1726.filter (independentCachedEdge 2800)=independentCachedBranchMembers1725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1725
def independentCachedBranchMembers1727 : Finset ℕ := ([72,132,1626,1686,1714,1764,2614,2732,3186,3226,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1727 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1727 4 (fun x => (if x<2614 then (if x<1686 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<1714 then 0 else (if x<1764 then 1 else 1))) else (if x<3226 then (if x<2732 then 2 else (if x<3186 then 2 else 2)) else (if x<3276 then 1 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1728 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1692,1714,1720,1738,1764,2614,2620,2638,2732,2772,2800,3164,3186,3192,3226,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1728 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1728 2620 4
  · have he : independentCachedBranchMembers1728.erase 2620=independentCachedBranchMembers1726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1726
  · have he : independentCachedBranchMembers1728.filter (independentCachedEdge 2620)=independentCachedBranchMembers1727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1727
def independentCachedBranchMembers1729 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1729 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1729 2606 5
  · have he : independentCachedBranchMembers1729.erase 2606=independentCachedBranchMembers1723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1723
  · have he : independentCachedBranchMembers1729.filter (independentCachedEdge 2606)=independentCachedBranchMembers1728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1728
def independentCachedBranchMembers1730 : Finset ℕ := ([72,252,1626,1644,1686,1714,1738,1752,2652,2680,2740,2764,2792,3126,3150,3164,3178,3192,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1730 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1730 5 (fun x => (if x<2740 then (if x<1714 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1644 then 1 else (if x<1686 then 0 else 1))) else (if x<1752 then (if x<1738 then 2 else 2) else (if x<2652 then 0 else (if x<2680 then 0 else 1)))) else (if x<3164 then (if x<2792 then (if x<2764 then 1 else 2) else (if x<3126 then 0 else (if x<3150 then 2 else 2))) else (if x<3238 then (if x<3178 then 3 else (if x<3192 then 1 else 0)) else (if x<3276 then 1 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1731 : Finset ℕ := ([1626,1644,1686,1752,2652,2792,3164,3178,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1731 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1731 4 (fun x => (if x<2792 then (if x<1686 then (if x<1644 then 0 else 0) else (if x<1752 then 1 else (if x<2652 then 1 else 0))) else (if x<3178 then (if x<3164 then 1 else 2) else (if x<3238 then 2 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1732 : Finset ℕ := ([48,72,252,1626,1644,1686,1714,1738,1752,2652,2680,2740,2764,2792,3126,3150,3164,3178,3192,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1732 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1732 48 4
  · have he : independentCachedBranchMembers1732.erase 48=independentCachedBranchMembers1730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1730
  · have he : independentCachedBranchMembers1732.filter (independentCachedEdge 48)=independentCachedBranchMembers1731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1731
def independentCachedBranchMembers1733 : Finset ℕ := ([1644,1752,2652,2680,2740,2764,2792,3126,3150,3178,3238] : List ℕ).toFinset
theorem independentCachedBranchBound1733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1733 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1733 4 (fun x => (if x<2764 then (if x<2652 then (if x<1752 then 0 else 0) else (if x<2680 then 0 else (if x<2740 then 1 else 1))) else (if x<3150 then (if x<2792 then 1 else (if x<3126 then 0 else 2)) else (if x<3178 then 2 else (if x<3238 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1734 : Finset ℕ := ([48,72,252,1626,1644,1686,1714,1738,1752,2652,2680,2740,2764,2792,3126,3150,3164,3178,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1734 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1734 3252 4
  · have he : independentCachedBranchMembers1734.erase 3252=independentCachedBranchMembers1732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1732
  · have he : independentCachedBranchMembers1734.filter (independentCachedEdge 3252)=independentCachedBranchMembers1733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1733
def independentCachedBranchMembers1735 : Finset ℕ := ([252,1686,1752,2652,2740,2764,3126,3150,3192,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1735 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1735 4 (fun x => (if x<2764 then (if x<1752 then (if x<1686 then 0 else 1) else (if x<2652 then 0 else (if x<2740 then 0 else 1))) else (if x<3192 then (if x<3126 then 2 else (if x<3150 then 1 else 2)) else (if x<3238 then 0 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1736 : Finset ℕ := ([48,72,252,1626,1644,1686,1714,1738,1752,2638,2652,2680,2740,2764,2792,3126,3150,3164,3178,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1736 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1736 2638 4
  · have he : independentCachedBranchMembers1736.erase 2638=independentCachedBranchMembers1734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1734
  · have he : independentCachedBranchMembers1736.filter (independentCachedEdge 2638)=independentCachedBranchMembers1735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1735
def independentCachedBranchMembers1737 : Finset ℕ := ([252,1626,1644,2740,2764,2792,3126,3150,3164,3178,3192] : List ℕ).toFinset
theorem independentCachedBranchBound1737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1737 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1737 4 (fun x => (if x<2792 then (if x<1644 then (if x<1626 then 0 else 1) else (if x<2740 then 0 else (if x<2764 then 1 else 0))) else (if x<3164 then (if x<3126 then 2 else (if x<3150 then 2 else 1)) else (if x<3178 then 0 else (if x<3192 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1738 : Finset ℕ := ([48,72,252,1626,1644,1686,1714,1738,1752,2614,2638,2652,2680,2740,2764,2792,3126,3150,3164,3178,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1738 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1738 2614 4
  · have he : independentCachedBranchMembers1738.erase 2614=independentCachedBranchMembers1736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1736
  · have he : independentCachedBranchMembers1738.filter (independentCachedEdge 2614)=independentCachedBranchMembers1737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1737
def independentCachedBranchMembers1739 : Finset ℕ := ([1644,1714,1738,1752,2614,2638,2652,2792,3126,3150,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1739 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1739 4 (fun x => (if x<2652 then (if x<1752 then (if x<1714 then 0 else (if x<1738 then 1 else 0)) else (if x<2614 then 1 else (if x<2638 then 1 else 0))) else (if x<3150 then (if x<2792 then 1 else (if x<3126 then 0 else 2)) else (if x<3164 then 2 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1740 : Finset ℕ := ([48,72,132,252,1626,1644,1686,1714,1738,1752,2614,2638,2652,2680,2740,2764,2792,3126,3150,3164,3178,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1740 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1740 132 4
  · have he : independentCachedBranchMembers1740.erase 132=independentCachedBranchMembers1738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1738
  · have he : independentCachedBranchMembers1740.filter (independentCachedEdge 132)=independentCachedBranchMembers1739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1739
def independentCachedBranchMembers1741 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1741 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1741 1746 5
  · have he : independentCachedBranchMembers1741.erase 1746=independentCachedBranchMembers1729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1729
  · have he : independentCachedBranchMembers1741.filter (independentCachedEdge 1746)=independentCachedBranchMembers1740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1740
def independentCachedBranchMembers1742 : Finset ℕ := ([72,132,1626,1644,1652,1678,1692,1714,1720,2680,2732,2740,3150,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1742 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1742 5 (fun x => (if x<2732 then (if x<1678 then (if x<1626 then (if x<132 then 0 else 0) else (if x<1644 then 0 else (if x<1652 then 1 else 2))) else (if x<1714 then (if x<1692 then 1 else 2) else (if x<1720 then 2 else (if x<2680 then 1 else 0)))) else (if x<3186 then (if x<3150 then (if x<2740 then 1 else 0) else (if x<3164 then 3 else (if x<3178 then 2 else 0))) else (if x<3238 then (if x<3192 then 2 else (if x<3226 then 3 else 2)) else (if x<3244 then 0 else (if x<3252 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1743 : Finset ℕ := ([132,1678,1720,2680,3164,3178,3186,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1743 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1743 4 (fun x => (if x<3178 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<2680 then 1 else (if x<3164 then 0 else 2))) else (if x<3226 then (if x<3186 then 2 else 0) else (if x<3244 then 1 else (if x<3252 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1744 : Finset ℕ := ([72,132,1626,1644,1652,1678,1692,1714,1720,2652,2680,2732,2740,3150,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1744 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1744 2652 4
  · have he : independentCachedBranchMembers1744.erase 2652=independentCachedBranchMembers1742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1742
  · have he : independentCachedBranchMembers1744.filter (independentCachedEdge 2652)=independentCachedBranchMembers1743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1743
def independentCachedBranchMembers1745 : Finset ℕ := ([72,132,3150,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1745 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1745 4 (fun x => (if x<3186 then (if x<3150 then (if x<132 then 0 else 0) else (if x<3164 then 1 else (if x<3178 then 2 else 0))) else (if x<3238 then (if x<3192 then 1 else (if x<3226 then 3 else 1)) else (if x<3244 then 0 else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1746 : Finset ℕ := ([72,132,1626,1644,1652,1678,1692,1714,1720,2652,2680,2714,2732,2740,3150,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1746 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1746 2714 4
  · have he : independentCachedBranchMembers1746.erase 2714=independentCachedBranchMembers1744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1744
  · have he : independentCachedBranchMembers1746.filter (independentCachedEdge 2714)=independentCachedBranchMembers1745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1745
def independentCachedBranchMembers1747 : Finset ℕ := ([72,1644,1720,2680,2732,3150,3164,3186,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1747 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1747 4 (fun x => (if x<3150 then (if x<1720 then (if x<1644 then 0 else 0) else (if x<2680 then 1 else (if x<2732 then 0 else 1))) else (if x<3226 then (if x<3164 then 2 else (if x<3186 then 0 else 2)) else (if x<3238 then 2 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1748 : Finset ℕ := ([72,132,1626,1644,1652,1678,1692,1714,1720,2652,2674,2680,2714,2732,2740,3150,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1748 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1748 2674 4
  · have he : independentCachedBranchMembers1748.erase 2674=independentCachedBranchMembers1746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1746
  · have he : independentCachedBranchMembers1748.filter (independentCachedEdge 2674)=independentCachedBranchMembers1747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1747
def independentCachedBranchMembers1749 : Finset ℕ := ([132,1652,1692,2652,2740,3150,3186,3192,3226,3238,3244] : List ℕ).toFinset
theorem independentCachedBranchBound1749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1749 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1749 4 (fun x => (if x<3150 then (if x<1692 then (if x<1652 then 0 else 1) else (if x<2652 then 0 else (if x<2740 then 1 else 0))) else (if x<3226 then (if x<3186 then 2 else (if x<3192 then 2 else 1)) else (if x<3238 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1750 : Finset ℕ := ([72,132,1626,1644,1652,1678,1692,1714,1720,2638,2652,2674,2680,2714,2732,2740,3150,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1750 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1750 2638 4
  · have he : independentCachedBranchMembers1750.erase 2638=independentCachedBranchMembers1748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1748
  · have he : independentCachedBranchMembers1750.filter (independentCachedEdge 2638)=independentCachedBranchMembers1749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1749
def independentCachedBranchMembers1751 : Finset ℕ := ([1644,1678,1692,1714,2638,2652,2674,2732,3150,3164,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound1751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1751 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1751 4 (fun x => (if x<2674 then (if x<1714 then (if x<1678 then 0 else (if x<1692 then 0 else 1)) else (if x<2638 then 1 else (if x<2652 then 0 else 1))) else (if x<3164 then (if x<2732 then 1 else (if x<3150 then 0 else 2)) else (if x<3186 then 3 else (if x<3244 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1752 : Finset ℕ := ([72,132,1626,1644,1652,1678,1686,1692,1714,1720,2638,2652,2674,2680,2714,2732,2740,3150,3164,3178,3186,3192,3226,3238,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1752 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1752 1686 4
  · have he : independentCachedBranchMembers1752.erase 1686=independentCachedBranchMembers1750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1750
  · have he : independentCachedBranchMembers1752.filter (independentCachedEdge 1686)=independentCachedBranchMembers1751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1751
def independentCachedBranchMembers1753 : Finset ℕ := ([48,72,132,192,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1753 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1753 192 5
  · have he : independentCachedBranchMembers1753.erase 192=independentCachedBranchMembers1741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1741
  · have he : independentCachedBranchMembers1753.filter (independentCachedEdge 192)=independentCachedBranchMembers1752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1752
def independentCachedBranchMembers1754 : Finset ℕ := ([72,132,1594,1626,1652,1686,1720,1738,1752,1764,2614,2680,2714,2740,2758,2772,2792,3126,3178,3192,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1754 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1754 5 (fun x => (if x<2740 then (if x<1720 then (if x<1626 then (if x<132 then 0 else (if x<1594 then 0 else 1)) else (if x<1652 then 0 else (if x<1686 then 1 else 0))) else (if x<1764 then (if x<1738 then 2 else (if x<1752 then 2 else 1)) else (if x<2680 then (if x<2614 then 2 else 1) else (if x<2714 then 0 else 1)))) else (if x<3192 then (if x<2792 then (if x<2758 then 0 else (if x<2772 then 2 else 1)) else (if x<3126 then 2 else (if x<3178 then 3 else 0))) else (if x<3252 then (if x<3226 then 3 else (if x<3238 then 3 else 0)) else (if x<3284 then (if x<3270 then 4 else 4) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1755 : Finset ℕ := ([12,48,72,132,192,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1755 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1755 12 5
  · have he : independentCachedBranchMembers1755.erase 12=independentCachedBranchMembers1753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1753
  · have he : independentCachedBranchMembers1755.filter (independentCachedEdge 12)=independentCachedBranchMembers1754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1754
def independentCachedBranchMembers1756 : Finset ℕ := ([1594,1626,1644,1652,1678,1686,1720,1752,2614,2638,2680,2714,2732,2740,2764,2772,2786,3132,3164,3178,3186,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1756 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1756 5 (fun x => (if x<2732 then (if x<1720 then (if x<1652 then (if x<1626 then 0 else (if x<1644 then 1 else 0)) else (if x<1678 then 1 else (if x<1686 then 0 else 1))) else (if x<2638 then (if x<1752 then 1 else (if x<2614 then 0 else 2)) else (if x<2680 then 2 else (if x<2714 then 0 else 0)))) else (if x<3164 then (if x<2772 then (if x<2740 then 2 else (if x<2764 then 1 else 0)) else (if x<2786 then 2 else (if x<3132 then 2 else 3))) else (if x<3238 then (if x<3178 then 4 else (if x<3186 then 3 else 4)) else (if x<3304 then (if x<3270 then 3 else 4) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1757 : Finset ℕ := ([1594,1626,1678,1686,2614,2638,2714,2786,3178,3186,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1757 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1757 4 (fun x => (if x<2714 then (if x<1686 then (if x<1626 then 0 else (if x<1678 then 1 else 0)) else (if x<2614 then 1 else (if x<2638 then 2 else 2))) else (if x<3186 then (if x<2786 then 0 else (if x<3178 then 2 else 1)) else (if x<3238 then 3 else (if x<3270 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1758 : Finset ℕ := ([252,1594,1626,1644,1652,1678,1686,1720,1752,2614,2638,2680,2714,2732,2740,2764,2772,2786,3132,3164,3178,3186,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1758 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1758 252 4
  · have he : independentCachedBranchMembers1758.erase 252=independentCachedBranchMembers1756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1756
  · have he : independentCachedBranchMembers1758.filter (independentCachedEdge 252)=independentCachedBranchMembers1757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1757
def independentCachedBranchMembers1759 : Finset ℕ := ([1644,1652,1720,1752,2614,2638,2714,2786,3132,3164,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1759 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1759 4 (fun x => (if x<2714 then (if x<1752 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<2614 then 1 else (if x<2638 then 1 else 0))) else (if x<3164 then (if x<2786 then 0 else (if x<3132 then 2 else 2)) else (if x<3304 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1760 : Finset ℕ := ([132,252,1594,1626,1644,1652,1678,1686,1720,1752,2614,2638,2680,2714,2732,2740,2764,2772,2786,3132,3164,3178,3186,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1760 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1760 132 4
  · have he : independentCachedBranchMembers1760.erase 132=independentCachedBranchMembers1758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1758
  · have he : independentCachedBranchMembers1760.filter (independentCachedEdge 132)=independentCachedBranchMembers1759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1759
def independentCachedBranchMembers1761 : Finset ℕ := ([1594,1652,1678,1720,2714,2732,2772,2786,3132,3186,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1761 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1761 4 (fun x => (if x<2772 then (if x<1720 then (if x<1652 then 0 else (if x<1678 then 0 else 1)) else (if x<2714 then 1 else (if x<2732 then 0 else 1))) else (if x<3186 then (if x<2786 then 0 else (if x<3132 then 2 else 2)) else (if x<3270 then 2 else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1762 : Finset ℕ := ([72,132,252,1594,1626,1644,1652,1678,1686,1720,1752,2614,2638,2680,2714,2732,2740,2764,2772,2786,3132,3164,3178,3186,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1762 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1762 72 4
  · have he : independentCachedBranchMembers1762.erase 72=independentCachedBranchMembers1760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1760
  · have he : independentCachedBranchMembers1762.filter (independentCachedEdge 72)=independentCachedBranchMembers1761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1761
def independentCachedBranchMembers1763 : Finset ℕ := ([1626,1644,1686,1752,2714,2732,2772,2786,3164,3178,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1763 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1763 4 (fun x => (if x<2772 then (if x<1752 then (if x<1644 then 0 else (if x<1686 then 0 else 1)) else (if x<2714 then 1 else (if x<2732 then 0 else 0))) else (if x<3178 then (if x<2786 then 1 else (if x<3164 then 2 else 2)) else (if x<3238 then 2 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1764 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1720,1752,2614,2638,2680,2714,2732,2740,2764,2772,2786,3132,3164,3178,3186,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1764 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1764 48 4
  · have he : independentCachedBranchMembers1764.erase 48=independentCachedBranchMembers1762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1762
  · have he : independentCachedBranchMembers1764.filter (independentCachedEdge 48)=independentCachedBranchMembers1763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1763
def independentCachedBranchMembers1765 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1720,2614,2638,2732,2772,3164,3186,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1765 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1765 4 (fun x => (if x<2614 then (if x<1626 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1686 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3164 then (if x<2732 then (if x<2638 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1766 : Finset ℕ := ([48,72,132,252,1594,1626,1644,1652,1678,1686,1720,1752,2606,2614,2638,2680,2714,2732,2740,2764,2772,2786,3132,3164,3178,3186,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1766 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1766 2606 4
  · have he : independentCachedBranchMembers1766.erase 2606=independentCachedBranchMembers1764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1764
  · have he : independentCachedBranchMembers1766.filter (independentCachedEdge 2606)=independentCachedBranchMembers1765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1765
def independentCachedBranchMembers1767 : Finset ℕ := ([12,48,72,132,192,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1767 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1767 3298 5
  · have he : independentCachedBranchMembers1767.erase 3298=independentCachedBranchMembers1755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1755
  · have he : independentCachedBranchMembers1767.filter (independentCachedEdge 3298)=independentCachedBranchMembers1766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1766
def independentCachedBranchMembers1768 : Finset ℕ := ([12,48,192,252,1594,1644,1678,1692,1714,1738,1752,1764,2606,2620,2680,2714,2740,2764,2786,2800,3126,3150,3164,3186,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1768 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1768 5 (fun x => (if x<2680 then (if x<1692 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1644 then (if x<1594 then 0 else 1) else (if x<1678 then 1 else 1))) else (if x<1752 then (if x<1714 then 2 else (if x<1738 then 2 else 2)) else (if x<2606 then (if x<1764 then 1 else 2) else (if x<2620 then 1 else 0)))) else (if x<3150 then (if x<2764 then (if x<2714 then 1 else (if x<2740 then 1 else 2)) else (if x<2800 then (if x<2786 then 0 else 2) else (if x<3126 then 0 else 3))) else (if x<3244 then (if x<3164 then 3 else (if x<3186 then 4 else 4)) else (if x<3284 then (if x<3270 then 3 else 4) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1769 : Finset ℕ := ([12,192,1644,1714,1738,1752,2620,2786,2800,3126,3150,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1769 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1769 4 (fun x => (if x<2620 then (if x<1714 then (if x<192 then 0 else (if x<1644 then 0 else 1)) else (if x<1738 then 2 else (if x<1752 then 1 else 2))) else (if x<3126 then (if x<2786 then 0 else (if x<2800 then 3 else 0)) else (if x<3164 then (if x<3150 then 2 else 1) else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1770 : Finset ℕ := ([12,192,3126,3150,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1770 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1770 3 (fun x => (if x<3150 then (if x<192 then 0 else (if x<3126 then 0 else 1)) else (if x<3164 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1771 : Finset ℕ := ([12,192,1644,1714,1738,1752,2620,2714,2786,2800,3126,3150,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1771 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1771 2714 3
  · have he : independentCachedBranchMembers1771.erase 2714=independentCachedBranchMembers1769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1769
  · have he : independentCachedBranchMembers1771.filter (independentCachedEdge 2714)=independentCachedBranchMembers1770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1770
def independentCachedBranchMembers1772 : Finset ℕ := ([1714,1738,2620,2800,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1772 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1772 3 (fun x => (if x<2800 then (if x<1738 then 0 else (if x<2620 then 0 else 1)) else (if x<3164 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1773 : Finset ℕ := ([12,192,1644,1714,1738,1752,2606,2620,2714,2786,2800,3126,3150,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1773 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1773 2606 3
  · have he : independentCachedBranchMembers1773.erase 2606=independentCachedBranchMembers1771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1771
  · have he : independentCachedBranchMembers1773.filter (independentCachedEdge 2606)=independentCachedBranchMembers1772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1772
def independentCachedBranchMembers1774 : Finset ℕ := ([12,48,132,192,252,1594,1644,1678,1692,1714,1738,1752,1764,2606,2620,2680,2714,2740,2764,2786,2800,3126,3150,3164,3186,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1774 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1774 132 4
  · have he : independentCachedBranchMembers1774.erase 132=independentCachedBranchMembers1768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1768
  · have he : independentCachedBranchMembers1774.filter (independentCachedEdge 132)=independentCachedBranchMembers1773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1773
def independentCachedBranchMembers1775 : Finset ℕ := ([12,192,1594,1678,1692,1764,2620,2786,2800,3186,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1775 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1775 4 (fun x => (if x<2620 then (if x<1678 then (if x<192 then 0 else (if x<1594 then 0 else 1)) else (if x<1692 then 1 else (if x<1764 then 2 else 2))) else (if x<3186 then (if x<2786 then 0 else (if x<2800 then 2 else 0)) else (if x<3270 then (if x<3244 then 1 else 3) else (if x<3284 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1776 : Finset ℕ := ([12,192,3186,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1776 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1776 3 (fun x => (if x<3244 then (if x<192 then 0 else (if x<3186 then 0 else 1)) else (if x<3270 then 2 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1777 : Finset ℕ := ([12,192,1594,1678,1692,1764,2620,2714,2786,2800,3186,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1777 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1777 2714 3
  · have he : independentCachedBranchMembers1777.erase 2714=independentCachedBranchMembers1775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1775
  · have he : independentCachedBranchMembers1777.filter (independentCachedEdge 2714)=independentCachedBranchMembers1776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1776
def independentCachedBranchMembers1778 : Finset ℕ := ([1692,1764,2620,2800,3186,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1778 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1778 3 (fun x => (if x<2800 then (if x<1764 then 0 else (if x<2620 then 0 else 1)) else (if x<3186 then 1 else (if x<3270 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1779 : Finset ℕ := ([12,192,1594,1678,1692,1764,2606,2620,2714,2786,2800,3186,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1779 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1779 2606 3
  · have he : independentCachedBranchMembers1779.erase 2606=independentCachedBranchMembers1777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1777
  · have he : independentCachedBranchMembers1779.filter (independentCachedEdge 2606)=independentCachedBranchMembers1778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1778
def independentCachedBranchMembers1780 : Finset ℕ := ([12,48,72,132,192,252,1594,1644,1678,1692,1714,1738,1752,1764,2606,2620,2680,2714,2740,2764,2786,2800,3126,3150,3164,3186,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1780 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1780 72 4
  · have he : independentCachedBranchMembers1780.erase 72=independentCachedBranchMembers1774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1774
  · have he : independentCachedBranchMembers1780.filter (independentCachedEdge 72)=independentCachedBranchMembers1779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1779
def independentCachedBranchMembers1781 : Finset ℕ := ([12,48,72,132,192,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800,3126,3132,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1781 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1781 3158 5
  · have he : independentCachedBranchMembers1781.erase 3158=independentCachedBranchMembers1767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1767
  · have he : independentCachedBranchMembers1781.filter (independentCachedEdge 3158)=independentCachedBranchMembers1780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1780
def independentCachedBranchMembers1782 : Finset ℕ := ([132,252,1626,1652,1686,1692,1714,1720,1738,1764,2606,2652,2674,2680,2714,2740,2758,2764,2792,3126,3132,3150,3178,3238,3244,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1782 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1782 5 (fun x => (if x<2680 then (if x<1714 then (if x<1652 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1686 then 1 else (if x<1692 then 1 else 0))) else (if x<1764 then (if x<1720 then 2 else (if x<1738 then 1 else 2)) else (if x<2652 then (if x<2606 then 0 else 3) else (if x<2674 then 3 else 3)))) else (if x<3132 then (if x<2758 then (if x<2714 then 1 else (if x<2740 then 1 else 0)) else (if x<2792 then (if x<2764 then 3 else 0) else (if x<3126 then 3 else 2))) else (if x<3238 then (if x<3150 then 4 else (if x<3178 then 2 else 4)) else (if x<3284 then (if x<3244 then 4 else 0) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1783 : Finset ℕ := ([1652,1692,1720,1764,2606,2674,2714,2758,3132,3244,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1783 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1783 4 (fun x => (if x<2714 then (if x<1764 then (if x<1692 then 0 else (if x<1720 then 0 else 1)) else (if x<2606 then 1 else (if x<2674 then 2 else 0))) else (if x<3244 then (if x<2758 then 0 else (if x<3132 then 1 else 2)) else (if x<3284 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1784 : Finset ℕ := ([72,132,252,1626,1652,1686,1692,1714,1720,1738,1764,2606,2652,2674,2680,2714,2740,2758,2764,2792,3126,3132,3150,3178,3238,3244,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1784 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1784 72 4
  · have he : independentCachedBranchMembers1784.erase 72=independentCachedBranchMembers1782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1782
  · have he : independentCachedBranchMembers1784.filter (independentCachedEdge 72)=independentCachedBranchMembers1783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1783
def independentCachedBranchMembers1785 : Finset ℕ := ([1626,1686,1692,1764,2606,2652,2714,2792,3178,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1785 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1785 4 (fun x => (if x<2714 then (if x<1764 then (if x<1686 then 0 else (if x<1692 then 0 else 1)) else (if x<2606 then 1 else (if x<2652 then 2 else 2))) else (if x<3238 then (if x<2792 then 0 else (if x<3178 then 2 else 3)) else (if x<3244 then 3 else (if x<3284 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1786 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1692,1714,1720,1738,1764,2606,2652,2674,2680,2714,2740,2758,2764,2792,3126,3132,3150,3178,3238,3244,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1786 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1786 48 4
  · have he : independentCachedBranchMembers1786.erase 48=independentCachedBranchMembers1784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1784
  · have he : independentCachedBranchMembers1786.filter (independentCachedEdge 48)=independentCachedBranchMembers1785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1785
def independentCachedBranchMembers1787 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1720,2652,2674,2758,2792,3126,3150,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1787 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1787 4 (fun x => (if x<2652 then (if x<1626 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1686 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3126 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3244 then (if x<3150 then 3 else 3) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1788 : Finset ℕ := ([48,72,132,252,1626,1652,1686,1692,1714,1720,1738,1764,2606,2652,2674,2680,2714,2740,2758,2764,2786,2792,3126,3132,3150,3178,3238,3244,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1788 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1788 2786 4
  · have he : independentCachedBranchMembers1788.erase 2786=independentCachedBranchMembers1786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1786
  · have he : independentCachedBranchMembers1788.filter (independentCachedEdge 2786)=independentCachedBranchMembers1787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1787
def independentCachedBranchMembers1789 : Finset ℕ := ([12,48,72,132,192,252,1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1746,1752,1764,2606,2614,2620,2638,2652,2674,2680,2714,2732,2740,2758,2764,2772,2786,2792,2800,3118,3126,3132,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1789 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1789 3118 5
  · have he : independentCachedBranchMembers1789.erase 3118=independentCachedBranchMembers1781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1781
  · have he : independentCachedBranchMembers1789.filter (independentCachedEdge 3118)=independentCachedBranchMembers1788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1788
def independentCachedBranchMembers1790 : Finset ℕ := ([132,252,1594,1644,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2732,2758,2772,2792,3132,3158,3178,3192,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1790 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1790 5 (fun x => (if x<2674 then (if x<1714 then (if x<1644 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1678 then 1 else (if x<1692 then 1 else 0))) else (if x<1764 then (if x<1738 then 2 else (if x<1752 then 2 else 1)) else (if x<2638 then (if x<2614 then 0 else 2) else (if x<2652 then 2 else 3)))) else (if x<3178 then (if x<2772 then (if x<2732 then 3 else (if x<2758 then 0 else 3)) else (if x<3132 then (if x<2792 then 0 else 3) else (if x<3158 then 4 else 3))) else (if x<3238 then (if x<3192 then 4 else (if x<3226 then 1 else 1)) else (if x<3276 then (if x<3252 then 4 else 0) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1791 : Finset ℕ := ([1594,1678,1692,1764,2674,2732,2758,2772,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1791 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1791 4 (fun x => (if x<2758 then (if x<1764 then (if x<1678 then 0 else (if x<1692 then 0 else 1)) else (if x<2674 then 1 else (if x<2732 then 0 else 1))) else (if x<3158 then (if x<2772 then 0 else (if x<3132 then 1 else 2)) else (if x<3226 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
