/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch58
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4672 : Finset ℕ := ([34,72,132,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3118,3162,3178,3188,3222,3238,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4672 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4672 34 4
  · have he : independentCachedBranchMembers4672.erase 34=independentCachedBranchMembers4670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4670
  · have he : independentCachedBranchMembers4672.filter (independentCachedEdge 34)=independentCachedBranchMembers4671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4671
def independentCachedBranchMembers4673 : Finset ℕ := ([34,72,132,238,1590,1628,1678,1764,2618,2638,2716,2792,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4673 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4673 4 (fun x => (if x<2618 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3118 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4674 : Finset ℕ := ([34,72,132,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4674 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4674 3282 4
  · have he : independentCachedBranchMembers4674.erase 3282=independentCachedBranchMembers4672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4672
  · have he : independentCachedBranchMembers4674.filter (independentCachedEdge 3282)=independentCachedBranchMembers4673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4673
def independentCachedBranchMembers4675 : Finset ℕ := ([34,72,132,238,1644,1650,1738,1748,2732,2738,2758,2776,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4675 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4675 4 (fun x => (if x<2732 then (if x<1644 then (if x<132 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1738 then (if x<1650 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3118 then (if x<2758 then (if x<2738 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4676 : Finset ℕ := ([34,72,132,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4676 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4676 3102 4
  · have he : independentCachedBranchMembers4676.erase 3102=independentCachedBranchMembers4674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4674
  · have he : independentCachedBranchMembers4676.filter (independentCachedEdge 3102)=independentCachedBranchMembers4675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4675
def independentCachedBranchMembers4677 : Finset ℕ := ([1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound4677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4677 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4677 4 (fun x => (if x<2618 then (if x<1678 then (if x<1644 then (if x<1628 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1764 then 1 else 0))) else (if x<2738 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2776 then (if x<2758 then 3 else 3) else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4678 : Finset ℕ := ([34,72,132,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4678 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4678 3072 4
  · have he : independentCachedBranchMembers4678.erase 3072=independentCachedBranchMembers4676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4676
  · have he : independentCachedBranchMembers4678.filter (independentCachedEdge 3072)=independentCachedBranchMembers4677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4677
def independentCachedBranchMembers4679 : Finset ℕ := ([34,238,1590,1644,1650,1764,2618,2732,2738,2792,3118,3178,3188,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4679 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4679 4 (fun x => (if x<2738 then (if x<1650 then (if x<1590 then (if x<238 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2732 then 2 else 2))) else (if x<3188 then (if x<3118 then (if x<2792 then 1 else 1) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4680 : Finset ℕ := ([34,72,132,222,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4680 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4680 222 4
  · have he : independentCachedBranchMembers4680.erase 222=independentCachedBranchMembers4678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4678
  · have he : independentCachedBranchMembers4680.filter (independentCachedEdge 222)=independentCachedBranchMembers4679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4679
def independentCachedBranchMembers4681 : Finset ℕ := ([72,132,1628,1644,1650,1678,2638,2716,2732,2738,3162,3178,3188,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4681 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4681 4 (fun x => (if x<2732 then (if x<1650 then (if x<1628 then (if x<132 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2638 then (if x<1678 then 1 else 2) else (if x<2716 then 2 else 1))) else (if x<3188 then (if x<3162 then (if x<2738 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3222 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4682 : Finset ℕ := ([34,72,132,192,222,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4682 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4682 192 4
  · have he : independentCachedBranchMembers4682.erase 192=independentCachedBranchMembers4680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4680
  · have he : independentCachedBranchMembers4682.filter (independentCachedEdge 192)=independentCachedBranchMembers4681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4681
def independentCachedBranchMembers4683 : Finset ℕ := ([34,238,1628,1678,1738,1748,2638,2716,2758,2776,3118,3178,3188,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4683 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4683 4 (fun x => (if x<2758 then (if x<1738 then (if x<1628 then (if x<238 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1748 then 2 else 2) else (if x<2716 then 1 else 1))) else (if x<3188 then (if x<3118 then (if x<2776 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4684 : Finset ℕ := ([18,34,72,132,192,222,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4684 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4684 18 4
  · have he : independentCachedBranchMembers4684.erase 18=independentCachedBranchMembers4682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4682
  · have he : independentCachedBranchMembers4684.filter (independentCachedEdge 18)=independentCachedBranchMembers4683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4683
def independentCachedBranchMembers4685 : Finset ℕ := ([72,132,1590,1738,1748,1764,2618,2758,2776,2792,3162,3178,3188,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4685 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4685 4 (fun x => (if x<2776 then (if x<1748 then (if x<1590 then (if x<132 then 0 else 0) else (if x<1738 then 1 else 2)) else (if x<2618 then (if x<1764 then 1 else 2) else (if x<2758 then 1 else 2))) else (if x<3188 then (if x<3162 then (if x<2792 then 1 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3222 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4686 : Finset ℕ := ([12,18,34,72,132,192,222,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4686 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4686 12 4
  · have he : independentCachedBranchMembers4686.erase 12=independentCachedBranchMembers4684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4684
  · have he : independentCachedBranchMembers4686.filter (independentCachedEdge 12)=independentCachedBranchMembers4685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4685
def independentCachedBranchMembers4687 : Finset ℕ := ([12,18,34,36,72,80,130,132,192,222,238,246,1582,1590,1626,1628,1644,1650,1652,1678,1686,1702,1720,1738,1740,1746,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3072,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4687 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4687 1652 5
  · have he : independentCachedBranchMembers4687.erase 1652=independentCachedBranchMembers4667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4667
  · have he : independentCachedBranchMembers4687.filter (independentCachedEdge 1652)=independentCachedBranchMembers4686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4686
def independentCachedBranchMembers4688 : Finset ℕ := ([130,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3126,3164,3178,3188,3214,3238,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4688 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4688 5 (fun x => (if x<2732 then (if x<1686 then (if x<1626 then (if x<246 then 0 else (if x<1582 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1762 then (if x<1738 then 0 else (if x<1748 then 2 else 2)) else (if x<2646 then (if x<2620 then 0 else 3) else (if x<2714 then 3 else 3)))) else (if x<3178 then (if x<2776 then (if x<2738 then 1 else (if x<2758 then 0 else 0)) else (if x<3126 then (if x<2800 then 1 else 3) else (if x<3164 then 4 else 4))) else (if x<3238 then (if x<3188 then 2 else (if x<3214 then 2 else 4)) else (if x<3282 then (if x<3256 then 0 else 3) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4689 : Finset ℕ := ([1644,1686,1738,1762,2620,2714,2738,2758,3126,3178,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4689 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4689 4 (fun x => (if x<2738 then (if x<1762 then (if x<1686 then 0 else (if x<1738 then 1 else 0)) else (if x<2620 then 1 else (if x<2714 then 0 else 0))) else (if x<3178 then (if x<2758 then 1 else (if x<3126 then 1 else 2)) else (if x<3256 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4690 : Finset ℕ := ([80,130,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3126,3164,3178,3188,3214,3238,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4690 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4690 80 4
  · have he : independentCachedBranchMembers4690.erase 80=independentCachedBranchMembers4688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4688
  · have he : independentCachedBranchMembers4690.filter (independentCachedEdge 80)=independentCachedBranchMembers4689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4689
def independentCachedBranchMembers4691 : Finset ℕ := ([1650,1686,1748,1762,2646,2738,2758,2800,3164,3178,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4691 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4691 4 (fun x => (if x<2758 then (if x<1762 then (if x<1686 then 0 else (if x<1748 then 0 else 1)) else (if x<2646 then 1 else (if x<2738 then 0 else 0))) else (if x<3178 then (if x<2800 then 1 else (if x<3164 then 1 else 2)) else (if x<3214 then 2 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4692 : Finset ℕ := ([36,80,130,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3126,3164,3178,3188,3214,3238,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4692 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4692 36 4
  · have he : independentCachedBranchMembers4692.erase 36=independentCachedBranchMembers4690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4690
  · have he : independentCachedBranchMembers4692.filter (independentCachedEdge 36)=independentCachedBranchMembers4691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4691
def independentCachedBranchMembers4693 : Finset ℕ := ([36,80,130,246,1582,1626,1686,1762,2620,2646,2714,2800,3126,3164,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4693 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4693 4 (fun x => (if x<2620 then (if x<1582 then (if x<130 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3126 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4694 : Finset ℕ := ([36,80,130,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4694 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4694 3276 4
  · have he : independentCachedBranchMembers4694.erase 3276=independentCachedBranchMembers4692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4692
  · have he : independentCachedBranchMembers4694.filter (independentCachedEdge 3276)=independentCachedBranchMembers4693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4693
def independentCachedBranchMembers4695 : Finset ℕ := ([36,80,130,246,1644,1650,1738,1748,2732,2738,2758,2776,3126,3164,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4695 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4695 4 (fun x => (if x<2732 then (if x<1644 then (if x<130 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1738 then (if x<1650 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3126 then (if x<2758 then (if x<2738 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4696 : Finset ℕ := ([36,80,130,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4696 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4696 3102 4
  · have he : independentCachedBranchMembers4696.erase 3102=independentCachedBranchMembers4694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4694
  · have he : independentCachedBranchMembers4696.filter (independentCachedEdge 3102)=independentCachedBranchMembers4695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4695
def independentCachedBranchMembers4697 : Finset ℕ := ([1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4697 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4697 4 (fun x => (if x<2620 then (if x<1686 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1762 then 1 else 0))) else (if x<2738 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2776 then (if x<2758 then 3 else 3) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4698 : Finset ℕ := ([36,80,130,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4698 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4698 3072 4
  · have he : independentCachedBranchMembers4698.erase 3072=independentCachedBranchMembers4696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4696
  · have he : independentCachedBranchMembers4698.filter (independentCachedEdge 3072)=independentCachedBranchMembers4697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4697
def independentCachedBranchMembers4699 : Finset ℕ := ([36,246,1582,1644,1650,1762,2620,2732,2738,2800,3126,3178,3188,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4699 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4699 4 (fun x => (if x<2738 then (if x<1650 then (if x<1582 then (if x<246 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2732 then 2 else 1))) else (if x<3188 then (if x<3126 then (if x<2800 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4700 : Finset ℕ := ([36,80,130,222,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4700 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4700 222 4
  · have he : independentCachedBranchMembers4700.erase 222=independentCachedBranchMembers4698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4698
  · have he : independentCachedBranchMembers4700.filter (independentCachedEdge 222)=independentCachedBranchMembers4699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4699
def independentCachedBranchMembers4701 : Finset ℕ := ([80,130,1626,1644,1650,1686,2646,2714,2732,2738,3164,3178,3188,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4701 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4701 4 (fun x => (if x<2732 then (if x<1650 then (if x<1626 then (if x<130 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<2646 then (if x<1686 then 2 else 2) else (if x<2714 then 2 else 1))) else (if x<3188 then (if x<3164 then (if x<2738 then 1 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3214 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4702 : Finset ℕ := ([36,80,130,192,222,246,1582,1626,1644,1650,1686,1738,1748,1762,2620,2646,2714,2732,2738,2758,2776,2800,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4702 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4702 192 4
  · have he : independentCachedBranchMembers4702.erase 192=independentCachedBranchMembers4700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4700
  · have he : independentCachedBranchMembers4702.filter (independentCachedEdge 192)=independentCachedBranchMembers4701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4701
def independentCachedBranchMembers4703 : Finset ℕ := ([80,130,1582,1738,1748,1762,2620,2758,2776,2800,3164,3178,3188,3214,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4703 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4703 4 (fun x => (if x<2776 then (if x<1748 then (if x<1582 then (if x<130 then 0 else 0) else (if x<1738 then 1 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2758 then 1 else 2))) else (if x<3188 then (if x<3164 then (if x<2800 then 1 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3214 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
