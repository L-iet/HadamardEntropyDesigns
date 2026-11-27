/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch57
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4640 : Finset ℕ := ([72,80,130,132,1626,1628,1644,1650,1678,1686,1702,1720,2638,2646,2680,2714,2716,2730,2732,2738,2740,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4640 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4640 3180 4
  · have he : independentCachedBranchMembers4640.erase 3180=independentCachedBranchMembers4638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4638
  · have he : independentCachedBranchMembers4640.filter (independentCachedEdge 3180)=independentCachedBranchMembers4639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4639
def independentCachedBranchMembers4641 : Finset ℕ := ([72,80,130,132,1626,1628,1678,1686,2638,2646,2714,2716,3162,3164,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound4641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4641 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4641 4 (fun x => (if x<2638 then (if x<1626 then (if x<130 then (if x<80 then 0 else 1) else (if x<132 then 0 else 1)) else (if x<1678 then (if x<1628 then 1 else 0) else (if x<1686 then 1 else 0))) else (if x<3162 then (if x<2714 then (if x<2646 then 2 else 3) else (if x<2716 then 2 else 3)) else (if x<3214 then (if x<3164 then 2 else 3) else (if x<3222 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4642 : Finset ℕ := ([72,80,130,132,1626,1628,1644,1650,1678,1686,1702,1720,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4642 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4642 2662 4
  · have he : independentCachedBranchMembers4642.erase 2662=independentCachedBranchMembers4640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4640
  · have he : independentCachedBranchMembers4642.filter (independentCachedEdge 2662)=independentCachedBranchMembers4641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4641
def independentCachedBranchMembers4643 : Finset ℕ := ([34,36,72,80,130,132,192,222,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1740,1746,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3072,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4643 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4643 192 5
  · have he : independentCachedBranchMembers4643.erase 192=independentCachedBranchMembers4633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4633
  · have he : independentCachedBranchMembers4643.filter (independentCachedEdge 192)=independentCachedBranchMembers4642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4642
def independentCachedBranchMembers4644 : Finset ℕ := ([130,238,1582,1628,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2716,2730,2758,2776,2800,3118,3164,3178,3188,3214,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4644 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4644 5 (fun x => (if x<2680 then (if x<1720 then (if x<1628 then (if x<238 then 0 else (if x<1582 then 0 else 1)) else (if x<1678 then 1 else (if x<1702 then 0 else 2))) else (if x<1762 then (if x<1738 then 1 else (if x<1748 then 1 else 2)) else (if x<2638 then (if x<2620 then 0 else 1) else (if x<2662 then 1 else 3)))) else (if x<3164 then (if x<2758 then (if x<2716 then 3 else (if x<2730 then 4 else 0)) else (if x<2800 then (if x<2776 then 0 else 1) else (if x<3118 then 4 else 2))) else (if x<3214 then (if x<3178 then 2 else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 4 else 0) else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4645 : Finset ℕ := ([238,1720,1738,1762,2620,2638,2662,2716,2758,3178,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4645 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4645 4 (fun x => (if x<2662 then (if x<1762 then (if x<1720 then 0 else (if x<1738 then 1 else 0)) else (if x<2620 then 1 else (if x<2638 then 1 else 0))) else (if x<3178 then (if x<2716 then 1 else (if x<2758 then 2 else 2)) else (if x<3256 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4646 : Finset ℕ := ([80,130,238,1582,1628,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2716,2730,2758,2776,2800,3118,3164,3178,3188,3214,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4646 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4646 80 4
  · have he : independentCachedBranchMembers4646.erase 80=independentCachedBranchMembers4644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4644
  · have he : independentCachedBranchMembers4646.filter (independentCachedEdge 80)=independentCachedBranchMembers4645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4645
def independentCachedBranchMembers4647 : Finset ℕ := ([130,1678,1720,1738,2620,2638,2680,2758,2800,3188,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4647 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4647 4 (fun x => (if x<2680 then (if x<1738 then (if x<1678 then 0 else (if x<1720 then 0 else 1)) else (if x<2620 then 1 else (if x<2638 then 1 else 1))) else (if x<3188 then (if x<2758 then 0 else (if x<2800 then 2 else 2)) else (if x<3214 then 0 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4648 : Finset ℕ := ([34,80,130,238,1582,1628,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2716,2730,2758,2776,2800,3118,3164,3178,3188,3214,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4648 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4648 34 4
  · have he : independentCachedBranchMembers4648.erase 34=independentCachedBranchMembers4646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4646
  · have he : independentCachedBranchMembers4648.filter (independentCachedEdge 34)=independentCachedBranchMembers4647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4647
def independentCachedBranchMembers4649 : Finset ℕ := ([130,238,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,3118,3164,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound4649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4649 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4649 4 (fun x => (if x<2620 then (if x<1720 then (if x<1678 then (if x<238 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3118 then (if x<2662 then (if x<2638 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3178 then (if x<3164 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4650 : Finset ℕ := ([34,80,130,238,1582,1628,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2716,2730,2758,2776,2800,3118,3164,3178,3188,3214,3238,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4650 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4650 3284 4
  · have he : independentCachedBranchMembers4650.erase 3284=independentCachedBranchMembers4648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4648
  · have he : independentCachedBranchMembers4650.filter (independentCachedEdge 3284)=independentCachedBranchMembers4649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4649
def independentCachedBranchMembers4651 : Finset ℕ := ([34,80,1582,1628,1702,1720,1738,1748,2662,2680,2716,2800,3178,3188,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4651 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4651 4 (fun x => (if x<2662 then (if x<1702 then (if x<1582 then (if x<80 then 0 else 0) else (if x<1628 then 0 else 0)) else (if x<1738 then (if x<1720 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2716 then (if x<2680 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3188 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4652 : Finset ℕ := ([34,80,130,238,1582,1628,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2716,2730,2758,2776,2800,3118,3164,3178,3188,3214,3238,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4652 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4652 3274 4
  · have he : independentCachedBranchMembers4652.erase 3274=independentCachedBranchMembers4650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4650
  · have he : independentCachedBranchMembers4652.filter (independentCachedEdge 3274)=independentCachedBranchMembers4651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4651
def independentCachedBranchMembers4653 : Finset ℕ := ([34,80,130,238,1582,1628,1678,1762,2620,2638,2716,2800,3118,3164,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4653 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4653 4 (fun x => (if x<2620 then (if x<1582 then (if x<130 then (if x<80 then 0 else 0) else (if x<238 then 1 else 1)) else (if x<1678 then (if x<1628 then 0 else 0) else (if x<1762 then 1 else 1))) else (if x<3118 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3164 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4654 : Finset ℕ := ([34,80,130,238,1582,1628,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2716,2730,2740,2758,2776,2800,3118,3164,3178,3188,3214,3238,3256,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4654 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4654 2740 4
  · have he : independentCachedBranchMembers4654.erase 2740=independentCachedBranchMembers4652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4652
  · have he : independentCachedBranchMembers4654.filter (independentCachedEdge 2740)=independentCachedBranchMembers4653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4653
def independentCachedBranchMembers4655 : Finset ℕ := ([18,34,36,72,80,130,132,192,222,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1740,1746,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3072,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4655 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4655 18 5
  · have he : independentCachedBranchMembers4655.erase 18=independentCachedBranchMembers4643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4643
  · have he : independentCachedBranchMembers4655.filter (independentCachedEdge 18)=independentCachedBranchMembers4654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4654
def independentCachedBranchMembers4656 : Finset ℕ := ([132,246,1590,1626,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2714,2740,2758,2776,2792,3126,3162,3178,3188,3222,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4656 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4656 5 (fun x => (if x<2680 then (if x<1720 then (if x<1626 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1686 then 1 else (if x<1702 then 0 else 2))) else (if x<1764 then (if x<1738 then 1 else (if x<1748 then 2 else 1)) else (if x<2646 then (if x<2618 then 0 else 1) else (if x<2662 then 1 else 3)))) else (if x<3162 then (if x<2758 then (if x<2714 then 3 else (if x<2740 then 4 else 0)) else (if x<2792 then (if x<2776 then 0 else 1) else (if x<3126 then 4 else 2))) else (if x<3222 then (if x<3178 then 2 else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 4 else 0) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4657 : Finset ℕ := ([246,1720,1748,1764,2618,2646,2662,2714,2758,3188,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4657 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4657 4 (fun x => (if x<2662 then (if x<1764 then (if x<1720 then 0 else (if x<1748 then 1 else 0)) else (if x<2618 then 1 else (if x<2646 then 1 else 0))) else (if x<3188 then (if x<2714 then 1 else (if x<2758 then 2 else 2)) else (if x<3256 then 0 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4658 : Finset ℕ := ([72,132,246,1590,1626,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2714,2740,2758,2776,2792,3126,3162,3178,3188,3222,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4658 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4658 72 4
  · have he : independentCachedBranchMembers4658.erase 72=independentCachedBranchMembers4656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4656
  · have he : independentCachedBranchMembers4658.filter (independentCachedEdge 72)=independentCachedBranchMembers4657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4657
def independentCachedBranchMembers4659 : Finset ℕ := ([132,1686,1720,1748,2618,2646,2680,2758,2792,3178,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4659 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4659 4 (fun x => (if x<2680 then (if x<1748 then (if x<1686 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2646 then 1 else 1))) else (if x<3178 then (if x<2758 then 0 else (if x<2792 then 2 else 2)) else (if x<3222 then 0 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4660 : Finset ℕ := ([36,72,132,246,1590,1626,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2714,2740,2758,2776,2792,3126,3162,3178,3188,3222,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4660 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4660 36 4
  · have he : independentCachedBranchMembers4660.erase 36=independentCachedBranchMembers4658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4658
  · have he : independentCachedBranchMembers4660.filter (independentCachedEdge 36)=independentCachedBranchMembers4659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4659
def independentCachedBranchMembers4661 : Finset ℕ := ([36,72,1590,1626,1702,1720,1738,1748,2662,2680,2714,2792,3178,3188,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4661 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4661 4 (fun x => (if x<2662 then (if x<1702 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1626 then 0 else 0)) else (if x<1738 then (if x<1720 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2714 then (if x<2680 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3188 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4662 : Finset ℕ := ([36,72,132,246,1590,1626,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2714,2740,2758,2776,2792,3126,3162,3178,3188,3222,3238,3256,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4662 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4662 3284 4
  · have he : independentCachedBranchMembers4662.erase 3284=independentCachedBranchMembers4660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4660
  · have he : independentCachedBranchMembers4662.filter (independentCachedEdge 3284)=independentCachedBranchMembers4661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4661
def independentCachedBranchMembers4663 : Finset ℕ := ([132,246,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,3126,3162,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound4663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4663 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4663 4 (fun x => (if x<2618 then (if x<1720 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3126 then (if x<2662 then (if x<2646 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3178 then (if x<3162 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4664 : Finset ℕ := ([36,72,132,246,1590,1626,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2714,2740,2758,2776,2792,3126,3162,3178,3188,3222,3238,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4664 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4664 3274 4
  · have he : independentCachedBranchMembers4664.erase 3274=independentCachedBranchMembers4662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4662
  · have he : independentCachedBranchMembers4664.filter (independentCachedEdge 3274)=independentCachedBranchMembers4663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4663
def independentCachedBranchMembers4665 : Finset ℕ := ([36,72,132,246,1590,1626,1686,1764,2618,2646,2714,2792,3126,3162,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4665 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4665 4 (fun x => (if x<2618 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1686 then (if x<1626 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3126 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3162 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4666 : Finset ℕ := ([36,72,132,246,1590,1626,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2714,2730,2740,2758,2776,2792,3126,3162,3178,3188,3222,3238,3256,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4666 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4666 2730 4
  · have he : independentCachedBranchMembers4666.erase 2730=independentCachedBranchMembers4664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4664
  · have he : independentCachedBranchMembers4666.filter (independentCachedEdge 2730)=independentCachedBranchMembers4665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4665
def independentCachedBranchMembers4667 : Finset ℕ := ([12,18,34,36,72,80,130,132,192,222,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1740,1746,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3072,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4667 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4667 12 5
  · have he : independentCachedBranchMembers4667.erase 12=independentCachedBranchMembers4655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4655
  · have he : independentCachedBranchMembers4667.filter (independentCachedEdge 12)=independentCachedBranchMembers4666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4666
def independentCachedBranchMembers4668 : Finset ℕ := ([132,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3118,3162,3178,3188,3222,3238,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4668 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4668 5 (fun x => (if x<2732 then (if x<1678 then (if x<1628 then (if x<238 then 0 else (if x<1590 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1764 then (if x<1738 then 0 else (if x<1748 then 2 else 2)) else (if x<2638 then (if x<2618 then 0 else 3) else (if x<2716 then 3 else 3)))) else (if x<3178 then (if x<2776 then (if x<2738 then 0 else (if x<2758 then 1 else 0)) else (if x<3118 then (if x<2792 then 1 else 3) else (if x<3162 then 4 else 4))) else (if x<3238 then (if x<3188 then 2 else (if x<3222 then 2 else 4)) else (if x<3276 then (if x<3256 then 0 else 3) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4669 : Finset ℕ := ([1650,1678,1748,1764,2618,2716,2732,2758,3118,3188,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4669 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4669 4 (fun x => (if x<2732 then (if x<1764 then (if x<1678 then 0 else (if x<1748 then 1 else 0)) else (if x<2618 then 1 else (if x<2716 then 0 else 0))) else (if x<3188 then (if x<2758 then 1 else (if x<3118 then 1 else 2)) else (if x<3256 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4670 : Finset ℕ := ([72,132,238,1590,1628,1644,1650,1678,1738,1748,1764,2618,2638,2716,2732,2738,2758,2776,2792,3118,3162,3178,3188,3222,3238,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4670 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4670 72 4
  · have he : independentCachedBranchMembers4670.erase 72=independentCachedBranchMembers4668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4668
  · have he : independentCachedBranchMembers4670.filter (independentCachedEdge 72)=independentCachedBranchMembers4669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4669
def independentCachedBranchMembers4671 : Finset ℕ := ([1644,1678,1738,1764,2638,2732,2758,2792,3162,3188,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4671 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4671 4 (fun x => (if x<2758 then (if x<1764 then (if x<1678 then 0 else (if x<1738 then 0 else 1)) else (if x<2638 then 1 else (if x<2732 then 0 else 0))) else (if x<3188 then (if x<2792 then 1 else (if x<3162 then 1 else 2)) else (if x<3222 then 2 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
