/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch55
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4576 : Finset ℕ := ([36,72,80,130,132,238,246,1644,1650,1702,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4576 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4576 72 4
  · have he : independentCachedBranchMembers4576.erase 72=independentCachedBranchMembers4574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4574
  · have he : independentCachedBranchMembers4576.filter (independentCachedEdge 72)=independentCachedBranchMembers4575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4575
def independentCachedBranchMembers4577 : Finset ℕ := ([36,130,1644,1738,2680,2732,2740,2758,3162,3214,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4577 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4577 4 (fun x => (if x<2740 then (if x<1738 then (if x<130 then 0 else (if x<1644 then 0 else 0)) else (if x<2680 then 0 else (if x<2732 then 1 else 1))) else (if x<3214 then (if x<2758 then 2 else (if x<3162 then 2 else 1)) else (if x<3222 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4578 : Finset ℕ := ([34,36,72,80,130,132,238,246,1644,1650,1702,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4578 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4578 34 4
  · have he : independentCachedBranchMembers4578.erase 34=independentCachedBranchMembers4576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4576
  · have he : independentCachedBranchMembers4578.filter (independentCachedEdge 34)=independentCachedBranchMembers4577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4577
def independentCachedBranchMembers4579 : Finset ℕ := ([34,36,72,80,130,132,238,246,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4579 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4579 4 (fun x => (if x<3118 then (if x<130 then (if x<72 then (if x<36 then 0 else 1) else (if x<80 then 0 else 1)) else (if x<238 then (if x<132 then 1 else 0) else (if x<246 then 0 else 1))) else (if x<3214 then (if x<3162 then (if x<3126 then 2 else 3) else (if x<3164 then 2 else 3)) else (if x<3298 then (if x<3222 then 3 else 2) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4580 : Finset ℕ := ([34,36,72,80,130,132,238,246,1644,1650,1702,1720,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4580 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4580 1720 4
  · have he : independentCachedBranchMembers4580.erase 1720=independentCachedBranchMembers4578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4578
  · have he : independentCachedBranchMembers4580.filter (independentCachedEdge 1720)=independentCachedBranchMembers4579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4579
def independentCachedBranchMembers4581 : Finset ℕ := ([34,36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4581 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4581 3102 5
  · have he : independentCachedBranchMembers4581.erase 3102=independentCachedBranchMembers4565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4565
  · have he : independentCachedBranchMembers4581.filter (independentCachedEdge 3102)=independentCachedBranchMembers4580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4580
def independentCachedBranchMembers4582 : Finset ℕ := ([1644,1650,1678,1720,1738,1748,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4582 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4582 5 (fun x => (if x<2662 then (if x<1748 then (if x<1678 then (if x<1650 then 0 else 0) else (if x<1720 then 1 else (if x<1738 then 0 else 0))) else (if x<2620 then (if x<1764 then 0 else (if x<2618 then 1 else 2)) else (if x<2638 then 3 else (if x<2646 then 2 else 3)))) else (if x<2738 then (if x<2716 then (if x<2680 then 4 else (if x<2714 then 4 else 1)) else (if x<2730 then 2 else (if x<2732 then 4 else 1))) else (if x<2776 then (if x<2740 then 3 else (if x<2758 then 4 else 1)) else (if x<2792 then 3 else (if x<2800 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4583 : Finset ℕ := ([1644,1748,2618,2662,2714,2732,2740,2758,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4583 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4583 4 (fun x => (if x<2732 then (if x<2618 then (if x<1748 then 0 else 0) else (if x<2662 then 1 else (if x<2714 then 1 else 2))) else (if x<2758 then (if x<2740 then 1 else 2) else (if x<2792 then 2 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4584 : Finset ℕ := ([1628,1644,1650,1678,1720,1738,1748,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4584 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4584 1628 4
  · have he : independentCachedBranchMembers4584.erase 1628=independentCachedBranchMembers4582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4582
  · have he : independentCachedBranchMembers4584.filter (independentCachedEdge 1628)=independentCachedBranchMembers4583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4583
def independentCachedBranchMembers4585 : Finset ℕ := ([1650,1738,2638,2680,2714,2716,2730,2732,2758,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4585 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4585 4 (fun x => (if x<2716 then (if x<2638 then (if x<1738 then 0 else 0) else (if x<2680 then 1 else (if x<2714 then 1 else 1))) else (if x<2732 then (if x<2730 then 2 else 2) else (if x<2758 then 1 else (if x<2800 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4586 : Finset ℕ := ([1590,1628,1644,1650,1678,1720,1738,1748,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4586 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4586 1590 4
  · have he : independentCachedBranchMembers4586.erase 1590=independentCachedBranchMembers4584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4584
  · have he : independentCachedBranchMembers4586.filter (independentCachedEdge 1590)=independentCachedBranchMembers4585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4585
def independentCachedBranchMembers4587 : Finset ℕ := ([1628,1650,1738,1764,2618,2638,2646,2680,2714,2732,2740,2776] : List ℕ).toFinset
theorem independentCachedBranchBound4587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4587 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4587 4 (fun x => (if x<2646 then (if x<1764 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<2732 then (if x<2680 then 2 else (if x<2714 then 2 else 2)) else (if x<2740 then 1 else (if x<2776 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4588 : Finset ℕ := ([1590,1628,1644,1650,1678,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4588 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4588 1762 4
  · have he : independentCachedBranchMembers4588.erase 1762=independentCachedBranchMembers4586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4586
  · have he : independentCachedBranchMembers4588.filter (independentCachedEdge 1762)=independentCachedBranchMembers4587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4587
def independentCachedBranchMembers4589 : Finset ℕ := ([1590,1644,1678,1748,2618,2620,2638,2662,2730,2732,2776,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4589 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4589 4 (fun x => (if x<2638 then (if x<1748 then (if x<1644 then 0 else (if x<1678 then 0 else 0)) else (if x<2618 then 0 else (if x<2620 then 1 else 2))) else (if x<2732 then (if x<2662 then 1 else (if x<2730 then 2 else 2)) else (if x<2776 then 1 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4590 : Finset ℕ := ([1590,1628,1644,1650,1678,1686,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4590 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4590 1686 4
  · have he : independentCachedBranchMembers4590.erase 1686=independentCachedBranchMembers4588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4588
  · have he : independentCachedBranchMembers4590.filter (independentCachedEdge 1686)=independentCachedBranchMembers4589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4589
def independentCachedBranchMembers4591 : Finset ℕ := ([1628,1650,1738,1764,2620,2662,2716,2730,2738,2758,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4591 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4591 4 (fun x => (if x<2716 then (if x<1764 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<2620 then 0 else (if x<2662 then 1 else 1))) else (if x<2758 then (if x<2730 then 2 else (if x<2738 then 1 else 2)) else (if x<2792 then 2 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4592 : Finset ℕ := ([1590,1626,1628,1644,1650,1678,1686,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4592 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4592 1626 4
  · have he : independentCachedBranchMembers4592.erase 1626=independentCachedBranchMembers4590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4590
  · have he : independentCachedBranchMembers4592.filter (independentCachedEdge 1626)=independentCachedBranchMembers4591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4591
def independentCachedBranchMembers4593 : Finset ℕ := ([1590,1644,1678,1748,2646,2680,2714,2716,2738,2740,2758,2792] : List ℕ).toFinset
theorem independentCachedBranchBound4593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4593 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4593 4 (fun x => (if x<2714 then (if x<1748 then (if x<1644 then 0 else (if x<1678 then 0 else 0)) else (if x<2646 then 0 else (if x<2680 then 1 else 1))) else (if x<2740 then (if x<2716 then 1 else (if x<2738 then 2 else 2)) else (if x<2758 then 1 else (if x<2792 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4594 : Finset ℕ := ([1582,1590,1626,1628,1644,1650,1678,1686,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4594 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4594 1582 4
  · have he : independentCachedBranchMembers4594.erase 1582=independentCachedBranchMembers4592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4592
  · have he : independentCachedBranchMembers4594.filter (independentCachedEdge 1582)=independentCachedBranchMembers4593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4593
def independentCachedBranchMembers4595 : Finset ℕ := ([1582,1590,1626,1628,1678,1686,1762,1764,2618,2620,2638,2646,2714,2716,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4595 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4595 4 (fun x => (if x<2618 then (if x<1678 then (if x<1626 then (if x<1590 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1762 then (if x<1686 then 1 else 0) else (if x<1764 then 0 else 1))) else (if x<2714 then (if x<2638 then (if x<2620 then 2 else 3) else (if x<2646 then 2 else 3)) else (if x<2792 then (if x<2716 then 3 else 2) else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4596 : Finset ℕ := ([1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4596 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4596 1702 4
  · have he : independentCachedBranchMembers4596.erase 1702=independentCachedBranchMembers4594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4594
  · have he : independentCachedBranchMembers4596.filter (independentCachedEdge 1702)=independentCachedBranchMembers4595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4595
def independentCachedBranchMembers4597 : Finset ℕ := ([34,36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3072,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4597 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4597 3072 5
  · have he : independentCachedBranchMembers4597.erase 3072=independentCachedBranchMembers4581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4581
  · have he : independentCachedBranchMembers4597.filter (independentCachedEdge 3072)=independentCachedBranchMembers4596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4596
def independentCachedBranchMembers4598 : Finset ℕ := ([238,1582,1626,1644,1650,1686,1738,1748,1762,2618,2638,2662,2680,2716,2730,2740,2792,3126,3164,3178,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4598 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4598 5 (fun x => (if x<2716 then (if x<1738 then (if x<1644 then (if x<1582 then 0 else (if x<1626 then 0 else 1)) else (if x<1650 then 1 else (if x<1686 then 2 else 2))) else (if x<2618 then (if x<1748 then 0 else (if x<1762 then 1 else 1)) else (if x<2662 then (if x<2638 then 3 else 0) else (if x<2680 then 3 else 2)))) else (if x<3178 then (if x<2792 then (if x<2730 then 2 else (if x<2740 then 0 else 3)) else (if x<3126 then 3 else (if x<3164 then 3 else 1))) else (if x<3256 then (if x<3214 then 0 else (if x<3238 then 0 else 4)) else (if x<3282 then (if x<3276 then 3 else 4) else (if x<3300 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4599 : Finset ℕ := ([1582,1644,1738,1762,2638,2662,2730,2792,3126,3164,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4599 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4599 4 (fun x => (if x<2730 then (if x<1762 then (if x<1644 then 0 else (if x<1738 then 1 else 0)) else (if x<2638 then 1 else (if x<2662 then 0 else 1))) else (if x<3164 then (if x<2792 then 0 else (if x<3126 then 1 else 2)) else (if x<3256 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4600 : Finset ℕ := ([132,238,1582,1626,1644,1650,1686,1738,1748,1762,2618,2638,2662,2680,2716,2730,2740,2792,3126,3164,3178,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4600 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4600 132 4
  · have he : independentCachedBranchMembers4600.erase 132=independentCachedBranchMembers4598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4598
  · have he : independentCachedBranchMembers4600.filter (independentCachedEdge 132)=independentCachedBranchMembers4599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4599
def independentCachedBranchMembers4601 : Finset ℕ := ([1582,1650,1748,1762,2618,2662,2716,2730,3214,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4601 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4601 4 (fun x => (if x<2716 then (if x<1762 then (if x<1650 then 0 else (if x<1748 then 0 else 1)) else (if x<2618 then 1 else (if x<2662 then 0 else 0))) else (if x<3256 then (if x<2730 then 1 else (if x<3214 then 1 else 2)) else (if x<3282 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4602 : Finset ℕ := ([72,132,238,1582,1626,1644,1650,1686,1738,1748,1762,2618,2638,2662,2680,2716,2730,2740,2792,3126,3164,3178,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4602 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4602 72 4
  · have he : independentCachedBranchMembers4602.erase 72=independentCachedBranchMembers4600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4600
  · have he : independentCachedBranchMembers4602.filter (independentCachedEdge 72)=independentCachedBranchMembers4601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4601
def independentCachedBranchMembers4603 : Finset ℕ := ([1626,1644,1686,1738,2638,2680,2740,2792,3214,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4603 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4603 4 (fun x => (if x<2740 then (if x<1738 then (if x<1644 then 0 else (if x<1686 then 0 else 1)) else (if x<2638 then 1 else (if x<2680 then 0 else 0))) else (if x<3256 then (if x<2792 then 1 else (if x<3214 then 1 else 2)) else (if x<3282 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4604 : Finset ℕ := ([34,72,132,238,1582,1626,1644,1650,1686,1738,1748,1762,2618,2638,2662,2680,2716,2730,2740,2792,3126,3164,3178,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4604 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4604 34 4
  · have he : independentCachedBranchMembers4604.erase 34=independentCachedBranchMembers4602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4602
  · have he : independentCachedBranchMembers4604.filter (independentCachedEdge 34)=independentCachedBranchMembers4603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4603
def independentCachedBranchMembers4605 : Finset ℕ := ([34,72,132,238,1582,1626,1686,1762,2618,2638,2716,2792,3126,3164,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4605 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4605 4 (fun x => (if x<2618 then (if x<1582 then (if x<132 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3126 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4606 : Finset ℕ := ([34,72,132,238,1582,1626,1644,1650,1686,1738,1748,1762,2618,2638,2662,2680,2716,2730,2740,2792,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4606 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4606 3188 4
  · have he : independentCachedBranchMembers4606.erase 3188=independentCachedBranchMembers4604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4604
  · have he : independentCachedBranchMembers4606.filter (independentCachedEdge 3188)=independentCachedBranchMembers4605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4605
def independentCachedBranchMembers4607 : Finset ℕ := ([34,72,132,238,1644,1650,1738,1748,2662,2680,2730,2740,3126,3164,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4607 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4607 4 (fun x => (if x<2662 then (if x<1644 then (if x<132 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1738 then (if x<1650 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3126 then (if x<2730 then (if x<2680 then 2 else 2) else (if x<2740 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
