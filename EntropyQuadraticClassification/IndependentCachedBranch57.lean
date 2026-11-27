/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch56
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4608 : Finset ℕ := ([34,72,132,238,1582,1626,1644,1650,1686,1738,1748,1762,2618,2638,2662,2680,2716,2730,2740,2792,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4608 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4608 3102 4
  · have he : independentCachedBranchMembers4608.erase 3102=independentCachedBranchMembers4606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4606
  · have he : independentCachedBranchMembers4608.filter (independentCachedEdge 3102)=independentCachedBranchMembers4607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4607
def independentCachedBranchMembers4609 : Finset ℕ := ([1582,1626,1644,1650,1686,1738,1748,1762,2618,2638,2662,2680,2716,2730,2740,2792] : List ℕ).toFinset
theorem independentCachedBranchBound4609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4609 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4609 4 (fun x => (if x<2618 then (if x<1686 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1762 then 1 else 0))) else (if x<2716 then (if x<2662 then (if x<2638 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<2740 then (if x<2730 then 2 else 3) else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4610 : Finset ℕ := ([34,72,132,238,1582,1626,1644,1650,1686,1738,1748,1762,2618,2638,2662,2680,2716,2730,2740,2792,3072,3102,3126,3164,3178,3188,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4610 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4610 3072 4
  · have he : independentCachedBranchMembers4610.erase 3072=independentCachedBranchMembers4608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4608
  · have he : independentCachedBranchMembers4610.filter (independentCachedEdge 3072)=independentCachedBranchMembers4609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4609
def independentCachedBranchMembers4611 : Finset ℕ := ([34,36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1746,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3072,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4611 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4611 1746 5
  · have he : independentCachedBranchMembers4611.erase 1746=independentCachedBranchMembers4597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4597
  · have he : independentCachedBranchMembers4611.filter (independentCachedEdge 1746)=independentCachedBranchMembers4610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4610
def independentCachedBranchMembers4612 : Finset ℕ := ([246,1590,1628,1644,1650,1678,1738,1748,1764,2620,2646,2662,2680,2714,2730,2740,2800,3118,3162,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4612 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4612 5 (fun x => (if x<2714 then (if x<1738 then (if x<1644 then (if x<1590 then 0 else (if x<1628 then 0 else 1)) else (if x<1650 then 2 else (if x<1678 then 1 else 2))) else (if x<2620 then (if x<1748 then 1 else (if x<1764 then 0 else 1)) else (if x<2662 then (if x<2646 then 3 else 0) else (if x<2680 then 3 else 2)))) else (if x<3188 then (if x<2800 then (if x<2730 then 2 else (if x<2740 then 3 else 0)) else (if x<3118 then 3 else (if x<3162 then 3 else 1))) else (if x<3256 then (if x<3222 then 0 else (if x<3238 then 0 else 4)) else (if x<3282 then (if x<3276 then 3 else 1) else (if x<3298 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4613 : Finset ℕ := ([1590,1650,1748,1764,2646,2662,2740,2800,3118,3162,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4613 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4613 4 (fun x => (if x<2740 then (if x<1764 then (if x<1650 then 0 else (if x<1748 then 1 else 0)) else (if x<2646 then 1 else (if x<2662 then 0 else 1))) else (if x<3162 then (if x<2800 then 0 else (if x<3118 then 1 else 2)) else (if x<3256 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4614 : Finset ℕ := ([130,246,1590,1628,1644,1650,1678,1738,1748,1764,2620,2646,2662,2680,2714,2730,2740,2800,3118,3162,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4614 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4614 130 4
  · have he : independentCachedBranchMembers4614.erase 130=independentCachedBranchMembers4612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4612
  · have he : independentCachedBranchMembers4614.filter (independentCachedEdge 130)=independentCachedBranchMembers4613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4613
def independentCachedBranchMembers4615 : Finset ℕ := ([1590,1644,1738,1764,2620,2662,2714,2740,3222,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4615 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4615 4 (fun x => (if x<2714 then (if x<1764 then (if x<1644 then 0 else (if x<1738 then 0 else 1)) else (if x<2620 then 1 else (if x<2662 then 0 else 0))) else (if x<3256 then (if x<2740 then 1 else (if x<3222 then 1 else 2)) else (if x<3276 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4616 : Finset ℕ := ([80,130,246,1590,1628,1644,1650,1678,1738,1748,1764,2620,2646,2662,2680,2714,2730,2740,2800,3118,3162,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4616 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4616 80 4
  · have he : independentCachedBranchMembers4616.erase 80=independentCachedBranchMembers4614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4614
  · have he : independentCachedBranchMembers4616.filter (independentCachedEdge 80)=independentCachedBranchMembers4615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4615
def independentCachedBranchMembers4617 : Finset ℕ := ([1628,1650,1678,1748,2646,2680,2730,2800,3222,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4617 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4617 4 (fun x => (if x<2730 then (if x<1748 then (if x<1650 then 0 else (if x<1678 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 0 else 0))) else (if x<3256 then (if x<2800 then 1 else (if x<3222 then 1 else 2)) else (if x<3276 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4618 : Finset ℕ := ([36,80,130,246,1590,1628,1644,1650,1678,1738,1748,1764,2620,2646,2662,2680,2714,2730,2740,2800,3118,3162,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4618 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4618 36 4
  · have he : independentCachedBranchMembers4618.erase 36=independentCachedBranchMembers4616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4616
  · have he : independentCachedBranchMembers4618.filter (independentCachedEdge 36)=independentCachedBranchMembers4617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4617
def independentCachedBranchMembers4619 : Finset ℕ := ([36,80,130,246,1590,1628,1678,1764,2620,2646,2714,2800,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4619 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4619 4 (fun x => (if x<2620 then (if x<1590 then (if x<130 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3118 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4620 : Finset ℕ := ([36,80,130,246,1590,1628,1644,1650,1678,1738,1748,1764,2620,2646,2662,2680,2714,2730,2740,2800,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4620 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4620 3178 4
  · have he : independentCachedBranchMembers4620.erase 3178=independentCachedBranchMembers4618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4618
  · have he : independentCachedBranchMembers4620.filter (independentCachedEdge 3178)=independentCachedBranchMembers4619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4619
def independentCachedBranchMembers4621 : Finset ℕ := ([36,80,130,246,1644,1650,1738,1748,2662,2680,2730,2740,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4621 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4621 4 (fun x => (if x<2662 then (if x<1644 then (if x<130 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1738 then (if x<1650 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3118 then (if x<2730 then (if x<2680 then 2 else 2) else (if x<2740 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4622 : Finset ℕ := ([36,80,130,246,1590,1628,1644,1650,1678,1738,1748,1764,2620,2646,2662,2680,2714,2730,2740,2800,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4622 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4622 3102 4
  · have he : independentCachedBranchMembers4622.erase 3102=independentCachedBranchMembers4620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4620
  · have he : independentCachedBranchMembers4622.filter (independentCachedEdge 3102)=independentCachedBranchMembers4621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4621
def independentCachedBranchMembers4623 : Finset ℕ := ([1590,1628,1644,1650,1678,1738,1748,1764,2620,2646,2662,2680,2714,2730,2740,2800] : List ℕ).toFinset
theorem independentCachedBranchBound4623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4623 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4623 4 (fun x => (if x<2620 then (if x<1678 then (if x<1644 then (if x<1628 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1764 then 1 else 0))) else (if x<2714 then (if x<2662 then (if x<2646 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<2740 then (if x<2730 then 2 else 3) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4624 : Finset ℕ := ([36,80,130,246,1590,1628,1644,1650,1678,1738,1748,1764,2620,2646,2662,2680,2714,2730,2740,2800,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4624 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4624 3072 4
  · have he : independentCachedBranchMembers4624.erase 3072=independentCachedBranchMembers4622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4622
  · have he : independentCachedBranchMembers4624.filter (independentCachedEdge 3072)=independentCachedBranchMembers4623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4623
def independentCachedBranchMembers4625 : Finset ℕ := ([34,36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1740,1746,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3072,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4625 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4625 1740 5
  · have he : independentCachedBranchMembers4625.erase 1740=independentCachedBranchMembers4611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4611
  · have he : independentCachedBranchMembers4625.filter (independentCachedEdge 1740)=independentCachedBranchMembers4624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4624
def independentCachedBranchMembers4626 : Finset ℕ := ([34,36,238,246,1582,1590,1644,1650,1702,1720,1762,1764,2618,2620,2662,2730,2732,2738,2740,2792,2800,3118,3126,3178,3188,3238,3256,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4626 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4626 5 (fun x => (if x<2662 then (if x<1650 then (if x<246 then (if x<36 then 0 else (if x<238 then 1 else 0)) else (if x<1590 then (if x<1582 then 1 else 0) else (if x<1644 then 1 else 2))) else (if x<1762 then (if x<1702 then 2 else (if x<1720 then 2 else 2)) else (if x<2618 then (if x<1764 then 0 else 1) else (if x<2620 then 3 else 4)))) else (if x<3118 then (if x<2738 then (if x<2730 then 0 else (if x<2732 then 0 else 2)) else (if x<2792 then (if x<2740 then 2 else 1) else (if x<2800 then 3 else 4))) else (if x<3238 then (if x<3178 then (if x<3126 then 4 else 3) else (if x<3188 then 0 else 1)) else (if x<3298 then (if x<3256 then 0 else 3) else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4627 : Finset ℕ := ([36,238,1582,1644,1650,1702,1720,1764,2620,2730,2740,2792,3126,3178,3188,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4627 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4627 4 (fun x => (if x<2620 then (if x<1650 then (if x<1582 then (if x<238 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1720 then (if x<1702 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3126 then (if x<2740 then (if x<2730 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3188 then (if x<3178 then 3 else 3) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4628 : Finset ℕ := ([34,36,238,246,1582,1590,1644,1650,1702,1720,1762,1764,2618,2620,2662,2730,2732,2738,2740,2792,2800,3118,3126,3178,3186,3188,3238,3256,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4628 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4628 3186 4
  · have he : independentCachedBranchMembers4628.erase 3186=independentCachedBranchMembers4626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4626
  · have he : independentCachedBranchMembers4628.filter (independentCachedEdge 3186)=independentCachedBranchMembers4627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4627
def independentCachedBranchMembers4629 : Finset ℕ := ([34,246,1590,1644,1650,1702,1720,1762,2618,2730,2740,2800,3118,3178,3188,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4629 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4629 4 (fun x => (if x<2618 then (if x<1650 then (if x<1590 then (if x<246 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1720 then (if x<1702 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3118 then (if x<2740 then (if x<2730 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3188 then (if x<3178 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4630 : Finset ℕ := ([34,36,238,246,1582,1590,1644,1650,1702,1720,1762,1764,2618,2620,2662,2730,2732,2738,2740,2792,2800,3118,3126,3178,3180,3186,3188,3238,3256,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4630 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4630 3180 4
  · have he : independentCachedBranchMembers4630.erase 3180=independentCachedBranchMembers4628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4628
  · have he : independentCachedBranchMembers4630.filter (independentCachedEdge 3180)=independentCachedBranchMembers4629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4629
def independentCachedBranchMembers4631 : Finset ℕ := ([34,36,238,246,1582,1590,1762,1764,2618,2620,2792,2800,3118,3126,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4631 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4631 4 (fun x => (if x<2618 then (if x<1582 then (if x<238 then (if x<36 then 0 else 1) else (if x<246 then 0 else 1)) else (if x<1762 then (if x<1590 then 0 else 1) else (if x<1764 then 0 else 1))) else (if x<3118 then (if x<2792 then (if x<2620 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3298 then (if x<3126 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4632 : Finset ℕ := ([34,36,238,246,1582,1590,1644,1650,1702,1720,1762,1764,2618,2620,2662,2680,2730,2732,2738,2740,2792,2800,3118,3126,3178,3180,3186,3188,3238,3256,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4632 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4632 2680 4
  · have he : independentCachedBranchMembers4632.erase 2680=independentCachedBranchMembers4630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4630
  · have he : independentCachedBranchMembers4632.filter (independentCachedEdge 2680)=independentCachedBranchMembers4631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4631
def independentCachedBranchMembers4633 : Finset ℕ := ([34,36,72,80,130,132,222,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1740,1746,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3072,3102,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4633 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4633 222 5
  · have he : independentCachedBranchMembers4633.erase 222=independentCachedBranchMembers4625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4625
  · have he : independentCachedBranchMembers4633.filter (independentCachedEdge 222)=independentCachedBranchMembers4632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4632
def independentCachedBranchMembers4634 : Finset ℕ := ([80,130,132,1626,1628,1644,1650,1678,1686,1702,1720,2638,2646,2680,2714,2716,2730,2732,2738,2740,3162,3164,3178,3188,3214,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4634 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4634 5 (fun x => (if x<2714 then (if x<1678 then (if x<1626 then (if x<130 then 0 else (if x<132 then 0 else 1)) else (if x<1644 then (if x<1628 then 1 else 0) else (if x<1650 then 2 else 2))) else (if x<1720 then (if x<1686 then 0 else (if x<1702 then 1 else 2)) else (if x<2646 then (if x<2638 then 2 else 3) else (if x<2680 then 4 else 0)))) else (if x<3164 then (if x<2732 then (if x<2716 then 3 else (if x<2730 then 4 else 0)) else (if x<2740 then (if x<2738 then 2 else 2) else (if x<3162 then 1 else 3))) else (if x<3214 then (if x<3178 then 4 else (if x<3188 then 1 else 0)) else (if x<3238 then (if x<3222 then 3 else 4) else (if x<3256 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4635 : Finset ℕ := ([80,1650,1678,1720,2646,2714,2716,2730,2732,3188,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4635 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4635 4 (fun x => (if x<2716 then (if x<1720 then (if x<1650 then 0 else (if x<1678 then 0 else 1)) else (if x<2646 then 1 else (if x<2714 then 0 else 1))) else (if x<3188 then (if x<2730 then 2 else (if x<2732 then 2 else 1)) else (if x<3214 then 0 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4636 : Finset ℕ := ([72,80,130,132,1626,1628,1644,1650,1678,1686,1702,1720,2638,2646,2680,2714,2716,2730,2732,2738,2740,3162,3164,3178,3188,3214,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4636 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4636 72 4
  · have he : independentCachedBranchMembers4636.erase 72=independentCachedBranchMembers4634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4634
  · have he : independentCachedBranchMembers4636.filter (independentCachedEdge 72)=independentCachedBranchMembers4635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4635
def independentCachedBranchMembers4637 : Finset ℕ := ([72,130,1628,1644,1650,1686,1702,1720,2638,2714,2730,2740,3162,3178,3188,3214] : List ℕ).toFinset
theorem independentCachedBranchBound4637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4637 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4637 4 (fun x => (if x<2638 then (if x<1650 then (if x<1628 then (if x<130 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1702 then (if x<1686 then 1 else 0) else (if x<1720 then 1 else 1))) else (if x<3162 then (if x<2730 then (if x<2714 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3188 then (if x<3178 then 2 else 3) else (if x<3214 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4638 : Finset ℕ := ([72,80,130,132,1626,1628,1644,1650,1678,1686,1702,1720,2638,2646,2680,2714,2716,2730,2732,2738,2740,3162,3164,3178,3186,3188,3214,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4638 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4638 3186 4
  · have he : independentCachedBranchMembers4638.erase 3186=independentCachedBranchMembers4636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4636
  · have he : independentCachedBranchMembers4638.filter (independentCachedEdge 3186)=independentCachedBranchMembers4637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4637
def independentCachedBranchMembers4639 : Finset ℕ := ([80,132,1626,1644,1650,1678,1702,1720,2646,2716,2730,2740,3164,3178,3188,3222] : List ℕ).toFinset
theorem independentCachedBranchBound4639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4639 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4639 4 (fun x => (if x<2646 then (if x<1650 then (if x<1626 then (if x<132 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1702 then (if x<1678 then 1 else 0) else (if x<1720 then 1 else 1))) else (if x<3164 then (if x<2730 then (if x<2716 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3188 then (if x<3178 then 2 else 3) else (if x<3222 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
