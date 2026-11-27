/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch54
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4544 : Finset ℕ := ([130,238,1582,1628,1644,1650,1686,1702,1720,1738,1764,2620,2638,2714,2730,2740,2758,2776,2792,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4544 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4544 130 4
  · have he : independentCachedBranchMembers4544.erase 130=independentCachedBranchMembers4542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4542
  · have he : independentCachedBranchMembers4544.filter (independentCachedEdge 130)=independentCachedBranchMembers4543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4543
def independentCachedBranchMembers4545 : Finset ℕ := ([1582,1650,1720,1764,2620,2714,2730,2758,3188,3214,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4545 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4545 4 (fun x => (if x<2730 then (if x<1764 then (if x<1650 then 0 else (if x<1720 then 0 else 0)) else (if x<2620 then 0 else (if x<2714 then 1 else 1))) else (if x<3214 then (if x<2758 then 2 else (if x<3188 then 2 else 1)) else (if x<3282 then 2 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4546 : Finset ℕ := ([72,130,238,1582,1628,1644,1650,1686,1702,1720,1738,1764,2620,2638,2714,2730,2740,2758,2776,2792,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4546 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4546 72 4
  · have he : independentCachedBranchMembers4546.erase 72=independentCachedBranchMembers4544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4544
  · have he : independentCachedBranchMembers4546.filter (independentCachedEdge 72)=independentCachedBranchMembers4545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4545
def independentCachedBranchMembers4547 : Finset ℕ := ([1628,1650,1686,1720,2638,2730,2758,2792,3178,3214,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4547 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4547 4 (fun x => (if x<2758 then (if x<1720 then (if x<1650 then 0 else (if x<1686 then 0 else 0)) else (if x<2638 then 0 else (if x<2730 then 1 else 1))) else (if x<3214 then (if x<2792 then 2 else (if x<3178 then 2 else 1)) else (if x<3276 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4548 : Finset ℕ := ([36,72,130,238,1582,1628,1644,1650,1686,1702,1720,1738,1764,2620,2638,2714,2730,2740,2758,2776,2792,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4548 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4548 36 4
  · have he : independentCachedBranchMembers4548.erase 36=independentCachedBranchMembers4546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4546
  · have he : independentCachedBranchMembers4548.filter (independentCachedEdge 36)=independentCachedBranchMembers4547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4547
def independentCachedBranchMembers4549 : Finset ℕ := ([36,72,130,238,1582,1628,1686,1764,2620,2638,2714,2792,3126,3162,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4549 4 (fun x => (if x<2620 then (if x<1582 then (if x<130 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1686 then (if x<1628 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3126 then (if x<2714 then (if x<2638 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3214 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4550 : Finset ℕ := ([36,72,130,238,1582,1628,1644,1650,1686,1702,1720,1738,1748,1764,2620,2638,2714,2730,2740,2758,2776,2792,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4550 1748 4
  · have he : independentCachedBranchMembers4550.erase 1748=independentCachedBranchMembers4548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4548
  · have he : independentCachedBranchMembers4550.filter (independentCachedEdge 1748)=independentCachedBranchMembers4549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4549
def independentCachedBranchMembers4551 : Finset ℕ := ([34,36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4551 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4551 3186 5
  · have he : independentCachedBranchMembers4551.erase 3186=independentCachedBranchMembers4537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4537
  · have he : independentCachedBranchMembers4551.filter (independentCachedEdge 3186)=independentCachedBranchMembers4550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4550
def independentCachedBranchMembers4552 : Finset ℕ := ([1590,1626,1644,1678,1702,1720,1748,1762,2618,2646,2716,2730,2740,2758,2776,2800,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4552 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4552 5 (fun x => (if x<2740 then (if x<1748 then (if x<1678 then (if x<1626 then 0 else (if x<1644 then 0 else 0)) else (if x<1702 then 0 else (if x<1720 then 1 else 0))) else (if x<2646 then (if x<1762 then 0 else (if x<2618 then 0 else 2)) else (if x<2716 then 2 else (if x<2730 then 2 else 1)))) else (if x<3178 then (if x<2800 then (if x<2758 then 1 else (if x<2776 then 1 else 1)) else (if x<3118 then 2 else (if x<3164 then 3 else 3))) else (if x<3276 then (if x<3188 then 4 else (if x<3222 then 4 else 3)) else (if x<3282 then 4 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4553 : Finset ℕ := ([1590,1626,1678,1762,2730,2740,2758,2776,3118,3164,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4553 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4553 4 (fun x => (if x<2758 then (if x<1762 then (if x<1626 then 0 else (if x<1678 then 0 else 0)) else (if x<2730 then 0 else (if x<2740 then 1 else 1))) else (if x<3164 then (if x<2776 then 1 else (if x<3118 then 1 else 2)) else (if x<3222 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4554 : Finset ℕ := ([1590,1626,1644,1650,1678,1702,1720,1748,1762,2618,2646,2716,2730,2740,2758,2776,2800,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4554 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4554 1650 4
  · have he : independentCachedBranchMembers4554.erase 1650=independentCachedBranchMembers4552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4552
  · have he : independentCachedBranchMembers4554.filter (independentCachedEdge 1650)=independentCachedBranchMembers4553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4553
def independentCachedBranchMembers4555 : Finset ℕ := ([1626,1644,1678,1720,2618,2716,2730,2776,3118,3164,3178,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4555 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4555 4 (fun x => (if x<2730 then (if x<1720 then (if x<1644 then 0 else (if x<1678 then 0 else 0)) else (if x<2618 then 0 else (if x<2716 then 1 else 1))) else (if x<3164 then (if x<2776 then 2 else (if x<3118 then 2 else 2)) else (if x<3178 then 2 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4556 : Finset ℕ := ([246,1590,1626,1644,1650,1678,1702,1720,1748,1762,2618,2646,2716,2730,2740,2758,2776,2800,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4556 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4556 246 4
  · have he : independentCachedBranchMembers4556.erase 246=independentCachedBranchMembers4554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4554
  · have he : independentCachedBranchMembers4556.filter (independentCachedEdge 246)=independentCachedBranchMembers4555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4555
def independentCachedBranchMembers4557 : Finset ℕ := ([1590,1644,1720,1762,2646,2730,2776,2800,3118,3164,3188,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4557 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4557 4 (fun x => (if x<2776 then (if x<1762 then (if x<1644 then 0 else (if x<1720 then 0 else 0)) else (if x<2646 then 0 else (if x<2730 then 1 else 2))) else (if x<3164 then (if x<2800 then 1 else (if x<3118 then 2 else 2)) else (if x<3188 then 1 else (if x<3282 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4558 : Finset ℕ := ([132,246,1590,1626,1644,1650,1678,1702,1720,1748,1762,2618,2646,2716,2730,2740,2758,2776,2800,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4558 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4558 132 4
  · have he : independentCachedBranchMembers4558.erase 132=independentCachedBranchMembers4556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4556
  · have he : independentCachedBranchMembers4558.filter (independentCachedEdge 132)=independentCachedBranchMembers4557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4557
def independentCachedBranchMembers4559 : Finset ℕ := ([1590,1644,1720,1762,2618,2716,2740,2758,3178,3222,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4559 4 (fun x => (if x<2740 then (if x<1762 then (if x<1644 then 0 else (if x<1720 then 0 else 0)) else (if x<2618 then 0 else (if x<2716 then 1 else 1))) else (if x<3222 then (if x<2758 then 2 else (if x<3178 then 2 else 1)) else (if x<3276 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4560 : Finset ℕ := ([80,132,246,1590,1626,1644,1650,1678,1702,1720,1748,1762,2618,2646,2716,2730,2740,2758,2776,2800,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4560 80 4
  · have he : independentCachedBranchMembers4560.erase 80=independentCachedBranchMembers4558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4558
  · have he : independentCachedBranchMembers4560.filter (independentCachedEdge 80)=independentCachedBranchMembers4559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4559
def independentCachedBranchMembers4561 : Finset ℕ := ([1626,1644,1678,1720,2646,2740,2758,2800,3188,3222,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4561 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4561 4 (fun x => (if x<2758 then (if x<1720 then (if x<1644 then 0 else (if x<1678 then 0 else 0)) else (if x<2646 then 0 else (if x<2740 then 1 else 1))) else (if x<3222 then (if x<2800 then 2 else (if x<3188 then 2 else 1)) else (if x<3282 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4562 : Finset ℕ := ([34,80,132,246,1590,1626,1644,1650,1678,1702,1720,1748,1762,2618,2646,2716,2730,2740,2758,2776,2800,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4562 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4562 34 4
  · have he : independentCachedBranchMembers4562.erase 34=independentCachedBranchMembers4560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4560
  · have he : independentCachedBranchMembers4562.filter (independentCachedEdge 34)=independentCachedBranchMembers4561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4561
def independentCachedBranchMembers4563 : Finset ℕ := ([34,80,132,246,1590,1626,1678,1762,2618,2646,2716,2800,3118,3164,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4563 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4563 4 (fun x => (if x<2618 then (if x<1590 then (if x<132 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1678 then (if x<1626 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3118 then (if x<2716 then (if x<2646 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3222 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4564 : Finset ℕ := ([34,80,132,246,1590,1626,1644,1650,1678,1702,1720,1738,1748,1762,2618,2646,2716,2730,2740,2758,2776,2800,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4564 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4564 1738 4
  · have he : independentCachedBranchMembers4564.erase 1738=independentCachedBranchMembers4562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4562
  · have he : independentCachedBranchMembers4564.filter (independentCachedEdge 1738)=independentCachedBranchMembers4563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4563
def independentCachedBranchMembers4565 : Finset ℕ := ([34,36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4565 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4565 3180 5
  · have he : independentCachedBranchMembers4565.erase 3180=independentCachedBranchMembers4551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4551
  · have he : independentCachedBranchMembers4565.filter (independentCachedEdge 3180)=independentCachedBranchMembers4564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4564
def independentCachedBranchMembers4566 : Finset ℕ := ([130,246,1644,1650,1702,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4566 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4566 5 (fun x => (if x<2738 then (if x<1738 then (if x<1644 then (if x<246 then 0 else 0) else (if x<1650 then 1 else (if x<1702 then 1 else 0))) else (if x<2680 then (if x<1748 then 1 else (if x<2662 then 1 else 2)) else (if x<2730 then 2 else (if x<2732 then 2 else 3)))) else (if x<3162 then (if x<2776 then (if x<2740 then 0 else (if x<2758 then 2 else 0)) else (if x<3118 then 3 else (if x<3126 then 3 else 4))) else (if x<3222 then (if x<3164 then 3 else (if x<3214 then 4 else 4)) else (if x<3298 then 0 else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4567 : Finset ℕ := ([1644,1738,2662,2738,2740,2758,3126,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4567 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4567 4 (fun x => (if x<2758 then (if x<2662 then (if x<1738 then 0 else 0) else (if x<2738 then 1 else (if x<2740 then 1 else 2))) else (if x<3222 then (if x<3126 then 2 else 1) else (if x<3298 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4568 : Finset ℕ := ([80,130,246,1644,1650,1702,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4568 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4568 80 4
  · have he : independentCachedBranchMembers4568.erase 80=independentCachedBranchMembers4566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4566
  · have he : independentCachedBranchMembers4568.filter (independentCachedEdge 80)=independentCachedBranchMembers4567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4567
def independentCachedBranchMembers4569 : Finset ℕ := ([1650,1748,2680,2730,2738,2758,3164,3214,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4569 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4569 4 (fun x => (if x<2758 then (if x<2680 then (if x<1748 then 0 else 0) else (if x<2730 then 1 else (if x<2738 then 1 else 2))) else (if x<3214 then (if x<3164 then 2 else 1) else (if x<3222 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4570 : Finset ℕ := ([36,80,130,246,1644,1650,1702,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4570 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4570 36 4
  · have he : independentCachedBranchMembers4570.erase 36=independentCachedBranchMembers4568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4568
  · have he : independentCachedBranchMembers4570.filter (independentCachedEdge 36)=independentCachedBranchMembers4569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4569
def independentCachedBranchMembers4571 : Finset ℕ := ([80,246,1650,1748,2680,2738,2740,2776,3126,3162,3164,3222] : List ℕ).toFinset
theorem independentCachedBranchBound4571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4571 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4571 4 (fun x => (if x<2740 then (if x<1748 then (if x<246 then 0 else (if x<1650 then 0 else 0)) else (if x<2680 then 0 else (if x<2738 then 1 else 1))) else (if x<3162 then (if x<2776 then 2 else (if x<3126 then 2 else 2)) else (if x<3164 then 2 else (if x<3222 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4572 : Finset ℕ := ([36,80,130,238,246,1644,1650,1702,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4572 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4572 238 4
  · have he : independentCachedBranchMembers4572.erase 238=independentCachedBranchMembers4570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4570
  · have he : independentCachedBranchMembers4572.filter (independentCachedEdge 238)=independentCachedBranchMembers4571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4571
def independentCachedBranchMembers4573 : Finset ℕ := ([36,130,1644,1738,2662,2730,2738,2776,3118,3126,3164,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4573 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4573 4 (fun x => (if x<2738 then (if x<1738 then (if x<130 then 0 else (if x<1644 then 0 else 0)) else (if x<2662 then 0 else (if x<2730 then 1 else 1))) else (if x<3126 then (if x<2776 then 2 else (if x<3118 then 2 else 1)) else (if x<3164 then 2 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4574 : Finset ℕ := ([36,80,130,132,238,246,1644,1650,1702,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4574 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4574 132 4
  · have he : independentCachedBranchMembers4574.erase 132=independentCachedBranchMembers4572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4572
  · have he : independentCachedBranchMembers4574.filter (independentCachedEdge 132)=independentCachedBranchMembers4573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4573
def independentCachedBranchMembers4575 : Finset ℕ := ([80,246,1650,1748,2662,2730,2732,2758,3118,3214,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4575 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4575 4 (fun x => (if x<2732 then (if x<1748 then (if x<246 then 0 else (if x<1650 then 0 else 0)) else (if x<2662 then 0 else (if x<2730 then 1 else 1))) else (if x<3214 then (if x<2758 then 2 else (if x<3118 then 2 else 1)) else (if x<3298 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
