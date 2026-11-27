/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch52
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4480 : Finset ℕ := ([1628,1650,1678,1686,1720,1748,1762,2618,2638,2646,2680,2716,2730,2738,2758,2792,2800,3164,3178,3214,3222,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4480 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4480 5 (fun x => (if x<2730 then (if x<1762 then (if x<1686 then (if x<1650 then 0 else (if x<1678 then 0 else 1)) else (if x<1720 then 0 else (if x<1748 then 0 else 1))) else (if x<2646 then (if x<2618 then 1 else (if x<2638 then 2 else 2)) else (if x<2680 then 0 else (if x<2716 then 0 else 0)))) else (if x<3178 then (if x<2792 then (if x<2738 then 1 else (if x<2758 then 0 else 1)) else (if x<2800 then 2 else (if x<3164 then 1 else 3))) else (if x<3256 then (if x<3214 then 2 else (if x<3222 then 3 else 4)) else (if x<3276 then 2 else (if x<3298 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4481 : Finset ℕ := ([36,80,130,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4481 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4481 36 5
  · have he : independentCachedBranchMembers4481.erase 36=independentCachedBranchMembers4479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4479
  · have he : independentCachedBranchMembers4481.filter (independentCachedEdge 36)=independentCachedBranchMembers4480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4480
def independentCachedBranchMembers4482 : Finset ℕ := ([1590,1626,1628,1650,1686,1720,1748,2618,2620,2646,2680,2714,2716,2738,2740,2776,2800,3126,3162,3164,3188,3222,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4482 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4482 5 (fun x => (if x<2716 then (if x<1748 then (if x<1650 then (if x<1626 then 0 else (if x<1628 then 0 else 1)) else (if x<1686 then 1 else (if x<1720 then 1 else 0))) else (if x<2646 then (if x<2618 then 0 else (if x<2620 then 0 else 2)) else (if x<2680 then 0 else (if x<2714 then 1 else 2)))) else (if x<3162 then (if x<2776 then (if x<2738 then 1 else (if x<2740 then 1 else 0)) else (if x<2800 then 0 else (if x<3126 then 2 else 3))) else (if x<3222 then (if x<3164 then 3 else (if x<3188 then 4 else 2)) else (if x<3256 then 4 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4483 : Finset ℕ := ([1626,1628,1720,2618,2620,2680,2714,2716,2776,3162,3164,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4483 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4483 4 (fun x => (if x<2714 then (if x<2618 then (if x<1628 then 0 else (if x<1720 then 1 else 0)) else (if x<2620 then 0 else (if x<2680 then 1 else 2))) else (if x<3162 then (if x<2716 then 2 else (if x<2776 then 3 else 0)) else (if x<3164 then 2 else (if x<3256 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4484 : Finset ℕ := ([246,1590,1626,1628,1650,1686,1720,1748,2618,2620,2646,2680,2714,2716,2738,2740,2776,2800,3126,3162,3164,3188,3222,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4484 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4484 246 4
  · have he : independentCachedBranchMembers4484.erase 246=independentCachedBranchMembers4482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4482
  · have he : independentCachedBranchMembers4484.filter (independentCachedEdge 246)=independentCachedBranchMembers4483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4483
def independentCachedBranchMembers4485 : Finset ℕ := ([1590,1686,1720,2618,2620,2714,2716,2738,2740,3126,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4485 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4485 4 (fun x => (if x<2716 then (if x<2618 then (if x<1686 then 0 else (if x<1720 then 1 else 0)) else (if x<2620 then 0 else (if x<2714 then 2 else 1))) else (if x<3126 then (if x<2738 then 3 else (if x<2740 then 2 else 0)) else (if x<3222 then 2 else (if x<3256 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4486 : Finset ℕ := ([80,246,1590,1626,1628,1650,1686,1720,1748,2618,2620,2646,2680,2714,2716,2738,2740,2776,2800,3126,3162,3164,3188,3222,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4486 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4486 80 4
  · have he : independentCachedBranchMembers4486.erase 80=independentCachedBranchMembers4484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4484
  · have he : independentCachedBranchMembers4486.filter (independentCachedEdge 80)=independentCachedBranchMembers4485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4485
def independentCachedBranchMembers4487 : Finset ℕ := ([36,80,130,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4487 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4487 238 5
  · have he : independentCachedBranchMembers4487.erase 238=independentCachedBranchMembers4481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4481
  · have he : independentCachedBranchMembers4487.filter (independentCachedEdge 238)=independentCachedBranchMembers4486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4486
def independentCachedBranchMembers4488 : Finset ℕ := ([1582,1590,1628,1644,1720,1738,1762,2620,2638,2646,2662,2714,2730,2738,2776,2792,2800,3118,3126,3164,3188,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4488 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4488 5 (fun x => (if x<2730 then (if x<1762 then (if x<1644 then (if x<1590 then 0 else (if x<1628 then 1 else 0)) else (if x<1720 then 1 else (if x<1738 then 0 else 0))) else (if x<2646 then (if x<2620 then 1 else (if x<2638 then 0 else 0)) else (if x<2662 then 2 else (if x<2714 then 1 else 2)))) else (if x<3126 then (if x<2792 then (if x<2738 then 0 else (if x<2776 then 1 else 0)) else (if x<2800 then 1 else (if x<3118 then 2 else 3))) else (if x<3256 then (if x<3164 then 4 else (if x<3188 then 3 else 2)) else (if x<3282 then 2 else (if x<3298 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4489 : Finset ℕ := ([1582,1590,1720,2638,2646,2662,2776,2792,2800,3118,3126,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4489 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4489 4 (fun x => (if x<2776 then (if x<2638 then (if x<1590 then 0 else (if x<1720 then 1 else 0)) else (if x<2646 then 0 else (if x<2662 then 1 else 2))) else (if x<3118 then (if x<2792 then 0 else (if x<2800 then 2 else 3)) else (if x<3126 then 3 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4490 : Finset ℕ := ([130,1582,1590,1628,1644,1720,1738,1762,2620,2638,2646,2662,2714,2730,2738,2776,2792,2800,3118,3126,3164,3188,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4490 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4490 130 4
  · have he : independentCachedBranchMembers4490.erase 130=independentCachedBranchMembers4488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4488
  · have he : independentCachedBranchMembers4490.filter (independentCachedEdge 130)=independentCachedBranchMembers4489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4489
def independentCachedBranchMembers4491 : Finset ℕ := ([1720,1762,2638,2646,2730,2738,2792,2800,3164,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4491 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4491 4 (fun x => (if x<2738 then (if x<2638 then (if x<1762 then 0 else 0) else (if x<2646 then 1 else (if x<2730 then 2 else 0))) else (if x<3164 then (if x<2792 then 2 else (if x<2800 then 1 else 0)) else (if x<3256 then 2 else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4492 : Finset ℕ := ([1762,2792,2800,3164,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4492 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4492 3 (fun x => (if x<2800 then (if x<2792 then 0 else 0) else (if x<3164 then 1 else (if x<3256 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4493 : Finset ℕ := ([1628,1720,1762,2638,2646,2730,2738,2792,2800,3164,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4493 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4493 1628 3
  · have he : independentCachedBranchMembers4493.erase 1628=independentCachedBranchMembers4491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4491
  · have he : independentCachedBranchMembers4493.filter (independentCachedEdge 1628)=independentCachedBranchMembers4492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4492
def independentCachedBranchMembers4494 : Finset ℕ := ([36,130,1582,1590,1628,1644,1720,1738,1762,2620,2638,2646,2662,2714,2730,2738,2776,2792,2800,3118,3126,3164,3188,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4494 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4494 36 4
  · have he : independentCachedBranchMembers4494.erase 36=independentCachedBranchMembers4490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4490
  · have he : independentCachedBranchMembers4494.filter (independentCachedEdge 36)=independentCachedBranchMembers4493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4493
def independentCachedBranchMembers4495 : Finset ℕ := ([36,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4495 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4495 132 5
  · have he : independentCachedBranchMembers4495.erase 132=independentCachedBranchMembers4487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4487
  · have he : independentCachedBranchMembers4495.filter (independentCachedEdge 132)=independentCachedBranchMembers4494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4494
def independentCachedBranchMembers4496 : Finset ℕ := ([1582,1650,1678,1720,1748,1762,1764,2618,2620,2646,2662,2714,2716,2730,2732,2758,2800,3118,3188,3214,3256,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4496 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4496 5 (fun x => (if x<2716 then (if x<1764 then (if x<1720 then (if x<1650 then 0 else (if x<1678 then 0 else 1)) else (if x<1748 then 0 else (if x<1762 then 1 else 1))) else (if x<2646 then (if x<2618 then 0 else (if x<2620 then 0 else 2)) else (if x<2662 then 2 else (if x<2714 then 0 else 2)))) else (if x<3188 then (if x<2758 then (if x<2730 then 1 else (if x<2732 then 1 else 0)) else (if x<2800 then 1 else (if x<3118 then 0 else 3))) else (if x<3282 then (if x<3214 then 2 else (if x<3256 then 4 else 2)) else (if x<3298 then 2 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4497 : Finset ℕ := ([1582,1678,1720,2618,2620,2714,2716,2730,2732,3118,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4497 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4497 4 (fun x => (if x<2716 then (if x<2618 then (if x<1678 then 0 else (if x<1720 then 1 else 0)) else (if x<2620 then 0 else (if x<2714 then 2 else 1))) else (if x<3118 then (if x<2730 then 3 else (if x<2732 then 2 else 0)) else (if x<3214 then 2 else (if x<3256 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4498 : Finset ℕ := ([246,1582,1650,1678,1720,1748,1762,1764,2618,2620,2646,2662,2714,2716,2730,2732,2758,2800,3118,3188,3214,3256,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4498 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4498 246 4
  · have he : independentCachedBranchMembers4498.erase 246=independentCachedBranchMembers4496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4496
  · have he : independentCachedBranchMembers4498.filter (independentCachedEdge 246)=independentCachedBranchMembers4497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4497
def independentCachedBranchMembers4499 : Finset ℕ := ([1720,1762,1764,2618,2620,2662,2714,2716,2758,3256,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4499 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4499 4 (fun x => (if x<2714 then (if x<2618 then (if x<1762 then 0 else (if x<1764 then 0 else 1)) else (if x<2620 then 1 else (if x<2662 then 0 else 0))) else (if x<3256 then (if x<2716 then 2 else (if x<2758 then 3 else 2)) else (if x<3298 then 2 else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4500 : Finset ℕ := ([80,246,1582,1650,1678,1720,1748,1762,1764,2618,2620,2646,2662,2714,2716,2730,2732,2758,2800,3118,3188,3214,3256,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4500 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4500 80 4
  · have he : independentCachedBranchMembers4500.erase 80=independentCachedBranchMembers4498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4498
  · have he : independentCachedBranchMembers4500.filter (independentCachedEdge 80)=independentCachedBranchMembers4499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4499
def independentCachedBranchMembers4501 : Finset ℕ := ([36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4501 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4501 72 5
  · have he : independentCachedBranchMembers4501.erase 72=independentCachedBranchMembers4495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4495
  · have he : independentCachedBranchMembers4501.filter (independentCachedEdge 72)=independentCachedBranchMembers4500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4500
def independentCachedBranchMembers4502 : Finset ℕ := ([1626,1644,1678,1686,1720,1738,1764,2620,2638,2646,2680,2714,2732,2740,2758,2792,2800,3162,3188,3214,3222,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4502 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4502 5 (fun x => (if x<2732 then (if x<1764 then (if x<1686 then (if x<1644 then 0 else (if x<1678 then 0 else 0)) else (if x<1720 then 1 else (if x<1738 then 0 else 1))) else (if x<2646 then (if x<2620 then 1 else (if x<2638 then 2 else 0)) else (if x<2680 then 2 else (if x<2714 then 0 else 0)))) else (if x<3188 then (if x<2792 then (if x<2740 then 0 else (if x<2758 then 1 else 1)) else (if x<2800 then 1 else (if x<3162 then 2 else 3))) else (if x<3256 then (if x<3214 then 2 else (if x<3222 then 3 else 4)) else (if x<3282 then 2 else (if x<3300 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4503 : Finset ℕ := ([1720,1764,2638,2646,2732,2740,2792,2800,3162,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4503 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4503 4 (fun x => (if x<2740 then (if x<2638 then (if x<1764 then 0 else 0) else (if x<2646 then 1 else (if x<2732 then 2 else 0))) else (if x<3162 then (if x<2792 then 2 else (if x<2800 then 1 else 0)) else (if x<3256 then 2 else (if x<3300 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4504 : Finset ℕ := ([1764,2792,2800,3162,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4504 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4504 3 (fun x => (if x<2800 then (if x<2792 then 0 else 0) else (if x<3162 then 1 else (if x<3256 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4505 : Finset ℕ := ([1626,1720,1764,2638,2646,2732,2740,2792,2800,3162,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4505 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4505 1626 3
  · have he : independentCachedBranchMembers4505.erase 1626=independentCachedBranchMembers4503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4503
  · have he : independentCachedBranchMembers4505.filter (independentCachedEdge 1626)=independentCachedBranchMembers4504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4504
def independentCachedBranchMembers4506 : Finset ℕ := ([130,1626,1644,1678,1686,1720,1738,1764,2620,2638,2646,2680,2714,2732,2740,2758,2792,2800,3162,3188,3214,3222,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4506 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4506 130 4
  · have he : independentCachedBranchMembers4506.erase 130=independentCachedBranchMembers4502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4502
  · have he : independentCachedBranchMembers4506.filter (independentCachedEdge 130)=independentCachedBranchMembers4505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4505
def independentCachedBranchMembers4507 : Finset ℕ := ([1678,1686,1720,2638,2646,2680,2758,2792,2800,3214,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4507 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4507 4 (fun x => (if x<2758 then (if x<2638 then (if x<1686 then 0 else (if x<1720 then 1 else 0)) else (if x<2646 then 0 else (if x<2680 then 1 else 0))) else (if x<3214 then (if x<2792 then 2 else (if x<2800 then 2 else 3)) else (if x<3222 then 3 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4508 : Finset ℕ := ([36,130,1626,1644,1678,1686,1720,1738,1764,2620,2638,2646,2680,2714,2732,2740,2758,2792,2800,3162,3188,3214,3222,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4508 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4508 36 4
  · have he : independentCachedBranchMembers4508.erase 36=independentCachedBranchMembers4506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4506
  · have he : independentCachedBranchMembers4508.filter (independentCachedEdge 36)=independentCachedBranchMembers4507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4507
def independentCachedBranchMembers4509 : Finset ℕ := ([34,36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4509 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4509 34 5
  · have he : independentCachedBranchMembers4509.erase 34=independentCachedBranchMembers4501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4501
  · have he : independentCachedBranchMembers4509.filter (independentCachedEdge 34)=independentCachedBranchMembers4508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4508
def independentCachedBranchMembers4510 : Finset ℕ := ([1590,1626,1644,1678,1720,1738,1748,1762,2620,2638,2662,2680,2714,2732,2738,2792,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4510 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4510 5 (fun x => (if x<2714 then (if x<1748 then (if x<1678 then (if x<1626 then 0 else (if x<1644 then 0 else 0)) else (if x<1720 then 0 else (if x<1738 then 0 else 1))) else (if x<2638 then (if x<1762 then 0 else (if x<2620 then 0 else 1)) else (if x<2662 then 1 else (if x<2680 then 2 else 2)))) else (if x<3178 then (if x<2792 then (if x<2732 then 1 else (if x<2738 then 2 else 2)) else (if x<3118 then 1 else (if x<3164 then 3 else 3))) else (if x<3276 then (if x<3188 then 4 else (if x<3222 then 4 else 3)) else (if x<3282 then 4 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4511 : Finset ℕ := ([1590,1626,1678,1762,2620,2638,2714,2792,3178,3188,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4511 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4511 4 (fun x => (if x<2714 then (if x<1762 then (if x<1626 then 0 else (if x<1678 then 0 else 0)) else (if x<2620 then 0 else (if x<2638 then 1 else 1))) else (if x<3188 then (if x<2792 then 1 else (if x<3178 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
