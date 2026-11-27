/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch85
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5536 : Finset ℕ := ([1708,1748,1752,2606,2646,2650,2652,2710,2714,2716,2788,2792,3102,3174,3178,3180,3238,3242,3244,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5536 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5536 5 (fun x => (if x<2792 then (if x<2650 then (if x<1752 then (if x<1748 then 0 else 0) else (if x<2606 then 1 else (if x<2646 then 0 else 0))) else (if x<2714 then (if x<2652 then 1 else (if x<2710 then 2 else 2)) else (if x<2716 then 3 else (if x<2788 then 0 else 0)))) else (if x<3238 then (if x<3174 then (if x<3102 then 1 else 2) else (if x<3178 then 3 else (if x<3180 then 4 else 2))) else (if x<3282 then (if x<3242 then 2 else (if x<3244 then 3 else 4)) else (if x<3284 then 3 else (if x<3288 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5537 : Finset ℕ := ([1708,2646,2650,2716,3102,3180,3238,3242,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5537 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5537 4 (fun x => (if x<3180 then (if x<2650 then (if x<2646 then 0 else 0) else (if x<2716 then 1 else (if x<3102 then 0 else 1))) else (if x<3242 then (if x<3238 then 2 else 1) else (if x<3284 then 2 else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5538 : Finset ℕ := ([1644,1708,1748,1752,2606,2646,2650,2652,2710,2714,2716,2788,2792,3102,3174,3178,3180,3238,3242,3244,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5538 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5538 1644 4
  · have he : independentCachedBranchMembers5538.erase 1644=independentCachedBranchMembers5536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5536
  · have he : independentCachedBranchMembers5538.filter (independentCachedEdge 1644)=independentCachedBranchMembers5537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5537
def independentCachedBranchMembers5539 : Finset ℕ := ([1644,1708,1748,1752,2652,2716,2788,2792,3180,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5539 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5539 4 (fun x => (if x<2788 then (if x<1752 then (if x<1708 then 0 else (if x<1748 then 1 else 0)) else (if x<2652 then 1 else (if x<2716 then 0 else 1))) else (if x<3244 then (if x<2792 then 0 else (if x<3180 then 1 else 2)) else (if x<3284 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5540 : Finset ℕ := ([1644,1708,1748,1752,2606,2646,2650,2652,2710,2714,2716,2786,2788,2792,3102,3174,3178,3180,3238,3242,3244,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5540 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5540 2786 4
  · have he : independentCachedBranchMembers5540.erase 2786=independentCachedBranchMembers5538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5538
  · have he : independentCachedBranchMembers5540.filter (independentCachedEdge 2786)=independentCachedBranchMembers5539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5539
def independentCachedBranchMembers5541 : Finset ℕ := ([1708,1752,2646,2714,2716,2792,3102,3178,3180,3238,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5541 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5541 4 (fun x => (if x<3102 then (if x<2714 then (if x<1752 then 0 else (if x<2646 then 0 else 1)) else (if x<2716 then 1 else (if x<2792 then 0 else 0))) else (if x<3238 then (if x<3178 then 1 else (if x<3180 then 2 else 3)) else (if x<3282 then 2 else (if x<3284 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5542 : Finset ℕ := ([1644,1702,1708,1748,1752,2606,2646,2650,2652,2710,2714,2716,2786,2788,2792,3102,3174,3178,3180,3238,3242,3244,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5542 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5542 1702 4
  · have he : independentCachedBranchMembers5542.erase 1702=independentCachedBranchMembers5540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5540
  · have he : independentCachedBranchMembers5542.filter (independentCachedEdge 1702)=independentCachedBranchMembers5541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5541
def independentCachedBranchMembers5543 : Finset ℕ := ([1644,1748,2646,2652,2714,2788,3102,3178,3238,3244,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5543 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5543 4 (fun x => (if x<3102 then (if x<2652 then (if x<1748 then 0 else (if x<2646 then 0 else 1)) else (if x<2714 then 0 else (if x<2788 then 1 else 0))) else (if x<3244 then (if x<3178 then 1 else (if x<3238 then 2 else 2)) else (if x<3282 then 3 else (if x<3288 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5544 : Finset ℕ := ([1642,1644,1702,1708,1748,1752,2606,2646,2650,2652,2710,2714,2716,2786,2788,2792,3102,3174,3178,3180,3238,3242,3244,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5544 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5544 1642 4
  · have he : independentCachedBranchMembers5544.erase 1642=independentCachedBranchMembers5542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5542
  · have he : independentCachedBranchMembers5544.filter (independentCachedEdge 1642)=independentCachedBranchMembers5543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5543
def independentCachedBranchMembers5545 : Finset ℕ := ([48,72,132,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5545 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5545 48 5
  · have he : independentCachedBranchMembers5545.erase 48=independentCachedBranchMembers5535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5535
  · have he : independentCachedBranchMembers5545.filter (independentCachedEdge 48)=independentCachedBranchMembers5544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5544
def independentCachedBranchMembers5546 : Finset ℕ := ([1708,1714,1738,1748,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5546 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5546 5 (fun x => (if x<2650 then (if x<2614 then (if x<1738 then (if x<1714 then 0 else 0) else (if x<1748 then 0 else (if x<2606 then 0 else 1))) else (if x<2620 then (if x<2618 then 2 else 3) else (if x<2638 then 4 else (if x<2646 then 2 else 1)))) else (if x<2716 then (if x<2702 then (if x<2652 then 4 else 3) else (if x<2710 then 3 else (if x<2714 then 4 else 1))) else (if x<2788 then (if x<2786 then 2 else 1) else (if x<2792 then 2 else (if x<2800 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5547 : Finset ℕ := ([1738,1748,2618,2620,2638,2646,2702,2710,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound5547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5547 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5547 4 (fun x => (if x<2646 then (if x<2618 then (if x<1748 then 0 else 0) else (if x<2620 then 1 else (if x<2638 then 2 else 1))) else (if x<2710 then (if x<2702 then 2 else 2) else (if x<2786 then 1 else (if x<2788 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5548 : Finset ℕ := ([1708,1714,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5548 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5548 1752 4
  · have he : independentCachedBranchMembers5548.erase 1752=independentCachedBranchMembers5546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5546
  · have he : independentCachedBranchMembers5548.filter (independentCachedEdge 1752)=independentCachedBranchMembers5547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5547
def independentCachedBranchMembers5549 : Finset ℕ := ([1738,1748,2606,2614,2650,2652,2714,2716,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5549 4 (fun x => (if x<2652 then (if x<2606 then (if x<1748 then 0 else 0) else (if x<2614 then 1 else (if x<2650 then 2 else 1))) else (if x<2716 then (if x<2714 then 2 else 2) else (if x<2792 then 1 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5550 : Finset ℕ := ([1708,1714,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5550 1734 4
  · have he : independentCachedBranchMembers5550.erase 1734=independentCachedBranchMembers5548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5548
  · have he : independentCachedBranchMembers5550.filter (independentCachedEdge 1734)=independentCachedBranchMembers5549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5549
def independentCachedBranchMembers5551 : Finset ℕ := ([1708,1714,2606,2620,2638,2652,2710,2714,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5551 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5551 4 (fun x => (if x<2652 then (if x<2606 then (if x<1714 then 0 else 0) else (if x<2620 then 1 else (if x<2638 then 2 else 2))) else (if x<2714 then (if x<2710 then 1 else 1) else (if x<2788 then 2 else (if x<2792 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5552 : Finset ℕ := ([1650,1708,1714,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5552 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5552 1650 4
  · have he : independentCachedBranchMembers5552.erase 1650=independentCachedBranchMembers5550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5550
  · have he : independentCachedBranchMembers5552.filter (independentCachedEdge 1650)=independentCachedBranchMembers5551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5551
def independentCachedBranchMembers5553 : Finset ℕ := ([1708,1714,2614,2618,2646,2650,2702,2716,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5553 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5553 4 (fun x => (if x<2650 then (if x<2614 then (if x<1714 then 0 else 0) else (if x<2618 then 1 else (if x<2646 then 2 else 2))) else (if x<2716 then (if x<2702 then 1 else 1) else (if x<2786 then 2 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5554 : Finset ℕ := ([1644,1650,1708,1714,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5554 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5554 1644 4
  · have he : independentCachedBranchMembers5554.erase 1644=independentCachedBranchMembers5552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5552
  · have he : independentCachedBranchMembers5554.filter (independentCachedEdge 1644)=independentCachedBranchMembers5553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5553
def independentCachedBranchMembers5555 : Finset ℕ := ([1708,1714,1734,1752,2606,2614,2650,2652,2702,2710,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound5555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5555 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5555 4 (fun x => (if x<2650 then (if x<1752 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<2606 then 0 else (if x<2614 then 1 else 2))) else (if x<2710 then (if x<2652 then 1 else (if x<2702 then 2 else 2)) else (if x<2786 then 1 else (if x<2788 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5556 : Finset ℕ := ([1644,1650,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5556 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5556 1720 4
  · have he : independentCachedBranchMembers5556.erase 1720=independentCachedBranchMembers5554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5554
  · have he : independentCachedBranchMembers5556.filter (independentCachedEdge 1720)=independentCachedBranchMembers5555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5555
def independentCachedBranchMembers5557 : Finset ℕ := ([1708,1714,1734,1752,2618,2620,2638,2646,2714,2716,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5557 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5557 4 (fun x => (if x<2638 then (if x<1752 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<2618 then 0 else (if x<2620 then 1 else 2))) else (if x<2716 then (if x<2646 then 1 else (if x<2714 then 2 else 2)) else (if x<2792 then 1 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5558 : Finset ℕ := ([1644,1650,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5558 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5558 1702 4
  · have he : independentCachedBranchMembers5558.erase 1702=independentCachedBranchMembers5556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5556
  · have he : independentCachedBranchMembers5558.filter (independentCachedEdge 1702)=independentCachedBranchMembers5557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5557
def independentCachedBranchMembers5559 : Finset ℕ := ([1644,1650,1738,1748,2606,2618,2638,2650,2710,2716,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5559 4 (fun x => (if x<2638 then (if x<1748 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<2606 then 0 else (if x<2618 then 1 else 2))) else (if x<2716 then (if x<2650 then 2 else (if x<2710 then 1 else 1)) else (if x<2786 then 2 else (if x<2792 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5560 : Finset ℕ := ([1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5560 1652 4
  · have he : independentCachedBranchMembers5560.erase 1652=independentCachedBranchMembers5558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5558
  · have he : independentCachedBranchMembers5560.filter (independentCachedEdge 1652)=independentCachedBranchMembers5559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5559
def independentCachedBranchMembers5561 : Finset ℕ := ([1644,1650,1738,1748,2614,2620,2646,2652,2702,2714,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5561 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5561 4 (fun x => (if x<2646 then (if x<1748 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<2614 then 0 else (if x<2620 then 1 else 2))) else (if x<2714 then (if x<2652 then 2 else (if x<2702 then 1 else 1)) else (if x<2788 then 2 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5562 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5562 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5562 1642 4
  · have he : independentCachedBranchMembers5562.erase 1642=independentCachedBranchMembers5560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5560
  · have he : independentCachedBranchMembers5562.filter (independentCachedEdge 1642)=independentCachedBranchMembers5561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5561
def independentCachedBranchMembers5563 : Finset ℕ := ([48,72,132,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5563 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5563 3072 5
  · have he : independentCachedBranchMembers5563.erase 3072=independentCachedBranchMembers5545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5545
  · have he : independentCachedBranchMembers5563.filter (independentCachedEdge 3072)=independentCachedBranchMembers5562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5562
def independentCachedBranchMembers5564 : Finset ℕ := ([132,252,1652,1708,1734,1748,2606,2620,2646,2652,2702,2710,2716,2788,3102,3174,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5564 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5564 5 (fun x => (if x<2716 then (if x<2606 then (if x<1708 then (if x<252 then 0 else (if x<1652 then 0 else 1)) else (if x<1734 then 0 else (if x<1748 then 1 else 0))) else (if x<2652 then (if x<2620 then 2 else (if x<2646 then 1 else 1)) else (if x<2702 then 2 else (if x<2710 then 1 else 2)))) else (if x<3238 then (if x<3174 then (if x<2788 then 0 else (if x<3102 then 0 else 2)) else (if x<3180 then 3 else (if x<3188 then 2 else 4))) else (if x<3270 then (if x<3244 then 2 else (if x<3252 then 3 else 0)) else (if x<3276 then 4 else (if x<3284 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5565 : Finset ℕ := ([252,1708,1734,2620,2646,2716,3102,3180,3188,3238,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5565 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5565 4 (fun x => (if x<3102 then (if x<2620 then (if x<1708 then 0 else (if x<1734 then 0 else 1)) else (if x<2646 then 0 else (if x<2716 then 1 else 2))) else (if x<3238 then (if x<3180 then 2 else (if x<3188 then 0 else 3)) else (if x<3276 then 3 else (if x<3284 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5566 : Finset ℕ := ([132,252,1652,1702,1708,1734,1748,2606,2620,2646,2652,2702,2710,2716,2788,3102,3174,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5566 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5566 1702 4
  · have he : independentCachedBranchMembers5566.erase 1702=independentCachedBranchMembers5564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5564
  · have he : independentCachedBranchMembers5566.filter (independentCachedEdge 1702)=independentCachedBranchMembers5565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5565
def independentCachedBranchMembers5567 : Finset ℕ := ([132,1652,1708,2646,2702,2716,3102,3180,3238,3252,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5567 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5567 4 (fun x => (if x<3102 then (if x<2646 then (if x<1652 then 0 else (if x<1708 then 1 else 0)) else (if x<2702 then 1 else (if x<2716 then 0 else 2))) else (if x<3252 then (if x<3180 then 2 else (if x<3238 then 3 else 0)) else (if x<3270 then 2 else (if x<3284 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
