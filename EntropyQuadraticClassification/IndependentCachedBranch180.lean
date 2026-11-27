/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch179
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8544 : Finset ℕ := ([132,252,1582,1590,1596,1614,1622,1628,1678,1686,1692,1764,2590,2668,2676,2726,2732,2758,2772,3102,3180,3188,3238,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8544 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8544 132 4
  · have he : independentCachedBranchMembers8544.erase 132=independentCachedBranchMembers8542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8542
  · have he : independentCachedBranchMembers8544.filter (independentCachedEdge 132)=independentCachedBranchMembers8543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8543
def independentCachedBranchMembers8545 : Finset ℕ := ([48,72,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8545 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8545 250 5
  · have he : independentCachedBranchMembers8545.erase 250=independentCachedBranchMembers8527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8527
  · have he : independentCachedBranchMembers8545.filter (independentCachedEdge 250)=independentCachedBranchMembers8544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8544
def independentCachedBranchMembers8546 : Finset ℕ := ([1590,1594,1614,1622,1626,1692,1768,1776,2590,2666,2674,2732,2744,2772,2776,3102,3178,3186,3252,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8546 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8546 5 (fun x => (if x<2732 then (if x<1692 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1622 then 0 else (if x<1626 then 1 else 2))) else (if x<2590 then (if x<1768 then 0 else (if x<1776 then 2 else 1)) else (if x<2666 then 0 else (if x<2674 then 2 else 1)))) else (if x<3178 then (if x<2772 then (if x<2744 then 2 else 1) else (if x<2776 then 1 else (if x<3102 then 2 else 3))) else (if x<3256 then (if x<3186 then 3 else (if x<3252 then 4 else 4)) else (if x<3276 then 3 else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8547 : Finset ℕ := ([1590,1594,1614,1776,2674,2744,3186,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8547 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8547 4 (fun x => (if x<2744 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1776 then 0 else (if x<2674 then 1 else 1))) else (if x<3252 then (if x<3186 then 1 else 2) else (if x<3256 then 0 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8548 : Finset ℕ := ([1582,1590,1594,1614,1622,1626,1692,1768,1776,2590,2666,2674,2732,2744,2772,2776,3102,3178,3186,3252,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8548 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8548 1582 4
  · have he : independentCachedBranchMembers8548.erase 1582=independentCachedBranchMembers8546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8546
  · have he : independentCachedBranchMembers8548.filter (independentCachedEdge 1582)=independentCachedBranchMembers8547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8547
def independentCachedBranchMembers8549 : Finset ℕ := ([1594,1626,1768,1776,2666,2674,2744,2776,3178,3186,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8549 4 (fun x => (if x<2744 then (if x<1776 then (if x<1626 then 0 else (if x<1768 then 1 else 0)) else (if x<2666 then 1 else (if x<2674 then 0 else 1))) else (if x<3186 then (if x<2776 then 0 else (if x<3178 then 1 else 2)) else (if x<3256 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8550 : Finset ℕ := ([1582,1590,1594,1614,1622,1626,1692,1764,1768,1776,2590,2666,2674,2732,2744,2772,2776,3102,3178,3186,3252,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8550 1764 4
  · have he : independentCachedBranchMembers8550.erase 1764=independentCachedBranchMembers8548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8548
  · have he : independentCachedBranchMembers8550.filter (independentCachedEdge 1764)=independentCachedBranchMembers8549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8549
def independentCachedBranchMembers8551 : Finset ℕ := ([1582,1590,1594,1614,1622,1626,2590,2666,2674,3102,3178,3186] : List ℕ).toFinset
theorem independentCachedBranchBound8551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8551 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8551 4 (fun x => (if x<2590 then (if x<1614 then (if x<1590 then 0 else (if x<1594 then 1 else 2)) else (if x<1622 then 1 else (if x<1626 then 0 else 3))) else (if x<3102 then (if x<2666 then 0 else (if x<2674 then 2 else 3)) else (if x<3178 then 1 else (if x<3186 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8552 : Finset ℕ := ([252,1582,1590,1594,1614,1622,1626,1692,1764,1768,1776,2590,2666,2674,2732,2744,2772,2776,3102,3178,3186,3252,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8552 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8552 252 4
  · have he : independentCachedBranchMembers8552.erase 252=independentCachedBranchMembers8550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8550
  · have he : independentCachedBranchMembers8552.filter (independentCachedEdge 252)=independentCachedBranchMembers8551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8551
def independentCachedBranchMembers8553 : Finset ℕ := ([1582,1590,1614,1622,1768,1776,2590,2744,2776,3102,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8553 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8553 4 (fun x => (if x<2590 then (if x<1622 then (if x<1590 then 0 else (if x<1614 then 1 else 1)) else (if x<1768 then 0 else (if x<1776 then 2 else 3))) else (if x<3102 then (if x<2744 then 0 else (if x<2776 then 2 else 3)) else (if x<3256 then 1 else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8554 : Finset ℕ := ([132,252,1582,1590,1594,1614,1622,1626,1692,1764,1768,1776,2590,2666,2674,2732,2744,2772,2776,3102,3178,3186,3252,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8554 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8554 132 4
  · have he : independentCachedBranchMembers8554.erase 132=independentCachedBranchMembers8552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8552
  · have he : independentCachedBranchMembers8554.filter (independentCachedEdge 132)=independentCachedBranchMembers8553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8553
def independentCachedBranchMembers8555 : Finset ℕ := ([48,72,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8555 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8555 130 5
  · have he : independentCachedBranchMembers8555.erase 130=independentCachedBranchMembers8545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8545
  · have he : independentCachedBranchMembers8555.filter (independentCachedEdge 130)=independentCachedBranchMembers8554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8554
def independentCachedBranchMembers8556 : Finset ℕ := ([1594,1596,1614,1686,1690,1692,1762,1764,1768,2590,2666,2668,2738,2744,2758,2762,3102,3178,3180,3252,3256,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8556 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8556 5 (fun x => (if x<2668 then (if x<1692 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1686 then 0 else (if x<1690 then 0 else 1))) else (if x<1768 then (if x<1762 then 2 else (if x<1764 then 0 else 2)) else (if x<2590 then 1 else (if x<2666 then 0 else 0)))) else (if x<3178 then (if x<2758 then (if x<2738 then 1 else (if x<2744 then 0 else 1)) else (if x<2762 then 0 else (if x<3102 then 1 else 2))) else (if x<3256 then (if x<3180 then 3 else (if x<3252 then 4 else 2)) else (if x<3270 then 3 else (if x<3276 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8557 : Finset ℕ := ([1594,1596,1686,1768,2666,2668,2744,2758,3178,3180,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8557 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8557 4 (fun x => (if x<2744 then (if x<1768 then (if x<1596 then 0 else (if x<1686 then 1 else 0)) else (if x<2666 then 1 else (if x<2668 then 0 else 1))) else (if x<3180 then (if x<2758 then 1 else (if x<3178 then 0 else 2)) else (if x<3256 then 3 else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8558 : Finset ℕ := ([1590,1594,1596,1614,1686,1690,1692,1762,1764,1768,2590,2666,2668,2738,2744,2758,2762,3102,3178,3180,3252,3256,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8558 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8558 1590 4
  · have he : independentCachedBranchMembers8558.erase 1590=independentCachedBranchMembers8556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8556
  · have he : independentCachedBranchMembers8558.filter (independentCachedEdge 1590)=independentCachedBranchMembers8557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8557
def independentCachedBranchMembers8559 : Finset ℕ := ([1594,1596,1690,1692,1762,1764,2590,2744,2758,3102,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8559 4 (fun x => (if x<2590 then (if x<1692 then (if x<1596 then 0 else (if x<1690 then 1 else 1)) else (if x<1762 then 0 else (if x<1764 then 2 else 3))) else (if x<3102 then (if x<2744 then 0 else (if x<2758 then 0 else 2)) else (if x<3256 then 1 else (if x<3270 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8560 : Finset ℕ := ([72,1590,1594,1596,1614,1686,1690,1692,1762,1764,1768,2590,2666,2668,2738,2744,2758,2762,3102,3178,3180,3252,3256,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8560 72 4
  · have he : independentCachedBranchMembers8560.erase 72=independentCachedBranchMembers8558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8558
  · have he : independentCachedBranchMembers8560.filter (independentCachedEdge 72)=independentCachedBranchMembers8559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8559
def independentCachedBranchMembers8561 : Finset ℕ := ([1686,1692,1762,1764,1768,2590,2666,2668,3102,3178,3180] : List ℕ).toFinset
theorem independentCachedBranchBound8561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8561 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8561 4 (fun x => (if x<2590 then (if x<1762 then (if x<1692 then 0 else 1) else (if x<1764 then 0 else (if x<1768 then 1 else 2))) else (if x<3102 then (if x<2666 then 0 else (if x<2668 then 0 else 2)) else (if x<3178 then 1 else (if x<3180 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8562 : Finset ℕ := ([1686,1692,1764,2666,3178] : List ℕ).toFinset
theorem independentCachedBranchBound8562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8562 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8562 3 (fun x => (if x<1764 then (if x<1692 then 0 else 1) else (if x<2666 then 0 else (if x<3178 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8563 : Finset ℕ := ([1686,1690,1692,1762,1764,1768,2590,2666,2668,3102,3178,3180] : List ℕ).toFinset
theorem independentCachedBranchBound8563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8563 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8563 1690 3
  · have he : independentCachedBranchMembers8563.erase 1690=independentCachedBranchMembers8561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8561
  · have he : independentCachedBranchMembers8563.filter (independentCachedEdge 1690)=independentCachedBranchMembers8562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8562
def independentCachedBranchMembers8564 : Finset ℕ := ([48,72,1590,1594,1596,1614,1686,1690,1692,1762,1764,1768,2590,2666,2668,2738,2744,2758,2762,3102,3178,3180,3252,3256,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8564 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8564 48 4
  · have he : independentCachedBranchMembers8564.erase 48=independentCachedBranchMembers8560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8560
  · have he : independentCachedBranchMembers8564.filter (independentCachedEdge 48)=independentCachedBranchMembers8563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8563
def independentCachedBranchMembers8565 : Finset ℕ := ([48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8565 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8565 80 5
  · have he : independentCachedBranchMembers8565.erase 80=independentCachedBranchMembers8555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8555
  · have he : independentCachedBranchMembers8565.filter (independentCachedEdge 80)=independentCachedBranchMembers8564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8564
def independentCachedBranchMembers8566 : Finset ℕ := ([1590,1626,1628,1678,1690,1692,1762,1764,1776,2590,2674,2676,2726,2738,2762,2776,3102,3186,3188,3238,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8566 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8566 5 (fun x => (if x<2676 then (if x<1692 then (if x<1628 then (if x<1626 then 0 else 0) else (if x<1678 then 1 else (if x<1690 then 0 else 1))) else (if x<1776 then (if x<1762 then 2 else (if x<1764 then 0 else 2)) else (if x<2590 then 1 else (if x<2674 then 0 else 0)))) else (if x<3186 then (if x<2762 then (if x<2726 then 1 else (if x<2738 then 0 else 1)) else (if x<2776 then 0 else (if x<3102 then 1 else 2))) else (if x<3252 then (if x<3188 then 3 else (if x<3238 then 4 else 3)) else (if x<3276 then 2 else (if x<3288 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8567 : Finset ℕ := ([1626,1628,1678,1776,2674,2676,2726,2776,3186,3188,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8567 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8567 4 (fun x => (if x<2726 then (if x<1776 then (if x<1628 then 0 else (if x<1678 then 1 else 0)) else (if x<2674 then 1 else (if x<2676 then 0 else 1))) else (if x<3188 then (if x<2776 then 0 else (if x<3186 then 1 else 2)) else (if x<3238 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8568 : Finset ℕ := ([1590,1614,1626,1628,1678,1690,1692,1762,1764,1776,2590,2674,2676,2726,2738,2762,2776,3102,3186,3188,3238,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8568 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8568 1614 4
  · have he : independentCachedBranchMembers8568.erase 1614=independentCachedBranchMembers8566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8566
  · have he : independentCachedBranchMembers8568.filter (independentCachedEdge 1614)=independentCachedBranchMembers8567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8567
def independentCachedBranchMembers8569 : Finset ℕ := ([1678,1692,1762,1764,1776,2590,2674,2676,3102,3186,3188] : List ℕ).toFinset
theorem independentCachedBranchBound8569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8569 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8569 4 (fun x => (if x<2590 then (if x<1762 then (if x<1692 then 0 else 1) else (if x<1764 then 0 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2674 then 0 else (if x<2676 then 0 else 2)) else (if x<3186 then 1 else (if x<3188 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8570 : Finset ℕ := ([1678,1692,1764,2674,3186] : List ℕ).toFinset
theorem independentCachedBranchBound8570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8570 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8570 3 (fun x => (if x<1764 then (if x<1692 then 0 else 1) else (if x<2674 then 0 else (if x<3186 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8571 : Finset ℕ := ([1678,1690,1692,1762,1764,1776,2590,2674,2676,3102,3186,3188] : List ℕ).toFinset
theorem independentCachedBranchBound8571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8571 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8571 1690 3
  · have he : independentCachedBranchMembers8571.erase 1690=independentCachedBranchMembers8569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8569
  · have he : independentCachedBranchMembers8571.filter (independentCachedEdge 1690)=independentCachedBranchMembers8570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8570
def independentCachedBranchMembers8572 : Finset ℕ := ([72,1590,1614,1626,1628,1678,1690,1692,1762,1764,1776,2590,2674,2676,2726,2738,2762,2776,3102,3186,3188,3238,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8572 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8572 72 4
  · have he : independentCachedBranchMembers8572.erase 72=independentCachedBranchMembers8568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8568
  · have he : independentCachedBranchMembers8572.filter (independentCachedEdge 72)=independentCachedBranchMembers8571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8571
def independentCachedBranchMembers8573 : Finset ℕ := ([1626,1628,1690,1692,1762,1764,2590,2726,2776,3102,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8573 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8573 4 (fun x => (if x<2590 then (if x<1692 then (if x<1628 then 0 else (if x<1690 then 1 else 1)) else (if x<1762 then 0 else (if x<1764 then 2 else 3))) else (if x<3102 then (if x<2726 then 0 else (if x<2776 then 2 else 0)) else (if x<3238 then 1 else (if x<3288 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8574 : Finset ℕ := ([48,72,1590,1614,1626,1628,1678,1690,1692,1762,1764,1776,2590,2674,2676,2726,2738,2762,2776,3102,3186,3188,3238,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8574 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8574 48 4
  · have he : independentCachedBranchMembers8574.erase 48=independentCachedBranchMembers8572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8572
  · have he : independentCachedBranchMembers8574.filter (independentCachedEdge 48)=independentCachedBranchMembers8573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8573
def independentCachedBranchMembers8575 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8575 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8575 40 5
  · have he : independentCachedBranchMembers8575.erase 40=independentCachedBranchMembers8565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8565
  · have he : independentCachedBranchMembers8575.filter (independentCachedEdge 40)=independentCachedBranchMembers8574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8574
end EntropyDesigns.QuadraticRefinement
