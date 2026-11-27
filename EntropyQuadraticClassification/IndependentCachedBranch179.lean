/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch178
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8512 : Finset ℕ := ([1582,1590,1594,1614,1622,1626,1678,1686,1690,1762,2590,2666,2674,2726,2738,2758,2762,3102,3178,3186,3238,3242,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8512 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8512 1690 4
  · have he : independentCachedBranchMembers8512.erase 1690=independentCachedBranchMembers8510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8510
  · have he : independentCachedBranchMembers8512.filter (independentCachedEdge 1690)=independentCachedBranchMembers8511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8511
def independentCachedBranchMembers8513 : Finset ℕ := ([252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8513 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8513 252 5
  · have he : independentCachedBranchMembers8513.erase 252=independentCachedBranchMembers8507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8507
  · have he : independentCachedBranchMembers8513.filter (independentCachedEdge 252)=independentCachedBranchMembers8512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8512
def independentCachedBranchMembers8514 : Finset ℕ := ([1590,1596,1614,1622,1628,1690,1768,1776,2590,2668,2676,2738,2744,2762,2776,3102,3180,3188,3242,3256,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8514 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8514 5 (fun x => (if x<2738 then (if x<1690 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1622 then 0 else (if x<1628 then 1 else 2))) else (if x<2590 then (if x<1768 then 0 else (if x<1776 then 2 else 1)) else (if x<2668 then 0 else (if x<2676 then 2 else 1)))) else (if x<3180 then (if x<2762 then (if x<2744 then 0 else 1) else (if x<2776 then 0 else (if x<3102 then 2 else 3))) else (if x<3256 then (if x<3188 then 3 else (if x<3242 then 4 else 3)) else (if x<3282 then 4 else (if x<3288 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8515 : Finset ℕ := ([1590,1596,1614,1776,2676,2738,2744,2762,3188,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8515 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8515 4 (fun x => (if x<2738 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1776 then 0 else (if x<2676 then 1 else 1))) else (if x<2762 then (if x<2744 then 0 else 1) else (if x<3188 then 0 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8516 : Finset ℕ := ([1582,1590,1596,1614,1622,1628,1690,1768,1776,2590,2668,2676,2738,2744,2762,2776,3102,3180,3188,3242,3256,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8516 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8516 1582 4
  · have he : independentCachedBranchMembers8516.erase 1582=independentCachedBranchMembers8514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8514
  · have he : independentCachedBranchMembers8516.filter (independentCachedEdge 1582)=independentCachedBranchMembers8515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8515
def independentCachedBranchMembers8517 : Finset ℕ := ([1596,1628,1768,1776,2668,2676,2744,2776,3180,3188,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8517 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8517 4 (fun x => (if x<2744 then (if x<1776 then (if x<1628 then 0 else (if x<1768 then 1 else 0)) else (if x<2668 then 1 else (if x<2676 then 0 else 1))) else (if x<3188 then (if x<2776 then 0 else (if x<3180 then 1 else 2)) else (if x<3256 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8518 : Finset ℕ := ([1582,1590,1596,1614,1622,1628,1690,1762,1768,1776,2590,2668,2676,2738,2744,2762,2776,3102,3180,3188,3242,3256,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8518 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8518 1762 4
  · have he : independentCachedBranchMembers8518.erase 1762=independentCachedBranchMembers8516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8516
  · have he : independentCachedBranchMembers8518.filter (independentCachedEdge 1762)=independentCachedBranchMembers8517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8517
def independentCachedBranchMembers8519 : Finset ℕ := ([132,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8519 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8519 132 5
  · have he : independentCachedBranchMembers8519.erase 132=independentCachedBranchMembers8513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8513
  · have he : independentCachedBranchMembers8519.filter (independentCachedEdge 132)=independentCachedBranchMembers8518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8518
def independentCachedBranchMembers8520 : Finset ℕ := ([1594,1596,1622,1678,1690,1692,1762,1764,1776,2590,2674,2676,2732,2744,2758,2772,3102,3186,3188,3242,3256,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8520 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8520 5 (fun x => (if x<2676 then (if x<1692 then (if x<1622 then (if x<1596 then 0 else 1) else (if x<1678 then 0 else (if x<1690 then 0 else 1))) else (if x<1776 then (if x<1762 then 2 else (if x<1764 then 0 else 2)) else (if x<2590 then 1 else (if x<2674 then 0 else 0)))) else (if x<3186 then (if x<2758 then (if x<2732 then 1 else (if x<2744 then 2 else 1)) else (if x<2772 then 0 else (if x<3102 then 2 else 3))) else (if x<3256 then (if x<3188 then 3 else (if x<3242 then 4 else 3)) else (if x<3270 then 4 else (if x<3282 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8521 : Finset ℕ := ([1594,1596,1678,1776,2674,2676,2744,2758,3186,3188,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8521 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8521 4 (fun x => (if x<2744 then (if x<1776 then (if x<1596 then 0 else (if x<1678 then 1 else 0)) else (if x<2674 then 1 else (if x<2676 then 0 else 1))) else (if x<3188 then (if x<2758 then 1 else (if x<3186 then 0 else 2)) else (if x<3256 then 3 else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8522 : Finset ℕ := ([1582,1594,1596,1622,1678,1690,1692,1762,1764,1776,2590,2674,2676,2732,2744,2758,2772,3102,3186,3188,3242,3256,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8522 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8522 1582 4
  · have he : independentCachedBranchMembers8522.erase 1582=independentCachedBranchMembers8520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8520
  · have he : independentCachedBranchMembers8522.filter (independentCachedEdge 1582)=independentCachedBranchMembers8521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8521
def independentCachedBranchMembers8523 : Finset ℕ := ([72,132,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8523 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8523 72 5
  · have he : independentCachedBranchMembers8523.erase 72=independentCachedBranchMembers8519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8519
  · have he : independentCachedBranchMembers8523.filter (independentCachedEdge 72)=independentCachedBranchMembers8522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8522
def independentCachedBranchMembers8524 : Finset ℕ := ([1582,1626,1628,1686,1690,1692,1762,1764,1768,2590,2666,2668,2726,2732,2772,2776,3102,3178,3180,3238,3242,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8524 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8524 5 (fun x => (if x<2668 then (if x<1692 then (if x<1628 then (if x<1626 then 0 else 0) else (if x<1686 then 1 else (if x<1690 then 0 else 1))) else (if x<1768 then (if x<1762 then 2 else (if x<1764 then 0 else 2)) else (if x<2590 then 1 else (if x<2666 then 0 else 0)))) else (if x<3178 then (if x<2772 then (if x<2726 then 1 else (if x<2732 then 0 else 2)) else (if x<2776 then 2 else (if x<3102 then 1 else 3))) else (if x<3242 then (if x<3180 then 3 else (if x<3238 then 4 else 3)) else (if x<3282 then 4 else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8525 : Finset ℕ := ([1626,1628,1686,1768,2666,2668,2726,2776,3178,3180,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8525 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8525 4 (fun x => (if x<2726 then (if x<1768 then (if x<1628 then 0 else (if x<1686 then 1 else 0)) else (if x<2666 then 1 else (if x<2668 then 0 else 1))) else (if x<3180 then (if x<2776 then 0 else (if x<3178 then 1 else 2)) else (if x<3238 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8526 : Finset ℕ := ([1582,1622,1626,1628,1686,1690,1692,1762,1764,1768,2590,2666,2668,2726,2732,2772,2776,3102,3178,3180,3238,3242,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8526 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8526 1622 4
  · have he : independentCachedBranchMembers8526.erase 1622=independentCachedBranchMembers8524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8524
  · have he : independentCachedBranchMembers8526.filter (independentCachedEdge 1622)=independentCachedBranchMembers8525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8525
def independentCachedBranchMembers8527 : Finset ℕ := ([48,72,132,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8527 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8527 48 5
  · have he : independentCachedBranchMembers8527.erase 48=independentCachedBranchMembers8523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8523
  · have he : independentCachedBranchMembers8527.filter (independentCachedEdge 48)=independentCachedBranchMembers8526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8526
def independentCachedBranchMembers8528 : Finset ℕ := ([1590,1596,1614,1628,1678,1686,1764,2590,2676,2732,2758,3102,3180,3188,3238,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8528 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8528 5 (fun x => (if x<2732 then (if x<1678 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1628 then 0 else 2)) else (if x<1764 then (if x<1686 then 1 else 2) else (if x<2590 then 0 else (if x<2676 then 0 else 1)))) else (if x<3188 then (if x<3102 then (if x<2758 then 1 else 1) else (if x<3180 then 2 else 2)) else (if x<3252 then (if x<3238 then 3 else 2) else (if x<3270 then 4 else (if x<3276 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8529 : Finset ℕ := ([1590,1596,1614,1678,2676,2758,3102,3180,3238] : List ℕ).toFinset
theorem independentCachedBranchBound8529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8529 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8529 4 (fun x => (if x<2676 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<3102 then (if x<2758 then 1 else 1) else (if x<3180 then 0 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8530 : Finset ℕ := ([1590,1596,1614,1628,1678,1686,1764,2590,2676,2732,2758,2772,3102,3180,3188,3238,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8530 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8530 2772 4
  · have he : independentCachedBranchMembers8530.erase 2772=independentCachedBranchMembers8528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8528
  · have he : independentCachedBranchMembers8530.filter (independentCachedEdge 2772)=independentCachedBranchMembers8529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8529
def independentCachedBranchMembers8531 : Finset ℕ := ([1596,1614,2732,2758,3102,3180,3188,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8531 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8531 4 (fun x => (if x<3102 then (if x<2732 then (if x<1614 then 0 else 0) else (if x<2758 then 1 else 0)) else (if x<3188 then (if x<3180 then 2 else 1) else (if x<3238 then 2 else (if x<3276 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8532 : Finset ℕ := ([1590,1596,1614,1628,1678,1686,1764,2590,2676,2726,2732,2758,2772,3102,3180,3188,3238,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8532 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8532 2726 4
  · have he : independentCachedBranchMembers8532.erase 2726=independentCachedBranchMembers8530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8530
  · have he : independentCachedBranchMembers8532.filter (independentCachedEdge 2726)=independentCachedBranchMembers8531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8531
def independentCachedBranchMembers8533 : Finset ℕ := ([1590,1678,2676,2732,3102,3180,3238,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8533 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8533 4 (fun x => (if x<3102 then (if x<2676 then (if x<1678 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<3238 then (if x<3180 then 2 else 1) else (if x<3252 then 1 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8534 : Finset ℕ := ([1590,1596,1614,1628,1678,1686,1764,2590,2668,2676,2726,2732,2758,2772,3102,3180,3188,3238,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8534 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8534 2668 4
  · have he : independentCachedBranchMembers8534.erase 2668=independentCachedBranchMembers8532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8532
  · have he : independentCachedBranchMembers8534.filter (independentCachedEdge 2668)=independentCachedBranchMembers8533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8533
def independentCachedBranchMembers8535 : Finset ℕ := ([1590,1614,1628,1686,2668,2726,3180,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8535 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8535 4 (fun x => (if x<2726 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1686 then 1 else (if x<2668 then 1 else 1))) else (if x<3238 then (if x<3180 then 1 else 2) else (if x<3252 then 2 else (if x<3276 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8536 : Finset ℕ := ([1590,1596,1614,1622,1628,1678,1686,1764,2590,2668,2676,2726,2732,2758,2772,3102,3180,3188,3238,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8536 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8536 1622 4
  · have he : independentCachedBranchMembers8536.erase 1622=independentCachedBranchMembers8534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8534
  · have he : independentCachedBranchMembers8536.filter (independentCachedEdge 1622)=independentCachedBranchMembers8535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8535
def independentCachedBranchMembers8537 : Finset ℕ := ([1590,1596,1614,1678,2676,2758,3188,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8537 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8537 4 (fun x => (if x<2758 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1678 then 0 else (if x<2676 then 1 else 1))) else (if x<3252 then (if x<3188 then 1 else 2) else (if x<3270 then 0 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8538 : Finset ℕ := ([1582,1590,1596,1614,1622,1628,1678,1686,1764,2590,2668,2676,2726,2732,2758,2772,3102,3180,3188,3238,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8538 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8538 1582 4
  · have he : independentCachedBranchMembers8538.erase 1582=independentCachedBranchMembers8536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8536
  · have he : independentCachedBranchMembers8538.filter (independentCachedEdge 1582)=independentCachedBranchMembers8537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8537
def independentCachedBranchMembers8539 : Finset ℕ := ([1596,1628,1678,1686,2668,2676,2726,2758,3180,3188,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8539 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8539 4 (fun x => (if x<2726 then (if x<1686 then (if x<1628 then 0 else (if x<1678 then 1 else 0)) else (if x<2668 then 1 else (if x<2676 then 1 else 0))) else (if x<3188 then (if x<2758 then 1 else (if x<3180 then 0 else 2)) else (if x<3238 then 3 else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8540 : Finset ℕ := ([1582,1590,1596,1614,1622,1628,1678,1686,1692,1764,2590,2668,2676,2726,2732,2758,2772,3102,3180,3188,3238,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8540 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8540 1692 4
  · have he : independentCachedBranchMembers8540.erase 1692=independentCachedBranchMembers8538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8538
  · have he : independentCachedBranchMembers8540.filter (independentCachedEdge 1692)=independentCachedBranchMembers8539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8539
def independentCachedBranchMembers8541 : Finset ℕ := ([1582,1590,1614,1622,1678,1686,2590,2726,2758,3102,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8541 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8541 4 (fun x => (if x<2590 then (if x<1622 then (if x<1590 then 0 else (if x<1614 then 1 else 1)) else (if x<1678 then 0 else (if x<1686 then 2 else 3))) else (if x<3102 then (if x<2726 then 0 else (if x<2758 then 2 else 3)) else (if x<3238 then 1 else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8542 : Finset ℕ := ([252,1582,1590,1596,1614,1622,1628,1678,1686,1692,1764,2590,2668,2676,2726,2732,2758,2772,3102,3180,3188,3238,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8542 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8542 252 4
  · have he : independentCachedBranchMembers8542.erase 252=independentCachedBranchMembers8540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8540
  · have he : independentCachedBranchMembers8542.filter (independentCachedEdge 252)=independentCachedBranchMembers8541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8541
def independentCachedBranchMembers8543 : Finset ℕ := ([1582,1590,1596,1614,1622,1628,2590,2668,2676,3102,3180,3188] : List ℕ).toFinset
theorem independentCachedBranchBound8543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8543 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8543 4 (fun x => (if x<2590 then (if x<1614 then (if x<1590 then 0 else (if x<1596 then 1 else 2)) else (if x<1622 then 1 else (if x<1628 then 0 else 3))) else (if x<3102 then (if x<2668 then 0 else (if x<2676 then 2 else 3)) else (if x<3180 then 1 else (if x<3188 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
