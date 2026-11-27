/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch180
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8576 : Finset ℕ := ([1590,1596,1614,1626,1678,1690,1762,1768,2590,2668,2674,2680,2726,2738,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8576 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8576 5 (fun x => (if x<2726 then (if x<1762 then (if x<1626 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1678 then 1 else (if x<1690 then 1 else 0))) else (if x<2668 then (if x<1768 then 0 else (if x<2590 then 1 else 0)) else (if x<2674 then 2 else (if x<2680 then 2 else 1)))) else (if x<3188 then (if x<2762 then (if x<2738 then 2 else (if x<2744 then 0 else 2)) else (if x<2772 then 0 else (if x<3178 then 2 else 3))) else (if x<3270 then (if x<3242 then 3 else (if x<3252 then 4 else 4)) else (if x<3282 then (if x<3276 then 3 else 4) else (if x<3288 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8577 : Finset ℕ := ([1590,1596,1614,1678,2590,2668,2726,2772,3188,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8577 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8577 4 (fun x => (if x<2726 then (if x<1678 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<2590 then 1 else (if x<2668 then 0 else 2))) else (if x<3252 then (if x<2772 then 2 else (if x<3188 then 2 else 1)) else (if x<3270 then 3 else (if x<3276 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8578 : Finset ℕ := ([250,1590,1596,1614,1626,1678,1690,1762,1768,2590,2668,2674,2680,2726,2738,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8578 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8578 250 4
  · have he : independentCachedBranchMembers8578.erase 250=independentCachedBranchMembers8576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8576
  · have he : independentCachedBranchMembers8578.filter (independentCachedEdge 250)=independentCachedBranchMembers8577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8577
def independentCachedBranchMembers8579 : Finset ℕ := ([1590,1614,1626,1768,2590,2674,2744,2772,3178,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8579 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8579 4 (fun x => (if x<2744 then (if x<1768 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<2590 then 1 else (if x<2674 then 0 else 2))) else (if x<3252 then (if x<2772 then 2 else (if x<3178 then 2 else 1)) else (if x<3276 then 3 else (if x<3288 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8580 : Finset ℕ := ([130,250,1590,1596,1614,1626,1678,1690,1762,1768,2590,2668,2674,2680,2726,2738,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8580 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8580 130 4
  · have he : independentCachedBranchMembers8580.erase 130=independentCachedBranchMembers8578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8578
  · have he : independentCachedBranchMembers8580.filter (independentCachedEdge 130)=independentCachedBranchMembers8579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8579
def independentCachedBranchMembers8581 : Finset ℕ := ([1596,1678,1690,1762,2590,2674,2744,2772,3188,3242,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8581 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8581 4 (fun x => (if x<2744 then (if x<1762 then (if x<1678 then 0 else (if x<1690 then 0 else 1)) else (if x<2590 then 1 else (if x<2674 then 0 else 2))) else (if x<3242 then (if x<2772 then 2 else (if x<3188 then 2 else 3)) else (if x<3270 then 1 else (if x<3282 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8582 : Finset ℕ := ([72,130,250,1590,1596,1614,1626,1678,1690,1762,1768,2590,2668,2674,2680,2726,2738,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8582 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8582 72 4
  · have he : independentCachedBranchMembers8582.erase 72=independentCachedBranchMembers8580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8580
  · have he : independentCachedBranchMembers8582.filter (independentCachedEdge 72)=independentCachedBranchMembers8581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8581
def independentCachedBranchMembers8583 : Finset ℕ := ([1626,1690,1762,1768,2590,2668,2726,2772,3178,3242,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8583 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8583 4 (fun x => (if x<2726 then (if x<1768 then (if x<1690 then 0 else (if x<1762 then 1 else 0)) else (if x<2590 then 1 else (if x<2668 then 0 else 1))) else (if x<3242 then (if x<2772 then 0 else (if x<3178 then 2 else 2)) else (if x<3282 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8584 : Finset ℕ := ([48,72,130,250,1590,1596,1614,1626,1678,1690,1762,1768,2590,2668,2674,2680,2726,2738,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8584 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8584 48 4
  · have he : independentCachedBranchMembers8584.erase 48=independentCachedBranchMembers8582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8582
  · have he : independentCachedBranchMembers8584.filter (independentCachedEdge 48)=independentCachedBranchMembers8583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8583
def independentCachedBranchMembers8585 : Finset ℕ := ([48,72,130,250,1590,1614,1690,1762,2668,2674,2726,2744,3178,3188,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8585 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8585 4 (fun x => (if x<2668 then (if x<1590 then (if x<130 then (if x<72 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1614 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3178 then (if x<2726 then (if x<2674 then 2 else 2) else (if x<2744 then 2 else 2)) else (if x<3270 then (if x<3188 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8586 : Finset ℕ := ([48,72,130,250,1590,1596,1614,1626,1678,1690,1762,1768,2590,2668,2674,2680,2726,2732,2738,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8586 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8586 2732 4
  · have he : independentCachedBranchMembers8586.erase 2732=independentCachedBranchMembers8584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8584
  · have he : independentCachedBranchMembers8586.filter (independentCachedEdge 2732)=independentCachedBranchMembers8585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8585
def independentCachedBranchMembers8587 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8587 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8587 3284 5
  · have he : independentCachedBranchMembers8587.erase 3284=independentCachedBranchMembers8575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8575
  · have he : independentCachedBranchMembers8587.filter (independentCachedEdge 3284)=independentCachedBranchMembers8586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8586
def independentCachedBranchMembers8588 : Finset ℕ := ([1582,1594,1622,1628,1686,1692,1764,1776,2590,2668,2674,2680,2726,2732,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8588 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8588 5 (fun x => (if x<2726 then (if x<1764 then (if x<1628 then (if x<1594 then 0 else (if x<1622 then 1 else 0)) else (if x<1686 then 1 else (if x<1692 then 1 else 0))) else (if x<2668 then (if x<1776 then 0 else (if x<2590 then 1 else 0)) else (if x<2674 then 2 else (if x<2680 then 2 else 1)))) else (if x<3188 then (if x<2762 then (if x<2732 then 2 else (if x<2744 then 0 else 2)) else (if x<2772 then 2 else (if x<3178 then 0 else 3))) else (if x<3270 then (if x<3242 then 3 else (if x<3252 then 4 else 4)) else (if x<3282 then (if x<3276 then 3 else 4) else (if x<3288 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8589 : Finset ℕ := ([1582,1594,1622,1686,2590,2674,2726,2762,3178,3242,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8589 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8589 4 (fun x => (if x<2726 then (if x<1686 then (if x<1594 then 0 else (if x<1622 then 1 else 0)) else (if x<2590 then 1 else (if x<2674 then 0 else 2))) else (if x<3242 then (if x<2762 then 2 else (if x<3178 then 2 else 1)) else (if x<3270 then 3 else (if x<3282 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8590 : Finset ℕ := ([252,1582,1594,1622,1628,1686,1692,1764,1776,2590,2668,2674,2680,2726,2732,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8590 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8590 252 4
  · have he : independentCachedBranchMembers8590.erase 252=independentCachedBranchMembers8588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8588
  · have he : independentCachedBranchMembers8590.filter (independentCachedEdge 252)=independentCachedBranchMembers8589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8589
def independentCachedBranchMembers8591 : Finset ℕ := ([1582,1622,1628,1776,2590,2668,2744,2762,3188,3242,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8591 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8591 4 (fun x => (if x<2744 then (if x<1776 then (if x<1622 then 0 else (if x<1628 then 0 else 1)) else (if x<2590 then 1 else (if x<2668 then 0 else 2))) else (if x<3242 then (if x<2762 then 2 else (if x<3188 then 2 else 1)) else (if x<3282 then 3 else (if x<3288 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8592 : Finset ℕ := ([132,252,1582,1594,1622,1628,1686,1692,1764,1776,2590,2668,2674,2680,2726,2732,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8592 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8592 132 4
  · have he : independentCachedBranchMembers8592.erase 132=independentCachedBranchMembers8590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8590
  · have he : independentCachedBranchMembers8592.filter (independentCachedEdge 132)=independentCachedBranchMembers8591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8591
def independentCachedBranchMembers8593 : Finset ℕ := ([1594,1686,1692,1764,2590,2668,2744,2762,3178,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8593 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8593 4 (fun x => (if x<2744 then (if x<1764 then (if x<1686 then 0 else (if x<1692 then 0 else 1)) else (if x<2590 then 1 else (if x<2668 then 0 else 2))) else (if x<3252 then (if x<2762 then 2 else (if x<3178 then 2 else 3)) else (if x<3270 then 1 else (if x<3276 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8594 : Finset ℕ := ([80,132,252,1582,1594,1622,1628,1686,1692,1764,1776,2590,2668,2674,2680,2726,2732,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8594 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8594 80 4
  · have he : independentCachedBranchMembers8594.erase 80=independentCachedBranchMembers8592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8592
  · have he : independentCachedBranchMembers8594.filter (independentCachedEdge 80)=independentCachedBranchMembers8593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8593
def independentCachedBranchMembers8595 : Finset ℕ := ([1628,1692,1764,1776,2590,2674,2726,2762,3188,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8595 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8595 4 (fun x => (if x<2726 then (if x<1776 then (if x<1692 then 0 else (if x<1764 then 1 else 0)) else (if x<2590 then 1 else (if x<2674 then 0 else 1))) else (if x<3252 then (if x<2762 then 0 else (if x<3188 then 2 else 2)) else (if x<3276 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8596 : Finset ℕ := ([40,80,132,252,1582,1594,1622,1628,1686,1692,1764,1776,2590,2668,2674,2680,2726,2732,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8596 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8596 40 4
  · have he : independentCachedBranchMembers8596.erase 40=independentCachedBranchMembers8594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8594
  · have he : independentCachedBranchMembers8596.filter (independentCachedEdge 40)=independentCachedBranchMembers8595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8595
def independentCachedBranchMembers8597 : Finset ℕ := ([40,80,132,252,1582,1622,1692,1764,2668,2674,2726,2744,3178,3188,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8597 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8597 4 (fun x => (if x<2668 then (if x<1582 then (if x<132 then (if x<80 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1622 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3178 then (if x<2726 then (if x<2674 then 2 else 2) else (if x<2744 then 2 else 2)) else (if x<3270 then (if x<3188 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8598 : Finset ℕ := ([40,80,132,252,1582,1594,1622,1628,1686,1692,1764,1776,2590,2668,2674,2680,2726,2732,2738,2744,2762,2772,3178,3188,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8598 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8598 2738 4
  · have he : independentCachedBranchMembers8598.erase 2738=independentCachedBranchMembers8596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8596
  · have he : independentCachedBranchMembers8598.filter (independentCachedEdge 2738)=independentCachedBranchMembers8597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8597
def independentCachedBranchMembers8599 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8599 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8599 3274 5
  · have he : independentCachedBranchMembers8599.erase 3274=independentCachedBranchMembers8587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8587
  · have he : independentCachedBranchMembers8599.filter (independentCachedEdge 3274)=independentCachedBranchMembers8598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8598
def independentCachedBranchMembers8600 : Finset ℕ := ([1582,1596,1622,1626,1678,1692,1764,1768,2590,2666,2676,2680,2732,2738,2758,2772,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8600 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8600 5 (fun x => (if x<2732 then (if x<1764 then (if x<1626 then (if x<1596 then 0 else (if x<1622 then 1 else 0)) else (if x<1678 then 1 else (if x<1692 then 1 else 0))) else (if x<2666 then (if x<1768 then 0 else (if x<2590 then 1 else 0)) else (if x<2676 then 2 else (if x<2680 then 2 else 1)))) else (if x<3186 then (if x<2772 then (if x<2738 then 0 else (if x<2758 then 2 else 2)) else (if x<2776 then 0 else (if x<3180 then 2 else 3))) else (if x<3252 then (if x<3238 then 3 else (if x<3242 then 3 else 4)) else (if x<3276 then (if x<3256 then 4 else 3) else (if x<3282 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8601 : Finset ℕ := ([1582,1622,1626,1678,2590,2666,2738,2758,3186,3238,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8601 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8601 4 (fun x => (if x<2738 then (if x<1678 then (if x<1622 then 0 else (if x<1626 then 0 else 1)) else (if x<2590 then 1 else (if x<2666 then 0 else 2))) else (if x<3238 then (if x<2758 then 2 else (if x<3186 then 2 else 1)) else (if x<3242 then 1 else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8602 : Finset ℕ := ([252,1582,1596,1622,1626,1678,1692,1764,1768,2590,2666,2676,2680,2732,2738,2758,2772,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8602 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8602 252 4
  · have he : independentCachedBranchMembers8602.erase 252=independentCachedBranchMembers8600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8600
  · have he : independentCachedBranchMembers8602.filter (independentCachedEdge 252)=independentCachedBranchMembers8601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8601
def independentCachedBranchMembers8603 : Finset ℕ := ([1582,1596,1622,1768,2590,2676,2738,2776,3180,3242,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8603 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8603 4 (fun x => (if x<2738 then (if x<1768 then (if x<1596 then 0 else (if x<1622 then 1 else 0)) else (if x<2590 then 1 else (if x<2676 then 0 else 2))) else (if x<3242 then (if x<2776 then 2 else (if x<3180 then 2 else 1)) else (if x<3256 then 3 else (if x<3282 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8604 : Finset ℕ := ([132,252,1582,1596,1622,1626,1678,1692,1764,1768,2590,2666,2676,2680,2732,2738,2758,2772,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8604 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8604 132 4
  · have he : independentCachedBranchMembers8604.erase 132=independentCachedBranchMembers8602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8602
  · have he : independentCachedBranchMembers8604.filter (independentCachedEdge 132)=independentCachedBranchMembers8603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8603
def independentCachedBranchMembers8605 : Finset ℕ := ([1596,1692,1764,1768,2590,2666,2738,2758,3180,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8605 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8605 4 (fun x => (if x<2738 then (if x<1768 then (if x<1692 then 0 else (if x<1764 then 1 else 0)) else (if x<2590 then 1 else (if x<2666 then 0 else 1))) else (if x<3252 then (if x<2758 then 2 else (if x<3180 then 0 else 2)) else (if x<3256 then 2 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8606 : Finset ℕ := ([80,132,252,1582,1596,1622,1626,1678,1692,1764,1768,2590,2666,2676,2680,2732,2738,2758,2772,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8606 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8606 80 4
  · have he : independentCachedBranchMembers8606.erase 80=independentCachedBranchMembers8604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8604
  · have he : independentCachedBranchMembers8606.filter (independentCachedEdge 80)=independentCachedBranchMembers8605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8605
def independentCachedBranchMembers8607 : Finset ℕ := ([1626,1678,1692,1764,2590,2676,2738,2776,3186,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8607 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8607 4 (fun x => (if x<2738 then (if x<1764 then (if x<1678 then 0 else (if x<1692 then 0 else 1)) else (if x<2590 then 1 else (if x<2676 then 0 else 2))) else (if x<3238 then (if x<2776 then 2 else (if x<3186 then 2 else 3)) else (if x<3252 then 3 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
