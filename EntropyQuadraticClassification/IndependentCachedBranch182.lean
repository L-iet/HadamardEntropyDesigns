/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch181
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8608 : Finset ℕ := ([40,80,132,252,1582,1596,1622,1626,1678,1692,1764,1768,2590,2666,2676,2680,2732,2738,2758,2772,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8608 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8608 40 4
  · have he : independentCachedBranchMembers8608.erase 40=independentCachedBranchMembers8606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8606
  · have he : independentCachedBranchMembers8608.filter (independentCachedEdge 40)=independentCachedBranchMembers8607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8607
def independentCachedBranchMembers8609 : Finset ℕ := ([40,80,132,252,1582,1622,1692,1764,2666,2676,2758,2776,3180,3186,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8609 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8609 4 (fun x => (if x<2666 then (if x<1582 then (if x<132 then (if x<80 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1622 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3180 then (if x<2758 then (if x<2676 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3238 then (if x<3186 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8610 : Finset ℕ := ([40,80,132,252,1582,1596,1622,1626,1678,1692,1764,1768,2590,2666,2676,2680,2732,2738,2758,2762,2772,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8610 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8610 2762 4
  · have he : independentCachedBranchMembers8610.erase 2762=independentCachedBranchMembers8608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8608
  · have he : independentCachedBranchMembers8610.filter (independentCachedEdge 2762)=independentCachedBranchMembers8609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8609
def independentCachedBranchMembers8611 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8611 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8611 3250 5
  · have he : independentCachedBranchMembers8611.erase 3250=independentCachedBranchMembers8599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8599
  · have he : independentCachedBranchMembers8611.filter (independentCachedEdge 3250)=independentCachedBranchMembers8610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8610
def independentCachedBranchMembers8612 : Finset ℕ := ([1590,1594,1614,1628,1686,1690,1762,1776,2590,2666,2676,2680,2732,2738,2758,2762,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8612 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8612 5 (fun x => (if x<2732 then (if x<1762 then (if x<1628 then (if x<1594 then 0 else (if x<1614 then 1 else 0)) else (if x<1686 then 1 else (if x<1690 then 1 else 0))) else (if x<2666 then (if x<1776 then 0 else (if x<2590 then 1 else 0)) else (if x<2676 then 2 else (if x<2680 then 2 else 1)))) else (if x<3186 then (if x<2762 then (if x<2738 then 2 else (if x<2758 then 0 else 2)) else (if x<2776 then 0 else (if x<3180 then 2 else 3))) else (if x<3252 then (if x<3238 then 3 else (if x<3242 then 3 else 4)) else (if x<3276 then (if x<3256 then 4 else 3) else (if x<3282 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8613 : Finset ℕ := ([1590,1614,1628,1686,2590,2676,2732,2758,3180,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8613 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8613 4 (fun x => (if x<2732 then (if x<1686 then (if x<1614 then 0 else (if x<1628 then 0 else 1)) else (if x<2590 then 1 else (if x<2676 then 0 else 2))) else (if x<3238 then (if x<2758 then 2 else (if x<3180 then 2 else 1)) else (if x<3252 then 1 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8614 : Finset ℕ := ([250,1590,1594,1614,1628,1686,1690,1762,1776,2590,2666,2676,2680,2732,2738,2758,2762,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8614 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8614 250 4
  · have he : independentCachedBranchMembers8614.erase 250=independentCachedBranchMembers8612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8612
  · have he : independentCachedBranchMembers8614.filter (independentCachedEdge 250)=independentCachedBranchMembers8613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8613
def independentCachedBranchMembers8615 : Finset ℕ := ([1590,1594,1614,1776,2590,2666,2732,2776,3186,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8615 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8615 4 (fun x => (if x<2732 then (if x<1776 then (if x<1594 then 0 else (if x<1614 then 1 else 0)) else (if x<2590 then 1 else (if x<2666 then 0 else 2))) else (if x<3252 then (if x<2776 then 2 else (if x<3186 then 2 else 1)) else (if x<3256 then 3 else (if x<3276 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8616 : Finset ℕ := ([130,250,1590,1594,1614,1628,1686,1690,1762,1776,2590,2666,2676,2680,2732,2738,2758,2762,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8616 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8616 130 4
  · have he : independentCachedBranchMembers8616.erase 130=independentCachedBranchMembers8614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8614
  · have he : independentCachedBranchMembers8616.filter (independentCachedEdge 130)=independentCachedBranchMembers8615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8615
def independentCachedBranchMembers8617 : Finset ℕ := ([1594,1690,1762,1776,2590,2676,2732,2758,3186,3242,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8617 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8617 4 (fun x => (if x<2732 then (if x<1776 then (if x<1690 then 0 else (if x<1762 then 1 else 0)) else (if x<2590 then 1 else (if x<2676 then 0 else 1))) else (if x<3242 then (if x<2758 then 2 else (if x<3186 then 0 else 2)) else (if x<3256 then 2 else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8618 : Finset ℕ := ([72,130,250,1590,1594,1614,1628,1686,1690,1762,1776,2590,2666,2676,2680,2732,2738,2758,2762,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8618 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8618 72 4
  · have he : independentCachedBranchMembers8618.erase 72=independentCachedBranchMembers8616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8616
  · have he : independentCachedBranchMembers8618.filter (independentCachedEdge 72)=independentCachedBranchMembers8617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8617
def independentCachedBranchMembers8619 : Finset ℕ := ([1628,1686,1690,1762,2590,2666,2732,2776,3180,3238,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8619 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8619 4 (fun x => (if x<2732 then (if x<1762 then (if x<1686 then 0 else (if x<1690 then 0 else 1)) else (if x<2590 then 1 else (if x<2666 then 0 else 2))) else (if x<3238 then (if x<2776 then 2 else (if x<3180 then 2 else 3)) else (if x<3242 then 3 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8620 : Finset ℕ := ([48,72,130,250,1590,1594,1614,1628,1686,1690,1762,1776,2590,2666,2676,2680,2732,2738,2758,2762,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8620 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8620 48 4
  · have he : independentCachedBranchMembers8620.erase 48=independentCachedBranchMembers8618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8618
  · have he : independentCachedBranchMembers8620.filter (independentCachedEdge 48)=independentCachedBranchMembers8619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8619
def independentCachedBranchMembers8621 : Finset ℕ := ([48,72,130,250,1590,1614,1690,1762,2666,2676,2758,2776,3180,3186,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8621 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8621 4 (fun x => (if x<2666 then (if x<1590 then (if x<130 then (if x<72 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1614 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3180 then (if x<2758 then (if x<2676 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3238 then (if x<3186 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8622 : Finset ℕ := ([48,72,130,250,1590,1594,1614,1628,1686,1690,1762,1776,2590,2666,2676,2680,2732,2738,2758,2762,2772,2776,3180,3186,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8622 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8622 2772 4
  · have he : independentCachedBranchMembers8622.erase 2772=independentCachedBranchMembers8620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8620
  · have he : independentCachedBranchMembers8622.filter (independentCachedEdge 2772)=independentCachedBranchMembers8621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8621
def independentCachedBranchMembers8623 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2744,2758,2762,2772,2776,3102,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8623 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8623 3244 5
  · have he : independentCachedBranchMembers8623.erase 3244=independentCachedBranchMembers8611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8611
  · have he : independentCachedBranchMembers8623.filter (independentCachedEdge 3244)=independentCachedBranchMembers8622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8622
def independentCachedBranchMembers8624 : Finset ℕ := ([1594,1596,1626,1628,1678,1686,1768,1776,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8624 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8624 5 (fun x => (if x<2738 then (if x<1686 then (if x<1626 then (if x<1596 then 0 else 1) else (if x<1628 then 1 else (if x<1678 then 0 else 0))) else (if x<1776 then (if x<1768 then 1 else 0) else (if x<2680 then 1 else (if x<2732 then 0 else 2)))) else (if x<3186 then (if x<2772 then (if x<2762 then 2 else 2) else (if x<3178 then 2 else (if x<3180 then 3 else 4))) else (if x<3256 then (if x<3188 then 4 else (if x<3238 then 3 else 3)) else (if x<3270 then 3 else (if x<3288 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8625 : Finset ℕ := ([1594,1626,1678,1686,2738,2762,3178,3186,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8625 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8625 4 (fun x => (if x<2762 then (if x<1678 then (if x<1626 then 0 else 1) else (if x<1686 then 0 else (if x<2738 then 1 else 2))) else (if x<3186 then (if x<3178 then 2 else 1) else (if x<3238 then 0 else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8626 : Finset ℕ := ([252,1594,1596,1626,1628,1678,1686,1768,1776,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8626 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8626 252 4
  · have he : independentCachedBranchMembers8626.erase 252=independentCachedBranchMembers8624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8624
  · have he : independentCachedBranchMembers8626.filter (independentCachedEdge 252)=independentCachedBranchMembers8625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8625
def independentCachedBranchMembers8627 : Finset ℕ := ([1596,1628,1768,1776,2738,2762,3180,3188,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8627 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8627 4 (fun x => (if x<2762 then (if x<1768 then (if x<1628 then 0 else 1) else (if x<1776 then 0 else (if x<2738 then 1 else 1))) else (if x<3188 then (if x<3180 then 0 else 2) else (if x<3256 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8628 : Finset ℕ := ([132,252,1594,1596,1626,1628,1678,1686,1768,1776,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8628 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8628 132 4
  · have he : independentCachedBranchMembers8628.erase 132=independentCachedBranchMembers8626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8626
  · have he : independentCachedBranchMembers8628.filter (independentCachedEdge 132)=independentCachedBranchMembers8627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8627
def independentCachedBranchMembers8629 : Finset ℕ := ([1594,1596,1678,1776,2732,2772,3186,3188,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8629 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8629 4 (fun x => (if x<2772 then (if x<1678 then (if x<1596 then 0 else 1) else (if x<1776 then 0 else (if x<2732 then 1 else 2))) else (if x<3188 then (if x<3186 then 2 else 0) else (if x<3256 then 1 else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8630 : Finset ℕ := ([72,132,252,1594,1596,1626,1628,1678,1686,1768,1776,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8630 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8630 72 4
  · have he : independentCachedBranchMembers8630.erase 72=independentCachedBranchMembers8628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8628
  · have he : independentCachedBranchMembers8630.filter (independentCachedEdge 72)=independentCachedBranchMembers8629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8629
def independentCachedBranchMembers8631 : Finset ℕ := ([1626,1628,1686,1768,2732,2772,3178,3180,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8631 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8631 4 (fun x => (if x<2772 then (if x<1686 then (if x<1628 then 0 else 1) else (if x<1768 then 0 else (if x<2732 then 1 else 2))) else (if x<3180 then (if x<3178 then 2 else 0) else (if x<3238 then 1 else (if x<3288 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8632 : Finset ℕ := ([48,72,132,252,1594,1596,1626,1628,1678,1686,1768,1776,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8632 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8632 48 4
  · have he : independentCachedBranchMembers8632.erase 48=independentCachedBranchMembers8630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8630
  · have he : independentCachedBranchMembers8632.filter (independentCachedEdge 48)=independentCachedBranchMembers8631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8631
def independentCachedBranchMembers8633 : Finset ℕ := ([132,252,1596,1628,1678,1686,2732,2772,3180,3188,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8633 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8633 4 (fun x => (if x<2732 then (if x<1628 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1678 then 2 else (if x<1686 then 1 else 2))) else (if x<3188 then (if x<2772 then 0 else (if x<3180 then 0 else 2)) else (if x<3238 then 1 else (if x<3270 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8634 : Finset ℕ := ([48,72,132,250,252,1594,1596,1626,1628,1678,1686,1768,1776,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8634 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8634 250 4
  · have he : independentCachedBranchMembers8634.erase 250=independentCachedBranchMembers8632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8632
  · have he : independentCachedBranchMembers8634.filter (independentCachedEdge 250)=independentCachedBranchMembers8633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8633
def independentCachedBranchMembers8635 : Finset ℕ := ([132,252,1594,1626,1768,1776,2732,2772,3178,3186,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8635 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8635 4 (fun x => (if x<2732 then (if x<1626 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1768 then 2 else (if x<1776 then 1 else 2))) else (if x<3186 then (if x<2772 then 0 else (if x<3178 then 0 else 1)) else (if x<3256 then 2 else (if x<3288 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8636 : Finset ℕ := ([48,72,130,132,250,252,1594,1596,1626,1628,1678,1686,1768,1776,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8636 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8636 130 4
  · have he : independentCachedBranchMembers8636.erase 130=independentCachedBranchMembers8634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8634
  · have he : independentCachedBranchMembers8636.filter (independentCachedEdge 130)=independentCachedBranchMembers8635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8635
def independentCachedBranchMembers8637 : Finset ℕ := ([48,72,1594,1596,1686,1768,2738,2762,3178,3180,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8637 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8637 4 (fun x => (if x<2738 then (if x<1596 then (if x<72 then 0 else (if x<1594 then 0 else 1)) else (if x<1686 then 2 else (if x<1768 then 1 else 2))) else (if x<3180 then (if x<2762 then 0 else (if x<3178 then 0 else 1)) else (if x<3256 then 2 else (if x<3270 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8638 : Finset ℕ := ([48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1768,1776,2680,2732,2738,2762,2772,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8638 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8638 80 4
  · have he : independentCachedBranchMembers8638.erase 80=independentCachedBranchMembers8636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8636
  · have he : independentCachedBranchMembers8638.filter (independentCachedEdge 80)=independentCachedBranchMembers8637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8637
def independentCachedBranchMembers8639 : Finset ℕ := ([48,72,1626,1628,1678,1776,2738,2762,3186,3188,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8639 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8639 4 (fun x => (if x<2738 then (if x<1628 then (if x<72 then 0 else (if x<1626 then 0 else 1)) else (if x<1678 then 2 else (if x<1776 then 1 else 2))) else (if x<3188 then (if x<2762 then 0 else (if x<3186 then 0 else 1)) else (if x<3238 then 2 else (if x<3288 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
