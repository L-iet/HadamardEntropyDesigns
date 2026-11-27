/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch183
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8672 : Finset ℕ := ([80,130,250,1582,1594,1622,1628,1678,1690,1762,1768,2666,2676,2726,2732,2738,2744,2762,2772,3102,3180,3186,3192,3242,3252,3270,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8672 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8672 80 4
  · have he : independentCachedBranchMembers8672.erase 80=independentCachedBranchMembers8670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8670
  · have he : independentCachedBranchMembers8672.filter (independentCachedEdge 80)=independentCachedBranchMembers8671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8671
def independentCachedBranchMembers8673 : Finset ℕ := ([1628,1678,1690,1762,2676,2726,2738,2762,3102,3186,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8673 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8673 4 (fun x => (if x<2738 then (if x<1762 then (if x<1678 then 0 else (if x<1690 then 0 else 1)) else (if x<2676 then 1 else (if x<2726 then 0 else 0))) else (if x<3186 then (if x<2762 then 1 else (if x<3102 then 1 else 2)) else (if x<3252 then 2 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8674 : Finset ℕ := ([40,80,130,250,1582,1594,1622,1628,1678,1690,1762,1768,2666,2676,2726,2732,2738,2744,2762,2772,3102,3180,3186,3192,3242,3252,3270,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8674 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8674 40 4
  · have he : independentCachedBranchMembers8674.erase 40=independentCachedBranchMembers8672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8672
  · have he : independentCachedBranchMembers8674.filter (independentCachedEdge 40)=independentCachedBranchMembers8673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8673
def independentCachedBranchMembers8675 : Finset ℕ := ([40,80,130,250,1582,1622,1690,1762,2666,2676,2726,2744,3180,3186,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8675 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8675 4 (fun x => (if x<2666 then (if x<1582 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3180 then (if x<2726 then (if x<2676 then 2 else 2) else (if x<2744 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8676 : Finset ℕ := ([40,80,130,250,1582,1594,1622,1628,1678,1690,1762,1768,2666,2676,2726,2732,2738,2744,2762,2772,3102,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8676 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8676 3276 4
  · have he : independentCachedBranchMembers8676.erase 3276=independentCachedBranchMembers8674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8674
  · have he : independentCachedBranchMembers8676.filter (independentCachedEdge 3276)=independentCachedBranchMembers8675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8675
def independentCachedBranchMembers8677 : Finset ℕ := ([40,80,130,250,1594,1628,1678,1768,2732,2738,2762,2772,3180,3186,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8677 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8677 4 (fun x => (if x<2732 then (if x<1594 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3180 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8678 : Finset ℕ := ([40,80,130,250,1582,1594,1622,1628,1678,1690,1762,1768,2666,2676,2726,2732,2738,2744,2762,2772,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8678 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8678 3174 4
  · have he : independentCachedBranchMembers8678.erase 3174=independentCachedBranchMembers8676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8676
  · have he : independentCachedBranchMembers8678.filter (independentCachedEdge 3174)=independentCachedBranchMembers8677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8677
def independentCachedBranchMembers8679 : Finset ℕ := ([1582,1594,1622,1628,1678,1690,1762,1768,2666,2676,2726,2732,2738,2744,2762,2772] : List ℕ).toFinset
theorem independentCachedBranchBound8679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8679 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8679 4 (fun x => (if x<2666 then (if x<1678 then (if x<1622 then (if x<1594 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1762 then (if x<1690 then 1 else 0) else (if x<1768 then 0 else 1))) else (if x<2738 then (if x<2726 then (if x<2676 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2762 then (if x<2744 then 3 else 2) else (if x<2772 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8680 : Finset ℕ := ([40,80,130,250,1582,1594,1622,1628,1678,1690,1762,1768,2666,2676,2726,2732,2738,2744,2762,2772,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8680 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8680 3072 4
  · have he : independentCachedBranchMembers8680.erase 3072=independentCachedBranchMembers8678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8678
  · have he : independentCachedBranchMembers8680.filter (independentCachedEdge 3072)=independentCachedBranchMembers8679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8679
def independentCachedBranchMembers8681 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8681 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8681 2740 5
  · have he : independentCachedBranchMembers8681.erase 2740=independentCachedBranchMembers8669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8669
  · have he : independentCachedBranchMembers8681.filter (independentCachedEdge 2740)=independentCachedBranchMembers8680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8680
def independentCachedBranchMembers8682 : Finset ℕ := ([72,252,1582,1596,1614,1626,1628,1690,1692,1768,2590,2666,2668,2680,2732,2744,2762,2776,3102,3178,3180,3192,3242,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8682 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8682 5 (fun x => (if x<2680 then (if x<1628 then (if x<1596 then (if x<252 then 0 else (if x<1582 then 0 else 1)) else (if x<1614 then 2 else (if x<1626 then 2 else 1))) else (if x<1768 then (if x<1690 then 0 else (if x<1692 then 2 else 1)) else (if x<2666 then (if x<2590 then 0 else 1) else (if x<2668 then 1 else 0)))) else (if x<3178 then (if x<2762 then (if x<2732 then 3 else (if x<2744 then 1 else 2)) else (if x<2776 then 2 else (if x<3102 then 0 else 4))) else (if x<3242 then (if x<3180 then 3 else (if x<3192 then 4 else 0)) else (if x<3276 then (if x<3256 then 4 else 3) else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8683 : Finset ℕ := ([72,252,1582,1596,1626,1690,2668,2732,2762,2776,3180,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8683 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8683 4 (fun x => (if x<2668 then (if x<1596 then (if x<252 then 0 else (if x<1582 then 0 else 1)) else (if x<1626 then 2 else (if x<1690 then 1 else 2))) else (if x<2776 then (if x<2732 then 0 else (if x<2762 then 1 else 2)) else (if x<3180 then 0 else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8684 : Finset ℕ := ([72,252,1582,1594,1596,1614,1626,1628,1690,1692,1768,2590,2666,2668,2680,2732,2744,2762,2776,3102,3178,3180,3192,3242,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8684 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8684 1594 4
  · have he : independentCachedBranchMembers8684.erase 1594=independentCachedBranchMembers8682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8682
  · have he : independentCachedBranchMembers8684.filter (independentCachedEdge 1594)=independentCachedBranchMembers8683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8683
def independentCachedBranchMembers8685 : Finset ℕ := ([252,1582,1596,1614,1628,1692,2590,2668,2732,3102,3180,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8685 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8685 4 (fun x => (if x<2590 then (if x<1614 then (if x<1582 then 0 else (if x<1596 then 1 else 0)) else (if x<1628 then 2 else (if x<1692 then 1 else 2))) else (if x<3102 then (if x<2668 then 1 else (if x<2732 then 0 else 3)) else (if x<3180 then 2 else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8686 : Finset ℕ := ([72,250,252,1582,1594,1596,1614,1626,1628,1690,1692,1768,2590,2666,2668,2680,2732,2744,2762,2776,3102,3178,3180,3192,3242,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8686 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8686 250 4
  · have he : independentCachedBranchMembers8686.erase 250=independentCachedBranchMembers8684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8684
  · have he : independentCachedBranchMembers8686.filter (independentCachedEdge 250)=independentCachedBranchMembers8685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8685
def independentCachedBranchMembers8687 : Finset ℕ := ([72,1614,1626,1628,1690,1692,2590,2762,2776,3102,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8687 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8687 4 (fun x => (if x<2590 then (if x<1628 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<1690 then 2 else (if x<1692 then 2 else 1))) else (if x<3102 then (if x<2762 then 1 else (if x<2776 then 0 else 1)) else (if x<3276 then 2 else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8688 : Finset ℕ := ([40,72,250,252,1582,1594,1596,1614,1626,1628,1690,1692,1768,2590,2666,2668,2680,2732,2744,2762,2776,3102,3178,3180,3192,3242,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8688 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8688 40 4
  · have he : independentCachedBranchMembers8688.erase 40=independentCachedBranchMembers8686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8686
  · have he : independentCachedBranchMembers8688.filter (independentCachedEdge 40)=independentCachedBranchMembers8687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8687
def independentCachedBranchMembers8689 : Finset ℕ := ([252,1582,1594,1628,1692,2590,2668,2680,2732,2744,2762,3178,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8689 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8689 4 (fun x => (if x<2680 then (if x<1628 then (if x<1582 then 0 else (if x<1594 then 1 else 2)) else (if x<2590 then (if x<1692 then 0 else 1) else (if x<2668 then 1 else 0))) else (if x<3178 then (if x<2744 then (if x<2732 then 2 else 1) else (if x<2762 then 3 else 3)) else (if x<3276 then (if x<3242 then 2 else 3) else (if x<3288 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8690 : Finset ℕ := ([1628,1692,2590,2762,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8690 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8690 3 (fun x => (if x<2762 then (if x<1692 then 0 else (if x<2590 then 1 else 0)) else (if x<3276 then 2 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8691 : Finset ℕ := ([40,252,1582,1594,1628,1692,2590,2668,2680,2732,2744,2762,3178,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8691 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8691 40 3
  · have he : independentCachedBranchMembers8691.erase 40=independentCachedBranchMembers8689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8689
  · have he : independentCachedBranchMembers8691.filter (independentCachedEdge 40)=independentCachedBranchMembers8690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8690
def independentCachedBranchMembers8692 : Finset ℕ := ([40,72,250,252,1582,1594,1596,1614,1626,1628,1690,1692,1768,2590,2666,2668,2680,2732,2744,2762,2776,3102,3178,3180,3192,3242,3256,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8692 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8692 3274 4
  · have he : independentCachedBranchMembers8692.erase 3274=independentCachedBranchMembers8688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8688
  · have he : independentCachedBranchMembers8692.filter (independentCachedEdge 3274)=independentCachedBranchMembers8691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8691
def independentCachedBranchMembers8693 : Finset ℕ := ([250,1594,1614,1628,1690,2590,2666,2680,2732,2762,2776,3180,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8693 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8693 4 (fun x => (if x<2680 then (if x<1628 then (if x<1594 then 0 else (if x<1614 then 0 else 1)) else (if x<2590 then (if x<1690 then 2 else 1) else (if x<2666 then 1 else 0))) else (if x<3180 then (if x<2762 then (if x<2732 then 2 else 3) else (if x<2776 then 1 else 3)) else (if x<3256 then (if x<3242 then 2 else 0) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8694 : Finset ℕ := ([1594,1690,2590,2732,3242,3256] : List ℕ).toFinset
theorem independentCachedBranchBound8694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8694 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8694 3 (fun x => (if x<2732 then (if x<1690 then 0 else (if x<2590 then 1 else 0)) else (if x<3242 then 2 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8695 : Finset ℕ := ([72,250,1594,1614,1628,1690,2590,2666,2680,2732,2762,2776,3180,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8695 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8695 72 3
  · have he : independentCachedBranchMembers8695.erase 72=independentCachedBranchMembers8693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8693
  · have he : independentCachedBranchMembers8695.filter (independentCachedEdge 72)=independentCachedBranchMembers8694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8694
def independentCachedBranchMembers8696 : Finset ℕ := ([40,72,250,252,1582,1594,1596,1614,1626,1628,1690,1692,1768,2590,2666,2668,2680,2732,2744,2762,2776,3102,3178,3180,3192,3242,3244,3256,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8696 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8696 3244 4
  · have he : independentCachedBranchMembers8696.erase 3244=independentCachedBranchMembers8692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8692
  · have he : independentCachedBranchMembers8696.filter (independentCachedEdge 3244)=independentCachedBranchMembers8695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8695
def independentCachedBranchMembers8697 : Finset ℕ := ([40,72,250,252,1582,1614,1690,1692,2666,2668,2744,2776,3178,3180,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8697 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8697 4 (fun x => (if x<2666 then (if x<1582 then (if x<250 then (if x<72 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1690 then (if x<1614 then 2 else 3) else (if x<1692 then 2 else 3))) else (if x<3178 then (if x<2744 then (if x<2668 then 0 else 1) else (if x<2776 then 0 else 1)) else (if x<3256 then (if x<3180 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8698 : Finset ℕ := ([40,72,250,252,1582,1594,1596,1614,1626,1628,1678,1690,1692,1768,2590,2666,2668,2680,2732,2744,2762,2776,3102,3178,3180,3192,3242,3244,3256,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8698 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8698 1678 4
  · have he : independentCachedBranchMembers8698.erase 1678=independentCachedBranchMembers8696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8696
  · have he : independentCachedBranchMembers8698.filter (independentCachedEdge 1678)=independentCachedBranchMembers8697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8697
def independentCachedBranchMembers8699 : Finset ℕ := ([40,48,72,80,130,132,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8699 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8699 246 5
  · have he : independentCachedBranchMembers8699.erase 246=independentCachedBranchMembers8681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8681
  · have he : independentCachedBranchMembers8699.filter (independentCachedEdge 246)=independentCachedBranchMembers8698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8698
def independentCachedBranchMembers8700 : Finset ℕ := ([80,132,1590,1594,1622,1626,1628,1678,1762,1764,2590,2674,2680,2726,2732,2762,3102,3186,3188,3192,3238,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8700 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8700 5 (fun x => (if x<2680 then (if x<1628 then (if x<1594 then (if x<132 then 0 else (if x<1590 then 0 else 1)) else (if x<1622 then 2 else (if x<1626 then 2 else 0))) else (if x<1764 then (if x<1678 then 1 else (if x<1762 then 0 else 2)) else (if x<2590 then 1 else (if x<2674 then 1 else 0)))) else (if x<3188 then (if x<2762 then (if x<2726 then 3 else (if x<2732 then 0 else 3)) else (if x<3102 then 3 else (if x<3186 then 2 else 2))) else (if x<3242 then (if x<3192 then 4 else (if x<3238 then 0 else 4)) else (if x<3270 then 2 else (if x<3276 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8701 : Finset ℕ := ([80,1590,1626,1628,2680,2726,2762,3102,3186,3188,3242,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8701 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8701 4 (fun x => (if x<2762 then (if x<1628 then (if x<1590 then 0 else (if x<1626 then 1 else 0)) else (if x<2680 then 1 else (if x<2726 then 0 else 1))) else (if x<3188 then (if x<3102 then 2 else (if x<3186 then 3 else 0)) else (if x<3242 then 2 else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8702 : Finset ℕ := ([80,132,1590,1594,1622,1626,1628,1678,1762,1764,2590,2674,2680,2726,2732,2758,2762,3102,3186,3188,3192,3238,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8702 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8702 2758 4
  · have he : independentCachedBranchMembers8702.erase 2758=independentCachedBranchMembers8700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8700
  · have he : independentCachedBranchMembers8702.filter (independentCachedEdge 2758)=independentCachedBranchMembers8701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8701
def independentCachedBranchMembers8703 : Finset ℕ := ([132,1594,1626,1762,2674,2680,2762,3102,3188,3238,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8703 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8703 4 (fun x => (if x<2762 then (if x<1762 then (if x<1594 then 0 else (if x<1626 then 0 else 1)) else (if x<2674 then 1 else (if x<2680 then 0 else 2))) else (if x<3238 then (if x<3102 then 1 else (if x<3188 then 3 else 2)) else (if x<3270 then 2 else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
