/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch187
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8800 : Finset ℕ := ([72,132,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8800 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8800 72 4
  · have he : independentCachedBranchMembers8800.erase 72=independentCachedBranchMembers8798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8798
  · have he : independentCachedBranchMembers8800.filter (independentCachedEdge 72)=independentCachedBranchMembers8799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8799
def independentCachedBranchMembers8801 : Finset ℕ := ([1626,1628,1686,1768,2666,2668,2726,2776,3102,3174,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8801 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8801 4 (fun x => (if x<2726 then (if x<1768 then (if x<1628 then 0 else (if x<1686 then 1 else 0)) else (if x<2666 then 1 else (if x<2668 then 0 else 1))) else (if x<3174 then (if x<2776 then 0 else (if x<3102 then 1 else 2)) else (if x<3244 then 2 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8802 : Finset ℕ := ([48,72,132,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8802 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8802 48 4
  · have he : independentCachedBranchMembers8802.erase 48=independentCachedBranchMembers8800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8800
  · have he : independentCachedBranchMembers8802.filter (independentCachedEdge 48)=independentCachedBranchMembers8801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8801
def independentCachedBranchMembers8803 : Finset ℕ := ([48,72,132,252,1594,1628,1678,1768,2666,2676,2726,2744,3244,3250,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8803 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8803 4 (fun x => (if x<2666 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1628 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3244 then (if x<2726 then (if x<2676 then 2 else 2) else (if x<2744 then 2 else 2)) else (if x<3274 then (if x<3250 then 3 else 3) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8804 : Finset ℕ := ([48,72,132,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3102,3174,3192,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8804 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8804 3282 4
  · have he : independentCachedBranchMembers8804.erase 3282=independentCachedBranchMembers8802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8802
  · have he : independentCachedBranchMembers8804.filter (independentCachedEdge 3282)=independentCachedBranchMembers8803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8803
def independentCachedBranchMembers8805 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1776,2668,2674,2758,2776,3244,3250,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8805 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8805 4 (fun x => (if x<2668 then (if x<1596 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3244 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3274 then (if x<3250 then 3 else 3) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8806 : Finset ℕ := ([48,72,132,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8806 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8806 3242 4
  · have he : independentCachedBranchMembers8806.erase 3242=independentCachedBranchMembers8804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8804
  · have he : independentCachedBranchMembers8806.filter (independentCachedEdge 3242)=independentCachedBranchMembers8805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8805
def independentCachedBranchMembers8807 : Finset ℕ := ([1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776] : List ℕ).toFinset
theorem independentCachedBranchBound8807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8807 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8807 4 (fun x => (if x<2666 then (if x<1678 then (if x<1626 then (if x<1596 then 0 else 1) else (if x<1628 then 1 else 0)) else (if x<1768 then (if x<1686 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<2726 then (if x<2674 then (if x<2668 then 2 else 3) else (if x<2676 then 3 else 2)) else (if x<2758 then (if x<2744 then 2 else 2) else (if x<2776 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8808 : Finset ℕ := ([48,72,132,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8808 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8808 3072 4
  · have he : independentCachedBranchMembers8808.erase 3072=independentCachedBranchMembers8806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8806
  · have he : independentCachedBranchMembers8808.filter (independentCachedEdge 3072)=independentCachedBranchMembers8807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8807
def independentCachedBranchMembers8809 : Finset ℕ := ([132,252,1596,1628,1678,1686,2668,2676,2726,2758,3102,3174,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8809 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8809 4 (fun x => (if x<2726 then (if x<1678 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1628 then 1 else 2)) else (if x<2668 then (if x<1686 then 1 else 2) else (if x<2676 then 2 else 1))) else (if x<3244 then (if x<3102 then (if x<2758 then 2 else 1) else (if x<3174 then 3 else 3)) else (if x<3276 then (if x<3252 then 0 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8810 : Finset ℕ := ([48,72,132,250,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8810 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8810 250 4
  · have he : independentCachedBranchMembers8810.erase 250=independentCachedBranchMembers8808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8808
  · have he : independentCachedBranchMembers8810.filter (independentCachedEdge 250)=independentCachedBranchMembers8809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8809
def independentCachedBranchMembers8811 : Finset ℕ := ([132,252,1594,1626,1768,1776,2666,2674,2744,2776,3102,3174,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8811 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8811 4 (fun x => (if x<2744 then (if x<1768 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1626 then 1 else 2)) else (if x<2666 then (if x<1776 then 1 else 2) else (if x<2674 then 1 else 2))) else (if x<3244 then (if x<3102 then (if x<2776 then 1 else 2) else (if x<3174 then 3 else 3)) else (if x<3276 then (if x<3252 then 0 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8812 : Finset ℕ := ([48,72,130,132,250,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8812 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8812 130 4
  · have he : independentCachedBranchMembers8812.erase 130=independentCachedBranchMembers8810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8810
  · have he : independentCachedBranchMembers8812.filter (independentCachedEdge 130)=independentCachedBranchMembers8811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8811
def independentCachedBranchMembers8813 : Finset ℕ := ([48,72,1594,1596,1686,1768,2666,2668,2744,2758,3102,3174,3250,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8813 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8813 4 (fun x => (if x<2744 then (if x<1686 then (if x<1594 then (if x<72 then 0 else 0) else (if x<1596 then 1 else 2)) else (if x<2666 then (if x<1768 then 1 else 2) else (if x<2668 then 1 else 2))) else (if x<3250 then (if x<3102 then (if x<2758 then 2 else 1) else (if x<3174 then 3 else 3)) else (if x<3274 then (if x<3252 then 0 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8814 : Finset ℕ := ([48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8814 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8814 80 4
  · have he : independentCachedBranchMembers8814.erase 80=independentCachedBranchMembers8812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8812
  · have he : independentCachedBranchMembers8814.filter (independentCachedEdge 80)=independentCachedBranchMembers8813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8813
def independentCachedBranchMembers8815 : Finset ℕ := ([48,72,1626,1628,1678,1776,2674,2676,2726,2776,3102,3174,3250,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8815 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8815 4 (fun x => (if x<2726 then (if x<1678 then (if x<1626 then (if x<72 then 0 else 0) else (if x<1628 then 1 else 2)) else (if x<2674 then (if x<1776 then 1 else 2) else (if x<2676 then 1 else 2))) else (if x<3250 then (if x<3102 then (if x<2776 then 1 else 2) else (if x<3174 then 3 else 3)) else (if x<3274 then (if x<3252 then 0 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8816 : Finset ℕ := ([40,48,72,80,130,132,250,252,1594,1596,1626,1628,1678,1686,1768,1776,2666,2668,2674,2676,2726,2744,2758,2776,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8816 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8816 40 4
  · have he : independentCachedBranchMembers8816.erase 40=independentCachedBranchMembers8814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8814
  · have he : independentCachedBranchMembers8816.filter (independentCachedEdge 40)=independentCachedBranchMembers8815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8815
def independentCachedBranchMembers8817 : Finset ℕ := ([36,40,48,66,72,80,130,132,144,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2662,2666,2668,2674,2676,2680,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8817 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8817 2662 5
  · have he : independentCachedBranchMembers8817.erase 2662=independentCachedBranchMembers8793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8793
  · have he : independentCachedBranchMembers8817.filter (independentCachedEdge 2662)=independentCachedBranchMembers8816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8816
def independentCachedBranchMembers8818 : Finset ℕ := ([1594,1596,1614,1626,1628,1678,1686,1692,1764,1768,1776,3072,3102,3178,3180,3186,3188,3192,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8818 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8818 5 (fun x => (if x<3180 then (if x<1692 then (if x<1626 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1678 then (if x<1628 then 1 else 2) else (if x<1686 then 1 else 0))) else (if x<1776 then (if x<1764 then 3 else (if x<1768 then 2 else 1)) else (if x<3102 then (if x<3072 then 3 else 4) else (if x<3178 then 0 else 0)))) else (if x<3252 then (if x<3192 then (if x<3186 then 2 else (if x<3188 then 3 else 4)) else (if x<3244 then (if x<3238 then 1 else 2) else (if x<3250 then 1 else 0))) else (if x<3274 then (if x<3256 then 3 else (if x<3270 then 4 else 0)) else (if x<3284 then (if x<3276 then 1 else 4) else (if x<3288 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8819 : Finset ℕ := ([1594,1596,1686,1768,3072,3178,3180,3192,3244,3256,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8819 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8819 4 (fun x => (if x<3180 then (if x<1768 then (if x<1596 then 0 else (if x<1686 then 1 else 0)) else (if x<3072 then 1 else (if x<3178 then 2 else 0))) else (if x<3256 then (if x<3192 then 1 else (if x<3244 then 2 else 2)) else (if x<3270 then 1 else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8820 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1692,1764,1768,1776,3072,3102,3178,3180,3186,3188,3192,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8820 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8820 1590 4
  · have he : independentCachedBranchMembers8820.erase 1590=independentCachedBranchMembers8818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8818
  · have he : independentCachedBranchMembers8820.filter (independentCachedEdge 1590)=independentCachedBranchMembers8819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8819
def independentCachedBranchMembers8821 : Finset ℕ := ([1590,1594,1614,1628,1678,1692,1764,1768,3180,3186,3244,3250,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8821 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8821 4 (fun x => (if x<3180 then (if x<1678 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1628 then 0 else 1)) else (if x<1764 then (if x<1692 then 1 else 0) else (if x<1768 then 0 else 1))) else (if x<3270 then (if x<3244 then (if x<3186 then 2 else 2) else (if x<3250 then 3 else 3)) else (if x<3284 then (if x<3274 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8822 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1692,1764,1768,1776,3072,3102,3178,3180,3186,3188,3192,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8822 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8822 3282 4
  · have he : independentCachedBranchMembers8822.erase 3282=independentCachedBranchMembers8820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8820
  · have he : independentCachedBranchMembers8822.filter (independentCachedEdge 3282)=independentCachedBranchMembers8821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8821
def independentCachedBranchMembers8823 : Finset ℕ := ([1590,1596,1614,1626,1686,1692,1764,1776,3178,3188,3238,3244,3250,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8823 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8823 4 (fun x => (if x<3178 then (if x<1686 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1626 then 0 else 1)) else (if x<1764 then (if x<1692 then 1 else 0) else (if x<1776 then 0 else 1))) else (if x<3250 then (if x<3238 then (if x<3188 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3274 then (if x<3256 then 3 else 2) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8824 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1692,1764,1768,1776,3072,3102,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8824 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8824 3242 4
  · have he : independentCachedBranchMembers8824.erase 3242=independentCachedBranchMembers8822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8822
  · have he : independentCachedBranchMembers8824.filter (independentCachedEdge 3242)=independentCachedBranchMembers8823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8823
def independentCachedBranchMembers8825 : Finset ℕ := ([1594,1596,1626,1628,1678,1686,1768,1776,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8825 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8825 4 (fun x => (if x<3178 then (if x<1678 then (if x<1626 then (if x<1596 then 0 else 1) else (if x<1628 then 1 else 0)) else (if x<1768 then (if x<1686 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3238 then (if x<3186 then (if x<3180 then 2 else 3) else (if x<3188 then 3 else 2)) else (if x<3270 then (if x<3256 then 2 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8826 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1692,1764,1768,1776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8826 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8826 3174 4
  · have he : independentCachedBranchMembers8826.erase 3174=independentCachedBranchMembers8824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8824
  · have he : independentCachedBranchMembers8826.filter (independentCachedEdge 3174)=independentCachedBranchMembers8825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8825
def independentCachedBranchMembers8827 : Finset ℕ := ([1596,1628,1692,1764,1768,1776,3072,3180,3188,3192,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8827 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8827 4 (fun x => (if x<3188 then (if x<1768 then (if x<1692 then (if x<1628 then 0 else 1) else (if x<1764 then 2 else 0)) else (if x<3072 then (if x<1776 then 1 else 2) else (if x<3180 then 3 else 0))) else (if x<3256 then (if x<3244 then (if x<3192 then 3 else 1) else (if x<3252 then 3 else 0)) else (if x<3284 then (if x<3276 then 2 else 1) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8828 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1692,1762,1764,1768,1776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8828 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8828 1762 4
  · have he : independentCachedBranchMembers8828.erase 1762=independentCachedBranchMembers8826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8826
  · have he : independentCachedBranchMembers8828.filter (independentCachedEdge 1762)=independentCachedBranchMembers8827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8827
def independentCachedBranchMembers8829 : Finset ℕ := ([1594,1626,1678,1686,1692,1764,3072,3178,3186,3192,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8829 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8829 4 (fun x => (if x<3186 then (if x<1692 then (if x<1678 then (if x<1626 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<3072 then (if x<1764 then 2 else 2) else (if x<3178 then 3 else 1))) else (if x<3252 then (if x<3238 then (if x<3192 then 0 else 3) else (if x<3244 then 1 else 2)) else (if x<3276 then (if x<3270 then 3 else 0) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8830 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8830 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8830 1690 4
  · have he : independentCachedBranchMembers8830.erase 1690=independentCachedBranchMembers8828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8828
  · have he : independentCachedBranchMembers8830.filter (independentCachedEdge 1690)=independentCachedBranchMembers8829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8829
def independentCachedBranchMembers8831 : Finset ℕ := ([1590,1614,1626,1628,1686,1768,3072,3178,3180,3192,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8831 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8831 4 (fun x => (if x<3180 then (if x<1686 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1628 then 1 else 2)) else (if x<3072 then (if x<1768 then 1 else 2) else (if x<3178 then 3 else 1))) else (if x<3252 then (if x<3238 then (if x<3192 then 2 else 3) else (if x<3250 then 1 else 0)) else (if x<3276 then (if x<3274 then 3 else 0) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
