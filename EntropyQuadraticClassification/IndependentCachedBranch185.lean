/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch184
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8704 : Finset ℕ := ([80,132,1590,1594,1622,1626,1628,1678,1762,1764,2590,2674,2676,2680,2726,2732,2758,2762,3102,3186,3188,3192,3238,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8704 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8704 2676 4
  · have he : independentCachedBranchMembers8704.erase 2676=independentCachedBranchMembers8702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8702
  · have he : independentCachedBranchMembers8704.filter (independentCachedEdge 2676)=independentCachedBranchMembers8703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8703
def independentCachedBranchMembers8705 : Finset ℕ := ([80,132,1590,1594,1628,1762,2674,2726,3186,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8705 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8705 4 (fun x => (if x<2674 then (if x<1594 then (if x<132 then 0 else (if x<1590 then 0 else 1)) else (if x<1628 then 2 else (if x<1762 then 1 else 2))) else (if x<3238 then (if x<2726 then 0 else (if x<3186 then 0 else 2)) else (if x<3242 then 1 else (if x<3276 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8706 : Finset ℕ := ([80,132,1590,1594,1596,1622,1626,1628,1678,1762,1764,2590,2674,2676,2680,2726,2732,2758,2762,3102,3186,3188,3192,3238,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8706 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8706 1596 4
  · have he : independentCachedBranchMembers8706.erase 1596=independentCachedBranchMembers8704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8704
  · have he : independentCachedBranchMembers8706.filter (independentCachedEdge 1596)=independentCachedBranchMembers8705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8705
def independentCachedBranchMembers8707 : Finset ℕ := ([132,1590,1594,1622,1626,1764,2590,2674,2732,3102,3186,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8707 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8707 4 (fun x => (if x<2590 then (if x<1622 then (if x<1590 then 0 else (if x<1594 then 1 else 0)) else (if x<1626 then 2 else (if x<1764 then 1 else 2))) else (if x<3102 then (if x<2674 then 1 else (if x<2732 then 0 else 2)) else (if x<3186 then 3 else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8708 : Finset ℕ := ([80,130,132,1590,1594,1596,1622,1626,1628,1678,1762,1764,2590,2674,2676,2680,2726,2732,2758,2762,3102,3186,3188,3192,3238,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8708 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8708 130 4
  · have he : independentCachedBranchMembers8708.erase 130=independentCachedBranchMembers8706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8706
  · have he : independentCachedBranchMembers8708.filter (independentCachedEdge 130)=independentCachedBranchMembers8707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8707
def independentCachedBranchMembers8709 : Finset ℕ := ([80,1622,1626,1628,1762,1764,2590,2726,2732,3102,3238,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8709 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8709 4 (fun x => (if x<2590 then (if x<1628 then (if x<1622 then 0 else (if x<1626 then 0 else 1)) else (if x<1762 then 2 else (if x<1764 then 1 else 2))) else (if x<3102 then (if x<2726 then 1 else (if x<2732 then 1 else 0)) else (if x<3238 then 2 else (if x<3242 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8710 : Finset ℕ := ([48,80,130,132,1590,1594,1596,1622,1626,1628,1678,1762,1764,2590,2674,2676,2680,2726,2732,2758,2762,3102,3186,3188,3192,3238,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8710 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8710 48 4
  · have he : independentCachedBranchMembers8710.erase 48=independentCachedBranchMembers8708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8708
  · have he : independentCachedBranchMembers8710.filter (independentCachedEdge 48)=independentCachedBranchMembers8709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8709
def independentCachedBranchMembers8711 : Finset ℕ := ([132,1594,1622,1628,1764,2590,2674,2680,2726,2732,2762,3188,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8711 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8711 4 (fun x => (if x<2680 then (if x<1628 then (if x<1594 then 0 else (if x<1622 then 0 else 1)) else (if x<2590 then (if x<1764 then 2 else 1) else (if x<2674 then 1 else 0))) else (if x<3188 then (if x<2732 then (if x<2726 then 2 else 3) else (if x<2762 then 1 else 3)) else (if x<3270 then (if x<3242 then 2 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8712 : Finset ℕ := ([1594,1764,2590,2762,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8712 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8712 3 (fun x => (if x<2762 then (if x<1764 then 0 else (if x<2590 then 1 else 0)) else (if x<3270 then 2 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8713 : Finset ℕ := ([80,132,1594,1622,1628,1764,2590,2674,2680,2726,2732,2762,3188,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8713 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8713 80 3
  · have he : independentCachedBranchMembers8713.erase 80=independentCachedBranchMembers8711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8711
  · have he : independentCachedBranchMembers8713.filter (independentCachedEdge 80)=independentCachedBranchMembers8712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8712
def independentCachedBranchMembers8714 : Finset ℕ := ([48,80,130,132,1590,1594,1596,1622,1626,1628,1678,1762,1764,2590,2674,2676,2680,2726,2732,2758,2762,3102,3186,3188,3192,3238,3242,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8714 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8714 3274 4
  · have he : independentCachedBranchMembers8714.erase 3274=independentCachedBranchMembers8710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8710
  · have he : independentCachedBranchMembers8714.filter (independentCachedEdge 3274)=independentCachedBranchMembers8713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8713
def independentCachedBranchMembers8715 : Finset ℕ := ([130,1590,1594,1628,1762,2590,2676,2680,2732,2758,2762,3186,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8715 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8715 4 (fun x => (if x<2680 then (if x<1628 then (if x<1590 then 0 else (if x<1594 then 1 else 2)) else (if x<2590 then (if x<1762 then 0 else 1) else (if x<2676 then 1 else 0))) else (if x<3186 then (if x<2758 then (if x<2732 then 2 else 3) else (if x<2762 then 3 else 1)) else (if x<3242 then (if x<3238 then 2 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8716 : Finset ℕ := ([1628,1762,2590,2732,3238,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8716 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8716 3 (fun x => (if x<2732 then (if x<1762 then 0 else (if x<2590 then 1 else 0)) else (if x<3238 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8717 : Finset ℕ := ([48,130,1590,1594,1628,1762,2590,2676,2680,2732,2758,2762,3186,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8717 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8717 48 3
  · have he : independentCachedBranchMembers8717.erase 48=independentCachedBranchMembers8715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8715
  · have he : independentCachedBranchMembers8717.filter (independentCachedEdge 48)=independentCachedBranchMembers8716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8716
def independentCachedBranchMembers8718 : Finset ℕ := ([48,80,130,132,1590,1594,1596,1622,1626,1628,1678,1762,1764,2590,2674,2676,2680,2726,2732,2758,2762,3102,3186,3188,3192,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8718 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8718 3244 4
  · have he : independentCachedBranchMembers8718.erase 3244=independentCachedBranchMembers8714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8714
  · have he : independentCachedBranchMembers8718.filter (independentCachedEdge 3244)=independentCachedBranchMembers8717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8717
def independentCachedBranchMembers8719 : Finset ℕ := ([48,80,130,132,1590,1622,1762,1764,2674,2676,2726,2758,3186,3188,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8719 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8719 4 (fun x => (if x<2674 then (if x<1590 then (if x<130 then (if x<80 then 0 else 1) else (if x<132 then 0 else 1)) else (if x<1762 then (if x<1622 then 2 else 3) else (if x<1764 then 2 else 3))) else (if x<3186 then (if x<2726 then (if x<2676 then 1 else 0) else (if x<2758 then 1 else 0)) else (if x<3238 then (if x<3188 then 2 else 3) else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8720 : Finset ℕ := ([48,80,130,132,1590,1594,1596,1622,1626,1628,1678,1762,1764,1768,2590,2674,2676,2680,2726,2732,2758,2762,3102,3186,3188,3192,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8720 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8720 1768 4
  · have he : independentCachedBranchMembers8720.erase 1768=independentCachedBranchMembers8718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8718
  · have he : independentCachedBranchMembers8720.filter (independentCachedEdge 1768)=independentCachedBranchMembers8719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8719
def independentCachedBranchMembers8721 : Finset ℕ := ([40,48,72,80,130,132,144,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2590,2666,2668,2674,2676,2680,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8721 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8721 144 5
  · have he : independentCachedBranchMembers8721.erase 144=independentCachedBranchMembers8699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8699
  · have he : independentCachedBranchMembers8721.filter (independentCachedEdge 144)=independentCachedBranchMembers8720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8720
def independentCachedBranchMembers8722 : Finset ℕ := ([80,252,1582,1590,1628,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2726,2738,2772,2776,3102,3180,3188,3192,3238,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8722 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8722 5 (fun x => (if x<2676 then (if x<1686 then (if x<1590 then (if x<252 then 0 else (if x<1582 then 0 else 1)) else (if x<1628 then 2 else (if x<1678 then 0 else 2))) else (if x<1768 then (if x<1690 then 1 else (if x<1764 then 3 else 1)) else (if x<2590 then (if x<1776 then 3 else 0) else (if x<2668 then 1 else 1)))) else (if x<3180 then (if x<2738 then (if x<2680 then 0 else (if x<2726 then 4 else 1)) else (if x<2776 then (if x<2772 then 4 else 1) else (if x<3102 then 0 else 2))) else (if x<3238 then (if x<3188 then 3 else (if x<3192 then 2 else 0)) else (if x<3276 then (if x<3242 then 2 else 3) else (if x<3288 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8723 : Finset ℕ := ([252,1582,1590,1764,1768,1776,2590,2772,2776,3102,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8723 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8723 4 (fun x => (if x<2590 then (if x<1764 then (if x<1582 then 0 else (if x<1590 then 1 else 2)) else (if x<1768 then 0 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2772 then 1 else (if x<2776 then 0 else 1)) else (if x<3276 then 2 else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8724 : Finset ℕ := ([80,130,252,1582,1590,1628,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2726,2738,2772,2776,3102,3180,3188,3192,3238,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8724 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8724 130 4
  · have he : independentCachedBranchMembers8724.erase 130=independentCachedBranchMembers8722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8722
  · have he : independentCachedBranchMembers8724.filter (independentCachedEdge 130)=independentCachedBranchMembers8723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8723
def independentCachedBranchMembers8725 : Finset ℕ := ([80,1582,1678,1690,1764,1776,2590,2676,2772,3102,3188,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8725 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8725 4 (fun x => (if x<2590 then (if x<1690 then (if x<1582 then 0 else (if x<1678 then 0 else 1)) else (if x<1764 then 2 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2676 then 1 else (if x<2772 then 1 else 0)) else (if x<3188 then 2 else (if x<3242 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8726 : Finset ℕ := ([72,80,130,252,1582,1590,1628,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2726,2738,2772,2776,3102,3180,3188,3192,3238,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8726 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8726 72 4
  · have he : independentCachedBranchMembers8726.erase 72=independentCachedBranchMembers8724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8724
  · have he : independentCachedBranchMembers8726.filter (independentCachedEdge 72)=independentCachedBranchMembers8725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8725
def independentCachedBranchMembers8727 : Finset ℕ := ([130,1590,1678,1690,1768,2590,2668,2680,2726,2738,2772,3188,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8727 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8727 4 (fun x => (if x<2680 then (if x<1690 then (if x<1590 then 0 else (if x<1678 then 1 else 0)) else (if x<2590 then (if x<1768 then 1 else 2) else (if x<2668 then 1 else 2))) else (if x<3188 then (if x<2738 then (if x<2726 then 0 else 3) else (if x<2772 then 1 else 3)) else (if x<3276 then (if x<3242 then 0 else 3) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8728 : Finset ℕ := ([1678,1690,2590,2772,3188,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8728 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8728 3 (fun x => (if x<2772 then (if x<1690 then 0 else (if x<2590 then 1 else 0)) else (if x<3188 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8729 : Finset ℕ := ([72,130,1590,1678,1690,1768,2590,2668,2680,2726,2738,2772,3188,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8729 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8729 72 3
  · have he : independentCachedBranchMembers8729.erase 72=independentCachedBranchMembers8727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8727
  · have he : independentCachedBranchMembers8729.filter (independentCachedEdge 72)=independentCachedBranchMembers8728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8728
def independentCachedBranchMembers8730 : Finset ℕ := ([72,80,130,252,1582,1590,1628,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2726,2738,2772,2776,3102,3180,3188,3192,3238,3242,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8730 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8730 3284 4
  · have he : independentCachedBranchMembers8730.erase 3284=independentCachedBranchMembers8726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8726
  · have he : independentCachedBranchMembers8730.filter (independentCachedEdge 3284)=independentCachedBranchMembers8729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8729
def independentCachedBranchMembers8731 : Finset ℕ := ([252,1582,1678,1764,1768,2590,2676,2680,2738,2772,2776,3180,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8731 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8731 4 (fun x => (if x<2680 then (if x<1764 then (if x<1582 then 0 else (if x<1678 then 1 else 2)) else (if x<2590 then (if x<1768 then 0 else 1) else (if x<2676 then 1 else 0))) else (if x<3180 then (if x<2772 then (if x<2738 then 2 else 3) else (if x<2776 then 3 else 1)) else (if x<3242 then (if x<3238 then 0 else 2) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8732 : Finset ℕ := ([1764,1768,2590,2738,3180,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8732 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8732 3 (fun x => (if x<2738 then (if x<1768 then 0 else (if x<2590 then 1 else 0)) else (if x<3180 then 2 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8733 : Finset ℕ := ([80,252,1582,1678,1764,1768,2590,2676,2680,2738,2772,2776,3180,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8733 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8733 80 3
  · have he : independentCachedBranchMembers8733.erase 80=independentCachedBranchMembers8731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8731
  · have he : independentCachedBranchMembers8733.filter (independentCachedEdge 80)=independentCachedBranchMembers8732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8732
def independentCachedBranchMembers8734 : Finset ℕ := ([72,80,130,252,1582,1590,1628,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2726,2738,2772,2776,3102,3180,3188,3192,3238,3242,3250,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8734 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8734 3250 4
  · have he : independentCachedBranchMembers8734.erase 3250=independentCachedBranchMembers8730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8730
  · have he : independentCachedBranchMembers8734.filter (independentCachedEdge 3250)=independentCachedBranchMembers8733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8733
def independentCachedBranchMembers8735 : Finset ℕ := ([72,80,130,252,1582,1590,1690,1764,2668,2676,2726,2776,3180,3188,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8735 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8735 4 (fun x => (if x<2668 then (if x<1582 then (if x<130 then (if x<80 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1690 then (if x<1590 then 2 else 3) else (if x<1764 then 2 else 3))) else (if x<3180 then (if x<2726 then (if x<2676 then 0 else 1) else (if x<2776 then 0 else 1)) else (if x<3238 then (if x<3188 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
