/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch63
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4832 : Finset ℕ := ([48,68,136,250,252,1644,1650,1720,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4832 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4832 250 4
  · have he : independentCachedBranchMembers4832.erase 250=independentCachedBranchMembers4830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4830
  · have he : independentCachedBranchMembers4832.filter (independentCachedEdge 250)=independentCachedBranchMembers4831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4831
def independentCachedBranchMembers4833 : Finset ℕ := ([48,136,1650,1738,2680,2730,2732,2758,3130,3132,3158,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4833 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4833 4 (fun x => (if x<2732 then (if x<1738 then (if x<136 then 0 else (if x<1650 then 0 else 0)) else (if x<2680 then 0 else (if x<2730 then 1 else 1))) else (if x<3132 then (if x<2758 then 2 else (if x<3130 then 2 else 1)) else (if x<3158 then 2 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4834 : Finset ℕ := ([48,68,136,144,250,252,1644,1650,1720,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4834 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4834 144 4
  · have he : independentCachedBranchMembers4834.erase 144=independentCachedBranchMembers4832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4832
  · have he : independentCachedBranchMembers4834.filter (independentCachedEdge 144)=independentCachedBranchMembers4833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4833
def independentCachedBranchMembers4835 : Finset ℕ := ([68,252,1644,1748,2680,2730,2738,2776,3130,3226,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4835 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4835 4 (fun x => (if x<2738 then (if x<1748 then (if x<252 then 0 else (if x<1644 then 0 else 0)) else (if x<2680 then 0 else (if x<2730 then 1 else 1))) else (if x<3226 then (if x<2776 then 2 else (if x<3130 then 2 else 1)) else (if x<3304 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4836 : Finset ℕ := ([48,66,68,136,144,250,252,1644,1650,1720,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4836 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4836 66 4
  · have he : independentCachedBranchMembers4836.erase 66=independentCachedBranchMembers4834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4834
  · have he : independentCachedBranchMembers4836.filter (independentCachedEdge 66)=independentCachedBranchMembers4835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4835
def independentCachedBranchMembers4837 : Finset ℕ := ([48,136,1650,1738,2662,2738,2740,2776,3150,3226,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4837 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4837 4 (fun x => (if x<2740 then (if x<1738 then (if x<136 then 0 else (if x<1650 then 0 else 0)) else (if x<2662 then 0 else (if x<2738 then 1 else 1))) else (if x<3226 then (if x<2776 then 2 else (if x<3150 then 2 else 1)) else (if x<3228 then 1 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4838 : Finset ℕ := ([40,48,66,68,136,144,250,252,1644,1650,1720,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4838 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4838 40 4
  · have he : independentCachedBranchMembers4838.erase 40=independentCachedBranchMembers4836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4836
  · have he : independentCachedBranchMembers4838.filter (independentCachedEdge 40)=independentCachedBranchMembers4837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4837
def independentCachedBranchMembers4839 : Finset ℕ := ([40,48,66,68,136,144,250,252,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4839 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4839 4 (fun x => (if x<3130 then (if x<136 then (if x<66 then (if x<48 then 0 else 1) else (if x<68 then 0 else 1)) else (if x<250 then (if x<144 then 1 else 0) else (if x<252 then 0 else 1))) else (if x<3226 then (if x<3150 then (if x<3132 then 2 else 3) else (if x<3158 then 2 else 3)) else (if x<3304 then (if x<3228 then 3 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4840 : Finset ℕ := ([40,48,66,68,136,144,250,252,1644,1650,1702,1720,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4840 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4840 1702 4
  · have he : independentCachedBranchMembers4840.erase 1702=independentCachedBranchMembers4838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4838
  · have he : independentCachedBranchMembers4840.filter (independentCachedEdge 1702)=independentCachedBranchMembers4839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4839
def independentCachedBranchMembers4841 : Finset ℕ := ([40,48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4841 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4841 3102 5
  · have he : independentCachedBranchMembers4841.erase 3102=independentCachedBranchMembers4825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4825
  · have he : independentCachedBranchMembers4841.filter (independentCachedEdge 3102)=independentCachedBranchMembers4840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4840
def independentCachedBranchMembers4842 : Finset ℕ := ([1644,1650,1690,1702,1738,1748,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4842 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4842 5 (fun x => (if x<2662 then (if x<1748 then (if x<1690 then (if x<1650 then 0 else 0) else (if x<1702 then 1 else (if x<1738 then 0 else 0))) else (if x<2614 then (if x<1776 then 0 else (if x<2606 then 1 else 2)) else (if x<2650 then 3 else (if x<2652 then 2 else 3)))) else (if x<2738 then (if x<2710 then (if x<2680 then 4 else (if x<2702 then 4 else 1)) else (if x<2730 then 2 else (if x<2732 then 4 else 3))) else (if x<2776 then (if x<2740 then 1 else (if x<2758 then 4 else 3)) else (if x<2786 then 1 else (if x<2788 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4843 : Finset ℕ := ([1650,1748,2606,2680,2702,2738,2740,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4843 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4843 4 (fun x => (if x<2738 then (if x<2606 then (if x<1748 then 0 else 0) else (if x<2680 then 1 else (if x<2702 then 1 else 2))) else (if x<2776 then (if x<2740 then 1 else 2) else (if x<2786 then 2 else (if x<2788 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4844 : Finset ℕ := ([1622,1644,1650,1690,1702,1738,1748,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4844 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4844 1622 4
  · have he : independentCachedBranchMembers4844.erase 1622=independentCachedBranchMembers4842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4842
  · have he : independentCachedBranchMembers4844.filter (independentCachedEdge 1622)=independentCachedBranchMembers4843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4843
def independentCachedBranchMembers4845 : Finset ℕ := ([1644,1738,2650,2662,2702,2710,2730,2738,2776,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4845 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4845 4 (fun x => (if x<2710 then (if x<2650 then (if x<1738 then 0 else 0) else (if x<2662 then 1 else (if x<2702 then 1 else 1))) else (if x<2738 then (if x<2730 then 2 else 2) else (if x<2776 then 1 else (if x<2788 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4846 : Finset ℕ := ([1596,1622,1644,1650,1690,1702,1738,1748,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4846 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4846 1596 4
  · have he : independentCachedBranchMembers4846.erase 1596=independentCachedBranchMembers4844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4844
  · have he : independentCachedBranchMembers4846.filter (independentCachedEdge 1596)=independentCachedBranchMembers4845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4845
def independentCachedBranchMembers4847 : Finset ℕ := ([1622,1644,1738,1776,2606,2650,2652,2662,2702,2738,2740,2758] : List ℕ).toFinset
theorem independentCachedBranchBound4847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4847 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4847 4 (fun x => (if x<2652 then (if x<1776 then (if x<1644 then 0 else (if x<1738 then 0 else 0)) else (if x<2606 then 0 else (if x<2650 then 1 else 1))) else (if x<2738 then (if x<2662 then 2 else (if x<2702 then 2 else 2)) else (if x<2740 then 1 else (if x<2758 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4848 : Finset ℕ := ([1596,1622,1644,1650,1690,1702,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4848 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4848 1768 4
  · have he : independentCachedBranchMembers4848.erase 1768=independentCachedBranchMembers4846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4846
  · have he : independentCachedBranchMembers4848.filter (independentCachedEdge 1768)=independentCachedBranchMembers4847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4847
def independentCachedBranchMembers4849 : Finset ℕ := ([1596,1650,1690,1748,2606,2614,2650,2680,2730,2738,2758,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4849 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4849 4 (fun x => (if x<2650 then (if x<1748 then (if x<1650 then 0 else (if x<1690 then 0 else 0)) else (if x<2606 then 0 else (if x<2614 then 1 else 2))) else (if x<2738 then (if x<2680 then 1 else (if x<2730 then 2 else 2)) else (if x<2758 then 1 else (if x<2788 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4850 : Finset ℕ := ([1596,1622,1644,1650,1690,1692,1702,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4850 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4850 1692 4
  · have he : independentCachedBranchMembers4850.erase 1692=independentCachedBranchMembers4848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4848
  · have he : independentCachedBranchMembers4850.filter (independentCachedEdge 1692)=independentCachedBranchMembers4849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4849
def independentCachedBranchMembers4851 : Finset ℕ := ([1622,1644,1738,1776,2614,2680,2710,2730,2732,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4851 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4851 4 (fun x => (if x<2710 then (if x<1776 then (if x<1644 then 0 else (if x<1738 then 0 else 0)) else (if x<2614 then 0 else (if x<2680 then 1 else 1))) else (if x<2776 then (if x<2730 then 2 else (if x<2732 then 1 else 2)) else (if x<2786 then 2 else (if x<2788 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4852 : Finset ℕ := ([1596,1614,1622,1644,1650,1690,1692,1702,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4852 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4852 1614 4
  · have he : independentCachedBranchMembers4852.erase 1614=independentCachedBranchMembers4850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4850
  · have he : independentCachedBranchMembers4852.filter (independentCachedEdge 1614)=independentCachedBranchMembers4851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4851
def independentCachedBranchMembers4853 : Finset ℕ := ([1596,1650,1690,1748,2652,2662,2702,2710,2732,2740,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound4853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4853 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4853 4 (fun x => (if x<2702 then (if x<1748 then (if x<1650 then 0 else (if x<1690 then 0 else 0)) else (if x<2652 then 0 else (if x<2662 then 1 else 1))) else (if x<2740 then (if x<2710 then 1 else (if x<2732 then 2 else 2)) else (if x<2776 then 1 else (if x<2786 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4854 : Finset ℕ := ([1594,1596,1614,1622,1644,1650,1690,1692,1702,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4854 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4854 1594 4
  · have he : independentCachedBranchMembers4854.erase 1594=independentCachedBranchMembers4852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4852
  · have he : independentCachedBranchMembers4854.filter (independentCachedEdge 1594)=independentCachedBranchMembers4853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4853
def independentCachedBranchMembers4855 : Finset ℕ := ([1594,1596,1614,1622,1690,1692,1768,1776,2606,2614,2650,2652,2702,2710,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4855 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4855 4 (fun x => (if x<2606 then (if x<1690 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1622 then 0 else 1)) else (if x<1768 then (if x<1692 then 1 else 0) else (if x<1776 then 0 else 1))) else (if x<2702 then (if x<2650 then (if x<2614 then 2 else 3) else (if x<2652 then 2 else 3)) else (if x<2786 then (if x<2710 then 3 else 2) else (if x<2788 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4856 : Finset ℕ := ([1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4856 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4856 1720 4
  · have he : independentCachedBranchMembers4856.erase 1720=independentCachedBranchMembers4854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4854
  · have he : independentCachedBranchMembers4856.filter (independentCachedEdge 1720)=independentCachedBranchMembers4855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4855
def independentCachedBranchMembers4857 : Finset ℕ := ([40,48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3072,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4857 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4857 3072 5
  · have he : independentCachedBranchMembers4857.erase 3072=independentCachedBranchMembers4841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4841
  · have he : independentCachedBranchMembers4857.filter (independentCachedEdge 3072)=independentCachedBranchMembers4856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4856
def independentCachedBranchMembers4858 : Finset ℕ := ([252,1596,1622,1644,1650,1690,1738,1748,1776,2614,2652,2662,2680,2702,2730,2740,2788,3130,3150,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4858 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4858 5 (fun x => (if x<2702 then (if x<1738 then (if x<1644 then (if x<1596 then 0 else (if x<1622 then 0 else 1)) else (if x<1650 then 1 else (if x<1690 then 2 else 2))) else (if x<2614 then (if x<1748 then 1 else (if x<1776 then 0 else 1)) else (if x<2662 then (if x<2652 then 3 else 0) else (if x<2680 then 2 else 3)))) else (if x<3188 then (if x<2788 then (if x<2730 then 2 else (if x<2740 then 3 else 0)) else (if x<3130 then 3 else (if x<3150 then 3 else 1))) else (if x<3256 then (if x<3228 then 0 else (if x<3238 then 0 else 3)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3304 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4859 : Finset ℕ := ([1596,1644,1748,1776,2652,2680,2740,2788,3130,3150,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4859 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4859 4 (fun x => (if x<2740 then (if x<1776 then (if x<1644 then 0 else (if x<1748 then 1 else 0)) else (if x<2652 then 1 else (if x<2680 then 0 else 1))) else (if x<3150 then (if x<2788 then 0 else (if x<3130 then 1 else 2)) else (if x<3238 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4860 : Finset ℕ := ([136,252,1596,1622,1644,1650,1690,1738,1748,1776,2614,2652,2662,2680,2702,2730,2740,2788,3130,3150,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4860 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4860 136 4
  · have he : independentCachedBranchMembers4860.erase 136=independentCachedBranchMembers4858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4858
  · have he : independentCachedBranchMembers4860.filter (independentCachedEdge 136)=independentCachedBranchMembers4859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4859
def independentCachedBranchMembers4861 : Finset ℕ := ([1596,1650,1738,1776,2614,2680,2702,2740,3228,3238,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4861 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4861 4 (fun x => (if x<2702 then (if x<1776 then (if x<1650 then 0 else (if x<1738 then 0 else 1)) else (if x<2614 then 1 else (if x<2680 then 0 else 0))) else (if x<3238 then (if x<2740 then 1 else (if x<3228 then 1 else 2)) else (if x<3282 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4862 : Finset ℕ := ([68,136,252,1596,1622,1644,1650,1690,1738,1748,1776,2614,2652,2662,2680,2702,2730,2740,2788,3130,3150,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4862 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4862 68 4
  · have he : independentCachedBranchMembers4862.erase 68=independentCachedBranchMembers4860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4860
  · have he : independentCachedBranchMembers4862.filter (independentCachedEdge 68)=independentCachedBranchMembers4861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4861
def independentCachedBranchMembers4863 : Finset ℕ := ([1622,1644,1690,1748,2652,2662,2730,2788,3228,3238,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4863 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4863 4 (fun x => (if x<2730 then (if x<1748 then (if x<1644 then 0 else (if x<1690 then 0 else 1)) else (if x<2652 then 1 else (if x<2662 then 0 else 0))) else (if x<3238 then (if x<2788 then 1 else (if x<3228 then 1 else 2)) else (if x<3282 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
