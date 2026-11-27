/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch62
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4800 : Finset ℕ := ([1596,1614,1644,1650,1690,1702,1720,1748,1768,2606,2652,2710,2730,2740,2758,2776,2788,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4800 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4800 1644 4
  · have he : independentCachedBranchMembers4800.erase 1644=independentCachedBranchMembers4798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4798
  · have he : independentCachedBranchMembers4800.filter (independentCachedEdge 1644)=independentCachedBranchMembers4799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4799
def independentCachedBranchMembers4801 : Finset ℕ := ([1614,1650,1690,1702,2606,2710,2730,2758,3130,3158,3178,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4801 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4801 4 (fun x => (if x<2730 then (if x<1702 then (if x<1650 then 0 else (if x<1690 then 0 else 0)) else (if x<2606 then 0 else (if x<2710 then 1 else 1))) else (if x<3158 then (if x<2758 then 2 else (if x<3130 then 2 else 2)) else (if x<3178 then 2 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4802 : Finset ℕ := ([252,1596,1614,1644,1650,1690,1702,1720,1748,1768,2606,2652,2710,2730,2740,2758,2776,2788,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4802 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4802 252 4
  · have he : independentCachedBranchMembers4802.erase 252=independentCachedBranchMembers4800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4800
  · have he : independentCachedBranchMembers4802.filter (independentCachedEdge 252)=independentCachedBranchMembers4801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4801
def independentCachedBranchMembers4803 : Finset ℕ := ([1596,1650,1702,1768,2652,2730,2758,2788,3130,3158,3188,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4803 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4803 4 (fun x => (if x<2758 then (if x<1768 then (if x<1650 then 0 else (if x<1702 then 0 else 0)) else (if x<2652 then 0 else (if x<2730 then 1 else 2))) else (if x<3158 then (if x<2788 then 1 else (if x<3130 then 2 else 2)) else (if x<3188 then 1 else (if x<3276 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4804 : Finset ℕ := ([144,252,1596,1614,1644,1650,1690,1702,1720,1748,1768,2606,2652,2710,2730,2740,2758,2776,2788,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4804 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4804 144 4
  · have he : independentCachedBranchMembers4804.erase 144=independentCachedBranchMembers4802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4802
  · have he : independentCachedBranchMembers4804.filter (independentCachedEdge 144)=independentCachedBranchMembers4803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4803
def independentCachedBranchMembers4805 : Finset ℕ := ([1596,1650,1702,1768,2606,2710,2740,2776,3178,3228,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4805 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4805 4 (fun x => (if x<2740 then (if x<1768 then (if x<1650 then 0 else (if x<1702 then 0 else 0)) else (if x<2606 then 0 else (if x<2710 then 1 else 1))) else (if x<3228 then (if x<2776 then 2 else (if x<3178 then 2 else 1)) else (if x<3282 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4806 : Finset ℕ := ([68,144,252,1596,1614,1644,1650,1690,1702,1720,1748,1768,2606,2652,2710,2730,2740,2758,2776,2788,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4806 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4806 68 4
  · have he : independentCachedBranchMembers4806.erase 68=independentCachedBranchMembers4804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4804
  · have he : independentCachedBranchMembers4806.filter (independentCachedEdge 68)=independentCachedBranchMembers4805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4805
def independentCachedBranchMembers4807 : Finset ℕ := ([1614,1650,1690,1702,2652,2740,2776,2788,3188,3228,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4807 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4807 4 (fun x => (if x<2776 then (if x<1702 then (if x<1650 then 0 else (if x<1690 then 0 else 0)) else (if x<2652 then 0 else (if x<2740 then 1 else 1))) else (if x<3228 then (if x<2788 then 2 else (if x<3188 then 2 else 1)) else (if x<3276 then 1 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4808 : Finset ℕ := ([40,68,144,252,1596,1614,1644,1650,1690,1702,1720,1748,1768,2606,2652,2710,2730,2740,2758,2776,2788,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4808 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4808 40 4
  · have he : independentCachedBranchMembers4808.erase 40=independentCachedBranchMembers4806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4806
  · have he : independentCachedBranchMembers4808.filter (independentCachedEdge 40)=independentCachedBranchMembers4807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4807
def independentCachedBranchMembers4809 : Finset ℕ := ([40,68,144,252,1596,1614,1690,1768,2606,2652,2710,2788,3130,3158,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4809 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4809 4 (fun x => (if x<2606 then (if x<1596 then (if x<144 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1690 then (if x<1614 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3130 then (if x<2710 then (if x<2652 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3228 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4810 : Finset ℕ := ([40,68,144,252,1596,1614,1644,1650,1690,1702,1720,1738,1748,1768,2606,2652,2710,2730,2740,2758,2776,2788,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4810 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4810 1738 4
  · have he : independentCachedBranchMembers4810.erase 1738=independentCachedBranchMembers4808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4808
  · have he : independentCachedBranchMembers4810.filter (independentCachedEdge 1738)=independentCachedBranchMembers4809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4809
def independentCachedBranchMembers4811 : Finset ℕ := ([40,48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4811 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4811 3186 5
  · have he : independentCachedBranchMembers4811.erase 3186=independentCachedBranchMembers4797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4797
  · have he : independentCachedBranchMembers4811.filter (independentCachedEdge 3186)=independentCachedBranchMembers4810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4810
def independentCachedBranchMembers4812 : Finset ℕ := ([1594,1622,1644,1692,1702,1720,1738,1776,2614,2650,2702,2730,2740,2758,2776,2786,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4812 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4812 5 (fun x => (if x<2740 then (if x<1738 then (if x<1692 then (if x<1622 then 0 else (if x<1644 then 0 else 0)) else (if x<1702 then 0 else (if x<1720 then 0 else 1))) else (if x<2650 then (if x<1776 then 0 else (if x<2614 then 0 else 2)) else (if x<2702 then 2 else (if x<2730 then 2 else 1)))) else (if x<3178 then (if x<2786 then (if x<2758 then 1 else (if x<2776 then 1 else 1)) else (if x<3132 then 2 else (if x<3150 then 3 else 3))) else (if x<3276 then (if x<3188 then 4 else (if x<3226 then 4 else 3)) else (if x<3282 then 4 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4813 : Finset ℕ := ([1594,1622,1692,1776,2730,2740,2758,2776,3132,3150,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4813 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4813 4 (fun x => (if x<2758 then (if x<1776 then (if x<1622 then 0 else (if x<1692 then 0 else 0)) else (if x<2730 then 0 else (if x<2740 then 1 else 1))) else (if x<3150 then (if x<2776 then 1 else (if x<3132 then 1 else 2)) else (if x<3226 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4814 : Finset ℕ := ([1594,1622,1644,1650,1692,1702,1720,1738,1776,2614,2650,2702,2730,2740,2758,2776,2786,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4814 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4814 1650 4
  · have he : independentCachedBranchMembers4814.erase 1650=independentCachedBranchMembers4812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4812
  · have he : independentCachedBranchMembers4814.filter (independentCachedEdge 1650)=independentCachedBranchMembers4813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4813
def independentCachedBranchMembers4815 : Finset ℕ := ([1622,1644,1692,1702,2614,2702,2740,2758,3132,3150,3188,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4815 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4815 4 (fun x => (if x<2740 then (if x<1702 then (if x<1644 then 0 else (if x<1692 then 0 else 0)) else (if x<2614 then 0 else (if x<2702 then 1 else 1))) else (if x<3150 then (if x<2758 then 2 else (if x<3132 then 2 else 2)) else (if x<3188 then 2 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4816 : Finset ℕ := ([250,1594,1622,1644,1650,1692,1702,1720,1738,1776,2614,2650,2702,2730,2740,2758,2776,2786,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4816 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4816 250 4
  · have he : independentCachedBranchMembers4816.erase 250=independentCachedBranchMembers4814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4814
  · have he : independentCachedBranchMembers4816.filter (independentCachedEdge 250)=independentCachedBranchMembers4815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4815
def independentCachedBranchMembers4817 : Finset ℕ := ([1594,1644,1702,1776,2650,2740,2758,2786,3132,3150,3178,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4817 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4817 4 (fun x => (if x<2758 then (if x<1776 then (if x<1644 then 0 else (if x<1702 then 0 else 0)) else (if x<2650 then 0 else (if x<2740 then 1 else 2))) else (if x<3150 then (if x<2786 then 1 else (if x<3132 then 2 else 2)) else (if x<3178 then 1 else (if x<3282 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4818 : Finset ℕ := ([136,250,1594,1622,1644,1650,1692,1702,1720,1738,1776,2614,2650,2702,2730,2740,2758,2776,2786,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4818 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4818 136 4
  · have he : independentCachedBranchMembers4818.erase 136=independentCachedBranchMembers4816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4816
  · have he : independentCachedBranchMembers4818.filter (independentCachedEdge 136)=independentCachedBranchMembers4817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4817
def independentCachedBranchMembers4819 : Finset ℕ := ([1594,1644,1702,1776,2614,2702,2730,2776,3188,3226,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4819 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4819 4 (fun x => (if x<2730 then (if x<1776 then (if x<1644 then 0 else (if x<1702 then 0 else 0)) else (if x<2614 then 0 else (if x<2702 then 1 else 1))) else (if x<3226 then (if x<2776 then 2 else (if x<3188 then 2 else 1)) else (if x<3276 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4820 : Finset ℕ := ([66,136,250,1594,1622,1644,1650,1692,1702,1720,1738,1776,2614,2650,2702,2730,2740,2758,2776,2786,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4820 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4820 66 4
  · have he : independentCachedBranchMembers4820.erase 66=independentCachedBranchMembers4818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4818
  · have he : independentCachedBranchMembers4820.filter (independentCachedEdge 66)=independentCachedBranchMembers4819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4819
def independentCachedBranchMembers4821 : Finset ℕ := ([1622,1644,1692,1702,2650,2730,2776,2786,3178,3226,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4821 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4821 4 (fun x => (if x<2776 then (if x<1702 then (if x<1644 then 0 else (if x<1692 then 0 else 0)) else (if x<2650 then 0 else (if x<2730 then 1 else 1))) else (if x<3226 then (if x<2786 then 2 else (if x<3178 then 2 else 1)) else (if x<3282 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4822 : Finset ℕ := ([48,66,136,250,1594,1622,1644,1650,1692,1702,1720,1738,1776,2614,2650,2702,2730,2740,2758,2776,2786,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4822 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4822 48 4
  · have he : independentCachedBranchMembers4822.erase 48=independentCachedBranchMembers4820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4820
  · have he : independentCachedBranchMembers4822.filter (independentCachedEdge 48)=independentCachedBranchMembers4821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4821
def independentCachedBranchMembers4823 : Finset ℕ := ([48,66,136,250,1594,1622,1692,1776,2614,2650,2702,2786,3132,3150,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4823 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4823 4 (fun x => (if x<2614 then (if x<1594 then (if x<136 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1692 then (if x<1622 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3132 then (if x<2702 then (if x<2650 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3226 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4824 : Finset ℕ := ([48,66,136,250,1594,1622,1644,1650,1692,1702,1720,1738,1748,1776,2614,2650,2702,2730,2740,2758,2776,2786,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4824 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4824 1748 4
  · have he : independentCachedBranchMembers4824.erase 1748=independentCachedBranchMembers4822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4822
  · have he : independentCachedBranchMembers4824.filter (independentCachedEdge 1748)=independentCachedBranchMembers4823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4823
def independentCachedBranchMembers4825 : Finset ℕ := ([40,48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4825 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4825 3180 5
  · have he : independentCachedBranchMembers4825.erase 3180=independentCachedBranchMembers4811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4811
  · have he : independentCachedBranchMembers4825.filter (independentCachedEdge 3180)=independentCachedBranchMembers4824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4824
def independentCachedBranchMembers4826 : Finset ℕ := ([136,252,1644,1650,1720,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4826 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4826 5 (fun x => (if x<2738 then (if x<1738 then (if x<1644 then (if x<252 then 0 else 0) else (if x<1650 then 1 else (if x<1720 then 1 else 0))) else (if x<2680 then (if x<1748 then 1 else (if x<2662 then 1 else 2)) else (if x<2730 then 2 else (if x<2732 then 2 else 0)))) else (if x<3150 then (if x<2776 then (if x<2740 then 3 else (if x<2758 then 2 else 3)) else (if x<3130 then 0 else (if x<3132 then 3 else 4))) else (if x<3228 then (if x<3158 then 3 else (if x<3226 then 4 else 4)) else (if x<3304 then 0 else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4827 : Finset ℕ := ([1650,1738,2680,2732,2740,2776,3132,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4827 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4827 4 (fun x => (if x<2776 then (if x<2680 then (if x<1738 then 0 else 0) else (if x<2732 then 1 else (if x<2740 then 1 else 2))) else (if x<3228 then (if x<3132 then 2 else 1) else (if x<3304 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4828 : Finset ℕ := ([68,136,252,1644,1650,1720,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4828 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4828 68 4
  · have he : independentCachedBranchMembers4828.erase 68=independentCachedBranchMembers4826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4826
  · have he : independentCachedBranchMembers4828.filter (independentCachedEdge 68)=independentCachedBranchMembers4827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4827
def independentCachedBranchMembers4829 : Finset ℕ := ([1644,1748,2662,2730,2732,2776,3158,3226,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4829 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4829 4 (fun x => (if x<2776 then (if x<2662 then (if x<1748 then 0 else 0) else (if x<2730 then 1 else (if x<2732 then 1 else 2))) else (if x<3226 then (if x<3158 then 2 else 1) else (if x<3228 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4830 : Finset ℕ := ([48,68,136,252,1644,1650,1720,1738,1748,2662,2680,2730,2732,2738,2740,2758,2776,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4830 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4830 48 4
  · have he : independentCachedBranchMembers4830.erase 48=independentCachedBranchMembers4828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4828
  · have he : independentCachedBranchMembers4830.filter (independentCachedEdge 48)=independentCachedBranchMembers4829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4829
def independentCachedBranchMembers4831 : Finset ℕ := ([68,252,1644,1748,2662,2732,2740,2758,3132,3150,3158,3228] : List ℕ).toFinset
theorem independentCachedBranchBound4831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4831 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4831 4 (fun x => (if x<2740 then (if x<1748 then (if x<252 then 0 else (if x<1644 then 0 else 0)) else (if x<2662 then 0 else (if x<2732 then 1 else 1))) else (if x<3150 then (if x<2758 then 2 else (if x<3132 then 2 else 2)) else (if x<3158 then 2 else (if x<3228 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
