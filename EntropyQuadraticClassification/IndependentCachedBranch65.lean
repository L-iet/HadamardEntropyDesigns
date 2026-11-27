/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch64
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4864 : Finset ℕ := ([48,68,136,252,1596,1622,1644,1650,1690,1738,1748,1776,2614,2652,2662,2680,2702,2730,2740,2788,3130,3150,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4864 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4864 48 4
  · have he : independentCachedBranchMembers4864.erase 48=independentCachedBranchMembers4862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4862
  · have he : independentCachedBranchMembers4864.filter (independentCachedEdge 48)=independentCachedBranchMembers4863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4863
def independentCachedBranchMembers4865 : Finset ℕ := ([48,68,136,252,1596,1622,1690,1776,2614,2652,2702,2788,3130,3150,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4865 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4865 4 (fun x => (if x<2614 then (if x<1596 then (if x<136 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3130 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4866 : Finset ℕ := ([48,68,136,252,1596,1622,1644,1650,1690,1738,1748,1776,2614,2652,2662,2680,2702,2730,2740,2788,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4866 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4866 3178 4
  · have he : independentCachedBranchMembers4866.erase 3178=independentCachedBranchMembers4864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4864
  · have he : independentCachedBranchMembers4866.filter (independentCachedEdge 3178)=independentCachedBranchMembers4865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4865
def independentCachedBranchMembers4867 : Finset ℕ := ([48,68,136,252,1644,1650,1738,1748,2662,2680,2730,2740,3130,3150,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4867 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4867 4 (fun x => (if x<2662 then (if x<1644 then (if x<136 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1738 then (if x<1650 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3130 then (if x<2730 then (if x<2680 then 2 else 2) else (if x<2740 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4868 : Finset ℕ := ([48,68,136,252,1596,1622,1644,1650,1690,1738,1748,1776,2614,2652,2662,2680,2702,2730,2740,2788,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4868 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4868 3102 4
  · have he : independentCachedBranchMembers4868.erase 3102=independentCachedBranchMembers4866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4866
  · have he : independentCachedBranchMembers4868.filter (independentCachedEdge 3102)=independentCachedBranchMembers4867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4867
def independentCachedBranchMembers4869 : Finset ℕ := ([1596,1622,1644,1650,1690,1738,1748,1776,2614,2652,2662,2680,2702,2730,2740,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4869 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4869 4 (fun x => (if x<2614 then (if x<1690 then (if x<1644 then (if x<1622 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<2702 then (if x<2662 then (if x<2652 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<2740 then (if x<2730 then 2 else 3) else (if x<2788 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4870 : Finset ℕ := ([48,68,136,252,1596,1622,1644,1650,1690,1738,1748,1776,2614,2652,2662,2680,2702,2730,2740,2788,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4870 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4870 3072 4
  · have he : independentCachedBranchMembers4870.erase 3072=independentCachedBranchMembers4868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4868
  · have he : independentCachedBranchMembers4870.filter (independentCachedEdge 3072)=independentCachedBranchMembers4869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4869
def independentCachedBranchMembers4871 : Finset ℕ := ([40,48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1746,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3072,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4871 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4871 1746 5
  · have he : independentCachedBranchMembers4871.erase 1746=independentCachedBranchMembers4857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4857
  · have he : independentCachedBranchMembers4871.filter (independentCachedEdge 1746)=independentCachedBranchMembers4870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4870
def independentCachedBranchMembers4872 : Finset ℕ := ([250,1594,1614,1644,1650,1692,1738,1748,1768,2606,2650,2662,2680,2710,2730,2740,2786,3132,3158,3178,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4872 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4872 5 (fun x => (if x<2710 then (if x<1738 then (if x<1644 then (if x<1594 then 0 else (if x<1614 then 0 else 1)) else (if x<1650 then 2 else (if x<1692 then 1 else 2))) else (if x<2606 then (if x<1748 then 0 else (if x<1768 then 1 else 1)) else (if x<2662 then (if x<2650 then 3 else 0) else (if x<2680 then 2 else 3)))) else (if x<3178 then (if x<2786 then (if x<2730 then 2 else (if x<2740 then 0 else 3)) else (if x<3132 then 3 else (if x<3158 then 3 else 1))) else (if x<3256 then (if x<3226 then 0 else (if x<3238 then 0 else 3)) else (if x<3282 then (if x<3276 then 4 else 1) else (if x<3312 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4873 : Finset ℕ := ([1594,1650,1738,1768,2650,2680,2730,2786,3132,3158,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4873 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4873 4 (fun x => (if x<2730 then (if x<1768 then (if x<1650 then 0 else (if x<1738 then 1 else 0)) else (if x<2650 then 1 else (if x<2680 then 0 else 1))) else (if x<3158 then (if x<2786 then 0 else (if x<3132 then 1 else 2)) else (if x<3238 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4874 : Finset ℕ := ([144,250,1594,1614,1644,1650,1692,1738,1748,1768,2606,2650,2662,2680,2710,2730,2740,2786,3132,3158,3178,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4874 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4874 144 4
  · have he : independentCachedBranchMembers4874.erase 144=independentCachedBranchMembers4872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4872
  · have he : independentCachedBranchMembers4874.filter (independentCachedEdge 144)=independentCachedBranchMembers4873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4873
def independentCachedBranchMembers4875 : Finset ℕ := ([1594,1644,1748,1768,2606,2680,2710,2730,3226,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4875 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4875 4 (fun x => (if x<2710 then (if x<1768 then (if x<1644 then 0 else (if x<1748 then 0 else 1)) else (if x<2606 then 1 else (if x<2680 then 0 else 0))) else (if x<3238 then (if x<2730 then 1 else (if x<3226 then 1 else 2)) else (if x<3276 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4876 : Finset ℕ := ([66,144,250,1594,1614,1644,1650,1692,1738,1748,1768,2606,2650,2662,2680,2710,2730,2740,2786,3132,3158,3178,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4876 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4876 66 4
  · have he : independentCachedBranchMembers4876.erase 66=independentCachedBranchMembers4874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4874
  · have he : independentCachedBranchMembers4876.filter (independentCachedEdge 66)=independentCachedBranchMembers4875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4875
def independentCachedBranchMembers4877 : Finset ℕ := ([1614,1650,1692,1738,2650,2662,2740,2786,3226,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4877 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4877 4 (fun x => (if x<2740 then (if x<1738 then (if x<1650 then 0 else (if x<1692 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 0 else 0))) else (if x<3238 then (if x<2786 then 1 else (if x<3226 then 1 else 2)) else (if x<3276 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4878 : Finset ℕ := ([40,66,144,250,1594,1614,1644,1650,1692,1738,1748,1768,2606,2650,2662,2680,2710,2730,2740,2786,3132,3158,3178,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4878 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4878 40 4
  · have he : independentCachedBranchMembers4878.erase 40=independentCachedBranchMembers4876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4876
  · have he : independentCachedBranchMembers4878.filter (independentCachedEdge 40)=independentCachedBranchMembers4877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4877
def independentCachedBranchMembers4879 : Finset ℕ := ([40,66,144,250,1594,1614,1692,1768,2606,2650,2710,2786,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4879 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4879 4 (fun x => (if x<2606 then (if x<1594 then (if x<144 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3132 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4880 : Finset ℕ := ([40,66,144,250,1594,1614,1644,1650,1692,1738,1748,1768,2606,2650,2662,2680,2710,2730,2740,2786,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4880 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4880 3188 4
  · have he : independentCachedBranchMembers4880.erase 3188=independentCachedBranchMembers4878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4878
  · have he : independentCachedBranchMembers4880.filter (independentCachedEdge 3188)=independentCachedBranchMembers4879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4879
def independentCachedBranchMembers4881 : Finset ℕ := ([40,66,144,250,1644,1650,1738,1748,2662,2680,2730,2740,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4881 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4881 4 (fun x => (if x<2662 then (if x<1644 then (if x<144 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1738 then (if x<1650 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3132 then (if x<2730 then (if x<2680 then 2 else 2) else (if x<2740 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4882 : Finset ℕ := ([40,66,144,250,1594,1614,1644,1650,1692,1738,1748,1768,2606,2650,2662,2680,2710,2730,2740,2786,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4882 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4882 3102 4
  · have he : independentCachedBranchMembers4882.erase 3102=independentCachedBranchMembers4880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4880
  · have he : independentCachedBranchMembers4882.filter (independentCachedEdge 3102)=independentCachedBranchMembers4881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4881
def independentCachedBranchMembers4883 : Finset ℕ := ([1594,1614,1644,1650,1692,1738,1748,1768,2606,2650,2662,2680,2710,2730,2740,2786] : List ℕ).toFinset
theorem independentCachedBranchBound4883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4883 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4883 4 (fun x => (if x<2606 then (if x<1692 then (if x<1644 then (if x<1614 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<2710 then (if x<2662 then (if x<2650 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<2740 then (if x<2730 then 2 else 3) else (if x<2786 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4884 : Finset ℕ := ([40,66,144,250,1594,1614,1644,1650,1692,1738,1748,1768,2606,2650,2662,2680,2710,2730,2740,2786,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4884 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4884 3072 4
  · have he : independentCachedBranchMembers4884.erase 3072=independentCachedBranchMembers4882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4882
  · have he : independentCachedBranchMembers4884.filter (independentCachedEdge 3072)=independentCachedBranchMembers4883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4883
def independentCachedBranchMembers4885 : Finset ℕ := ([40,48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3072,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4885 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4885 1740 5
  · have he : independentCachedBranchMembers4885.erase 1740=independentCachedBranchMembers4871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4871
  · have he : independentCachedBranchMembers4885.filter (independentCachedEdge 1740)=independentCachedBranchMembers4884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4884
def independentCachedBranchMembers4886 : Finset ℕ := ([40,48,250,252,1594,1596,1644,1650,1702,1720,1768,1776,2606,2614,2680,2730,2732,2738,2740,2786,2788,3130,3132,3178,3188,3238,3256,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4886 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4886 5 (fun x => (if x<2680 then (if x<1650 then (if x<252 then (if x<48 then 0 else (if x<250 then 1 else 0)) else (if x<1596 then (if x<1594 then 1 else 0) else (if x<1644 then 1 else 2))) else (if x<1768 then (if x<1702 then 2 else (if x<1720 then 2 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2614 then 3 else 4)))) else (if x<3130 then (if x<2738 then (if x<2730 then 0 else (if x<2732 then 0 else 2)) else (if x<2786 then (if x<2740 then 2 else 1) else (if x<2788 then 3 else 4))) else (if x<3238 then (if x<3178 then (if x<3132 then 4 else 3) else (if x<3188 then 0 else 1)) else (if x<3304 then (if x<3256 then 3 else 0) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4887 : Finset ℕ := ([40,252,1596,1644,1650,1702,1720,1768,2606,2730,2740,2788,3130,3178,3188,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4887 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4887 4 (fun x => (if x<2606 then (if x<1650 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1720 then (if x<1702 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3130 then (if x<2740 then (if x<2730 then 2 else 3) else (if x<2788 then 2 else 3)) else (if x<3188 then (if x<3178 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4888 : Finset ℕ := ([40,48,250,252,1594,1596,1644,1650,1702,1720,1768,1776,2606,2614,2680,2730,2732,2738,2740,2786,2788,3130,3132,3178,3186,3188,3238,3256,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4888 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4888 3186 4
  · have he : independentCachedBranchMembers4888.erase 3186=independentCachedBranchMembers4886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4886
  · have he : independentCachedBranchMembers4888.filter (independentCachedEdge 3186)=independentCachedBranchMembers4887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4887
def independentCachedBranchMembers4889 : Finset ℕ := ([48,250,1594,1644,1650,1702,1720,1776,2614,2730,2740,2786,3132,3178,3188,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4889 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4889 4 (fun x => (if x<2614 then (if x<1650 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1720 then (if x<1702 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3132 then (if x<2740 then (if x<2730 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3188 then (if x<3178 then 3 else 3) else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4890 : Finset ℕ := ([40,48,250,252,1594,1596,1644,1650,1702,1720,1768,1776,2606,2614,2680,2730,2732,2738,2740,2786,2788,3130,3132,3178,3180,3186,3188,3238,3256,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4890 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4890 3180 4
  · have he : independentCachedBranchMembers4890.erase 3180=independentCachedBranchMembers4888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4888
  · have he : independentCachedBranchMembers4890.filter (independentCachedEdge 3180)=independentCachedBranchMembers4889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4889
def independentCachedBranchMembers4891 : Finset ℕ := ([40,48,250,252,1594,1596,1768,1776,2606,2614,2786,2788,3130,3132,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4891 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4891 4 (fun x => (if x<2606 then (if x<1594 then (if x<250 then (if x<48 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1768 then (if x<1596 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3130 then (if x<2786 then (if x<2614 then 2 else 3) else (if x<2788 then 2 else 3)) else (if x<3304 then (if x<3132 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4892 : Finset ℕ := ([40,48,250,252,1594,1596,1644,1650,1702,1720,1768,1776,2606,2614,2662,2680,2730,2732,2738,2740,2786,2788,3130,3132,3178,3180,3186,3188,3238,3256,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4892 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4892 2662 4
  · have he : independentCachedBranchMembers4892.erase 2662=independentCachedBranchMembers4890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4890
  · have he : independentCachedBranchMembers4892.filter (independentCachedEdge 2662)=independentCachedBranchMembers4891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4891
def independentCachedBranchMembers4893 : Finset ℕ := ([40,48,66,68,136,144,222,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3072,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4893 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4893 222 5
  · have he : independentCachedBranchMembers4893.erase 222=independentCachedBranchMembers4885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4885
  · have he : independentCachedBranchMembers4893.filter (independentCachedEdge 222)=independentCachedBranchMembers4892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4892
def independentCachedBranchMembers4894 : Finset ℕ := ([68,136,144,1614,1622,1644,1650,1690,1692,1702,1720,2650,2652,2662,2702,2710,2730,2732,2738,2740,3150,3158,3178,3188,3226,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4894 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4894 5 (fun x => (if x<2702 then (if x<1690 then (if x<1614 then (if x<136 then 0 else (if x<144 then 0 else 1)) else (if x<1644 then (if x<1622 then 1 else 0) else (if x<1650 then 2 else 2))) else (if x<1720 then (if x<1692 then 0 else (if x<1702 then 1 else 2)) else (if x<2652 then (if x<2650 then 2 else 3) else (if x<2662 then 4 else 0)))) else (if x<3158 then (if x<2732 then (if x<2710 then 3 else (if x<2730 then 4 else 0)) else (if x<2740 then (if x<2738 then 2 else 2) else (if x<3150 then 1 else 3))) else (if x<3226 then (if x<3178 then 4 else (if x<3188 then 1 else 0)) else (if x<3238 then (if x<3228 then 3 else 4) else (if x<3256 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4895 : Finset ℕ := ([68,1644,1690,1702,2652,2702,2710,2730,2738,3188,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4895 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4895 4 (fun x => (if x<2710 then (if x<1702 then (if x<1644 then 0 else (if x<1690 then 0 else 1)) else (if x<2652 then 1 else (if x<2702 then 0 else 1))) else (if x<3188 then (if x<2730 then 2 else (if x<2738 then 2 else 1)) else (if x<3226 then 0 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
