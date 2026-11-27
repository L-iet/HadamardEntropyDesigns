/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch65
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4896 : Finset ℕ := ([66,68,136,144,1614,1622,1644,1650,1690,1692,1702,1720,2650,2652,2662,2702,2710,2730,2732,2738,2740,3150,3158,3178,3188,3226,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4896 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4896 66 4
  · have he : independentCachedBranchMembers4896.erase 66=independentCachedBranchMembers4894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4894
  · have he : independentCachedBranchMembers4896.filter (independentCachedEdge 66)=independentCachedBranchMembers4895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4895
def independentCachedBranchMembers4897 : Finset ℕ := ([68,144,1614,1644,1650,1690,1702,1720,2652,2710,2730,2740,3158,3178,3188,3228] : List ℕ).toFinset
theorem independentCachedBranchBound4897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4897 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4897 4 (fun x => (if x<2652 then (if x<1650 then (if x<1614 then (if x<144 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1702 then (if x<1690 then 1 else 0) else (if x<1720 then 1 else 1))) else (if x<3158 then (if x<2730 then (if x<2710 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3188 then (if x<3178 then 2 else 3) else (if x<3228 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4898 : Finset ℕ := ([66,68,136,144,1614,1622,1644,1650,1690,1692,1702,1720,2650,2652,2662,2702,2710,2730,2732,2738,2740,3150,3158,3178,3186,3188,3226,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4898 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4898 3186 4
  · have he : independentCachedBranchMembers4898.erase 3186=independentCachedBranchMembers4896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4896
  · have he : independentCachedBranchMembers4898.filter (independentCachedEdge 3186)=independentCachedBranchMembers4897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4897
def independentCachedBranchMembers4899 : Finset ℕ := ([66,136,1622,1644,1650,1692,1702,1720,2650,2702,2730,2740,3150,3178,3188,3226] : List ℕ).toFinset
theorem independentCachedBranchBound4899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4899 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4899 4 (fun x => (if x<2650 then (if x<1650 then (if x<1622 then (if x<136 then 0 else 0) else (if x<1644 then 0 else 1)) else (if x<1702 then (if x<1692 then 1 else 0) else (if x<1720 then 1 else 1))) else (if x<3150 then (if x<2730 then (if x<2702 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3188 then (if x<3178 then 2 else 3) else (if x<3226 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4900 : Finset ℕ := ([66,68,136,144,1614,1622,1644,1650,1690,1692,1702,1720,2650,2652,2662,2702,2710,2730,2732,2738,2740,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4900 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4900 3180 4
  · have he : independentCachedBranchMembers4900.erase 3180=independentCachedBranchMembers4898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4898
  · have he : independentCachedBranchMembers4900.filter (independentCachedEdge 3180)=independentCachedBranchMembers4899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4899
def independentCachedBranchMembers4901 : Finset ℕ := ([66,68,136,144,1614,1622,1690,1692,2650,2652,2702,2710,3150,3158,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound4901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4901 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4901 4 (fun x => (if x<2650 then (if x<1614 then (if x<136 then (if x<68 then 0 else 1) else (if x<144 then 0 else 1)) else (if x<1690 then (if x<1622 then 1 else 0) else (if x<1692 then 1 else 0))) else (if x<3150 then (if x<2702 then (if x<2652 then 2 else 3) else (if x<2710 then 2 else 3)) else (if x<3226 then (if x<3158 then 2 else 3) else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4902 : Finset ℕ := ([66,68,136,144,1614,1622,1644,1650,1690,1692,1702,1720,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4902 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4902 2680 4
  · have he : independentCachedBranchMembers4902.erase 2680=independentCachedBranchMembers4900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4900
  · have he : independentCachedBranchMembers4902.filter (independentCachedEdge 2680)=independentCachedBranchMembers4901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4901
def independentCachedBranchMembers4903 : Finset ℕ := ([40,48,66,68,136,144,192,222,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3072,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4903 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4903 192 5
  · have he : independentCachedBranchMembers4903.erase 192=independentCachedBranchMembers4893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4893
  · have he : independentCachedBranchMembers4903.filter (independentCachedEdge 192)=independentCachedBranchMembers4902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4902
def independentCachedBranchMembers4904 : Finset ℕ := ([144,252,1596,1614,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2702,2740,2758,2776,2786,3132,3150,3178,3188,3228,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4904 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4904 5 (fun x => (if x<2680 then (if x<1720 then (if x<1614 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 0 else 1))) else (if x<1776 then (if x<1738 then 2 else (if x<1748 then 2 else 1)) else (if x<2652 then (if x<2606 then 0 else 1) else (if x<2662 then 1 else 3)))) else (if x<3150 then (if x<2758 then (if x<2702 then 3 else (if x<2740 then 4 else 0)) else (if x<2786 then (if x<2776 then 1 else 0) else (if x<3132 then 4 else 2))) else (if x<3228 then (if x<3178 then 2 else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 4 else 3) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4905 : Finset ℕ := ([252,1702,1748,1776,2606,2652,2680,2702,2776,3188,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4905 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4905 4 (fun x => (if x<2680 then (if x<1776 then (if x<1702 then 0 else (if x<1748 then 1 else 0)) else (if x<2606 then 1 else (if x<2652 then 1 else 0))) else (if x<3188 then (if x<2702 then 1 else (if x<2776 then 2 else 2)) else (if x<3238 then 0 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4906 : Finset ℕ := ([66,144,252,1596,1614,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2702,2740,2758,2776,2786,3132,3150,3178,3188,3228,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4906 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4906 66 4
  · have he : independentCachedBranchMembers4906.erase 66=independentCachedBranchMembers4904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4904
  · have he : independentCachedBranchMembers4906.filter (independentCachedEdge 66)=independentCachedBranchMembers4905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4905
def independentCachedBranchMembers4907 : Finset ℕ := ([144,1692,1702,1748,2606,2652,2662,2776,2786,3178,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4907 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4907 4 (fun x => (if x<2662 then (if x<1748 then (if x<1692 then 0 else (if x<1702 then 0 else 1)) else (if x<2606 then 1 else (if x<2652 then 1 else 1))) else (if x<3178 then (if x<2776 then 0 else (if x<2786 then 2 else 2)) else (if x<3228 then 0 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4908 : Finset ℕ := ([48,66,144,252,1596,1614,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2702,2740,2758,2776,2786,3132,3150,3178,3188,3228,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4908 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4908 48 4
  · have he : independentCachedBranchMembers4908.erase 48=independentCachedBranchMembers4906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4906
  · have he : independentCachedBranchMembers4908.filter (independentCachedEdge 48)=independentCachedBranchMembers4907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4907
def independentCachedBranchMembers4909 : Finset ℕ := ([48,66,1596,1614,1702,1720,1738,1748,2662,2680,2702,2786,3178,3188,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4909 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4909 4 (fun x => (if x<2662 then (if x<1702 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1738 then (if x<1720 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2702 then (if x<2680 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3188 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4910 : Finset ℕ := ([48,66,144,252,1596,1614,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2702,2740,2758,2776,2786,3132,3150,3178,3188,3228,3238,3256,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4910 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4910 3284 4
  · have he : independentCachedBranchMembers4910.erase 3284=independentCachedBranchMembers4908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4908
  · have he : independentCachedBranchMembers4910.filter (independentCachedEdge 3284)=independentCachedBranchMembers4909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4909
def independentCachedBranchMembers4911 : Finset ℕ := ([144,252,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,3132,3150,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound4911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4911 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4911 4 (fun x => (if x<2606 then (if x<1720 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3132 then (if x<2662 then (if x<2652 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3178 then (if x<3150 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4912 : Finset ℕ := ([48,66,144,252,1596,1614,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2702,2740,2758,2776,2786,3132,3150,3178,3188,3228,3238,3256,3274,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4912 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4912 3274 4
  · have he : independentCachedBranchMembers4912.erase 3274=independentCachedBranchMembers4910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4910
  · have he : independentCachedBranchMembers4912.filter (independentCachedEdge 3274)=independentCachedBranchMembers4911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4911
def independentCachedBranchMembers4913 : Finset ℕ := ([48,66,144,252,1596,1614,1692,1776,2606,2652,2702,2786,3132,3150,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4913 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4913 4 (fun x => (if x<2606 then (if x<1596 then (if x<144 then (if x<66 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1692 then (if x<1614 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3132 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3150 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4914 : Finset ℕ := ([48,66,144,252,1596,1614,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2702,2730,2740,2758,2776,2786,3132,3150,3178,3188,3228,3238,3256,3274,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4914 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4914 2730 4
  · have he : independentCachedBranchMembers4914.erase 2730=independentCachedBranchMembers4912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4912
  · have he : independentCachedBranchMembers4914.filter (independentCachedEdge 2730)=independentCachedBranchMembers4913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4913
def independentCachedBranchMembers4915 : Finset ℕ := ([18,40,48,66,68,136,144,192,222,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3072,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4915 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4915 18 5
  · have he : independentCachedBranchMembers4915.erase 18=independentCachedBranchMembers4903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4903
  · have he : independentCachedBranchMembers4915.filter (independentCachedEdge 18)=independentCachedBranchMembers4914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4914
def independentCachedBranchMembers4916 : Finset ℕ := ([136,250,1594,1622,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2710,2730,2758,2776,2788,3130,3158,3178,3188,3226,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4916 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4916 5 (fun x => (if x<2680 then (if x<1720 then (if x<1622 then (if x<250 then 0 else (if x<1594 then 0 else 1)) else (if x<1690 then 1 else (if x<1702 then 0 else 1))) else (if x<1768 then (if x<1738 then 2 else (if x<1748 then 1 else 2)) else (if x<2650 then (if x<2614 then 0 else 1) else (if x<2662 then 1 else 3)))) else (if x<3158 then (if x<2758 then (if x<2710 then 3 else (if x<2730 then 4 else 0)) else (if x<2788 then (if x<2776 then 1 else 0) else (if x<3130 then 4 else 2))) else (if x<3226 then (if x<3178 then 2 else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 4 else 3) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4917 : Finset ℕ := ([250,1702,1738,1768,2614,2650,2680,2710,2776,3178,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4917 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4917 4 (fun x => (if x<2680 then (if x<1768 then (if x<1702 then 0 else (if x<1738 then 1 else 0)) else (if x<2614 then 1 else (if x<2650 then 1 else 0))) else (if x<3178 then (if x<2710 then 1 else (if x<2776 then 2 else 2)) else (if x<3238 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4918 : Finset ℕ := ([68,136,250,1594,1622,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2710,2730,2758,2776,2788,3130,3158,3178,3188,3226,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4918 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4918 68 4
  · have he : independentCachedBranchMembers4918.erase 68=independentCachedBranchMembers4916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4916
  · have he : independentCachedBranchMembers4918.filter (independentCachedEdge 68)=independentCachedBranchMembers4917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4917
def independentCachedBranchMembers4919 : Finset ℕ := ([136,1690,1702,1738,2614,2650,2662,2776,2788,3188,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4919 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4919 4 (fun x => (if x<2662 then (if x<1738 then (if x<1690 then 0 else (if x<1702 then 0 else 1)) else (if x<2614 then 1 else (if x<2650 then 1 else 1))) else (if x<3188 then (if x<2776 then 0 else (if x<2788 then 2 else 2)) else (if x<3226 then 0 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4920 : Finset ℕ := ([40,68,136,250,1594,1622,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2710,2730,2758,2776,2788,3130,3158,3178,3188,3226,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4920 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4920 40 4
  · have he : independentCachedBranchMembers4920.erase 40=independentCachedBranchMembers4918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4918
  · have he : independentCachedBranchMembers4920.filter (independentCachedEdge 40)=independentCachedBranchMembers4919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4919
def independentCachedBranchMembers4921 : Finset ℕ := ([136,250,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,3130,3158,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound4921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4921 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4921 4 (fun x => (if x<2614 then (if x<1720 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3130 then (if x<2662 then (if x<2650 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3178 then (if x<3158 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4922 : Finset ℕ := ([40,68,136,250,1594,1622,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2710,2730,2758,2776,2788,3130,3158,3178,3188,3226,3238,3256,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4922 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4922 3284 4
  · have he : independentCachedBranchMembers4922.erase 3284=independentCachedBranchMembers4920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4920
  · have he : independentCachedBranchMembers4922.filter (independentCachedEdge 3284)=independentCachedBranchMembers4921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4921
def independentCachedBranchMembers4923 : Finset ℕ := ([40,68,1594,1622,1702,1720,1738,1748,2662,2680,2710,2788,3178,3188,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4923 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4923 4 (fun x => (if x<2662 then (if x<1702 then (if x<1594 then (if x<68 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1738 then (if x<1720 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2710 then (if x<2680 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3188 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4924 : Finset ℕ := ([40,68,136,250,1594,1622,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2710,2730,2758,2776,2788,3130,3158,3178,3188,3226,3238,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4924 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4924 3274 4
  · have he : independentCachedBranchMembers4924.erase 3274=independentCachedBranchMembers4922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4922
  · have he : independentCachedBranchMembers4924.filter (independentCachedEdge 3274)=independentCachedBranchMembers4923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4923
def independentCachedBranchMembers4925 : Finset ℕ := ([40,68,136,250,1594,1622,1690,1768,2614,2650,2710,2788,3130,3158,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4925 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4925 4 (fun x => (if x<2614 then (if x<1594 then (if x<136 then (if x<68 then 0 else 0) else (if x<250 then 1 else 1)) else (if x<1690 then (if x<1622 then 0 else 0) else (if x<1768 then 1 else 1))) else (if x<3130 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3158 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4926 : Finset ℕ := ([40,68,136,250,1594,1622,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2710,2730,2740,2758,2776,2788,3130,3158,3178,3188,3226,3238,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4926 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4926 2740 4
  · have he : independentCachedBranchMembers4926.erase 2740=independentCachedBranchMembers4924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4924
  · have he : independentCachedBranchMembers4926.filter (independentCachedEdge 2740)=independentCachedBranchMembers4925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4925
def independentCachedBranchMembers4927 : Finset ℕ := ([12,18,40,48,66,68,136,144,192,222,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3072,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4927 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4927 12 5
  · have he : independentCachedBranchMembers4927.erase 12=independentCachedBranchMembers4915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4915
  · have he : independentCachedBranchMembers4927.filter (independentCachedEdge 12)=independentCachedBranchMembers4926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4926
end EntropyDesigns.QuadraticRefinement
