/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch66
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4928 : Finset ℕ := ([144,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3130,3150,3178,3188,3228,3238,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4928 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4928 5 (fun x => (if x<2732 then (if x<1690 then (if x<1622 then (if x<250 then 0 else (if x<1596 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1776 then (if x<1738 then 0 else (if x<1748 then 2 else 2)) else (if x<2650 then (if x<2606 then 0 else 3) else (if x<2710 then 3 else 3)))) else (if x<3178 then (if x<2776 then (if x<2738 then 1 else (if x<2758 then 0 else 1)) else (if x<3130 then (if x<2786 then 0 else 3) else (if x<3150 then 4 else 4))) else (if x<3238 then (if x<3188 then 2 else (if x<3228 then 2 else 4)) else (if x<3282 then (if x<3256 then 3 else 0) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4929 : Finset ℕ := ([1644,1690,1748,1776,2606,2710,2738,2776,3130,3188,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4929 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4929 4 (fun x => (if x<2738 then (if x<1776 then (if x<1690 then 0 else (if x<1748 then 1 else 0)) else (if x<2606 then 1 else (if x<2710 then 0 else 0))) else (if x<3188 then (if x<2776 then 1 else (if x<3130 then 1 else 2)) else (if x<3238 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4930 : Finset ℕ := ([66,144,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3130,3150,3178,3188,3228,3238,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4930 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4930 66 4
  · have he : independentCachedBranchMembers4930.erase 66=independentCachedBranchMembers4928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4928
  · have he : independentCachedBranchMembers4930.filter (independentCachedEdge 66)=independentCachedBranchMembers4929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4929
def independentCachedBranchMembers4931 : Finset ℕ := ([1650,1690,1738,1776,2650,2738,2776,2786,3150,3188,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4931 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4931 4 (fun x => (if x<2776 then (if x<1776 then (if x<1690 then 0 else (if x<1738 then 0 else 1)) else (if x<2650 then 1 else (if x<2738 then 0 else 0))) else (if x<3188 then (if x<2786 then 1 else (if x<3150 then 1 else 2)) else (if x<3228 then 2 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4932 : Finset ℕ := ([40,66,144,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3130,3150,3178,3188,3228,3238,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4932 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4932 40 4
  · have he : independentCachedBranchMembers4932.erase 40=independentCachedBranchMembers4930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4930
  · have he : independentCachedBranchMembers4932.filter (independentCachedEdge 40)=independentCachedBranchMembers4931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4931
def independentCachedBranchMembers4933 : Finset ℕ := ([40,66,144,250,1596,1622,1690,1776,2606,2650,2710,2786,3130,3150,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4933 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4933 4 (fun x => (if x<2606 then (if x<1596 then (if x<144 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3130 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4934 : Finset ℕ := ([40,66,144,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4934 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4934 3276 4
  · have he : independentCachedBranchMembers4934.erase 3276=independentCachedBranchMembers4932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4932
  · have he : independentCachedBranchMembers4934.filter (independentCachedEdge 3276)=independentCachedBranchMembers4933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4933
def independentCachedBranchMembers4935 : Finset ℕ := ([40,66,144,250,1644,1650,1738,1748,2732,2738,2758,2776,3130,3150,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4935 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4935 4 (fun x => (if x<2732 then (if x<1644 then (if x<144 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1738 then (if x<1650 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3130 then (if x<2758 then (if x<2738 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4936 : Finset ℕ := ([40,66,144,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4936 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4936 3102 4
  · have he : independentCachedBranchMembers4936.erase 3102=independentCachedBranchMembers4934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4934
  · have he : independentCachedBranchMembers4936.filter (independentCachedEdge 3102)=independentCachedBranchMembers4935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4935
def independentCachedBranchMembers4937 : Finset ℕ := ([1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound4937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4937 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4937 4 (fun x => (if x<2606 then (if x<1690 then (if x<1644 then (if x<1622 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<2738 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2776 then (if x<2758 then 3 else 3) else (if x<2786 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4938 : Finset ℕ := ([40,66,144,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4938 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4938 3072 4
  · have he : independentCachedBranchMembers4938.erase 3072=independentCachedBranchMembers4936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4936
  · have he : independentCachedBranchMembers4938.filter (independentCachedEdge 3072)=independentCachedBranchMembers4937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4937
def independentCachedBranchMembers4939 : Finset ℕ := ([40,250,1596,1644,1650,1776,2606,2732,2738,2786,3130,3178,3188,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4939 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4939 4 (fun x => (if x<2738 then (if x<1650 then (if x<1596 then (if x<250 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2732 then 2 else 1))) else (if x<3188 then (if x<3130 then (if x<2786 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4940 : Finset ℕ := ([40,66,144,222,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4940 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4940 222 4
  · have he : independentCachedBranchMembers4940.erase 222=independentCachedBranchMembers4938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4938
  · have he : independentCachedBranchMembers4940.filter (independentCachedEdge 222)=independentCachedBranchMembers4939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4939
def independentCachedBranchMembers4941 : Finset ℕ := ([66,144,1622,1644,1650,1690,2650,2710,2732,2738,3150,3178,3188,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4941 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4941 4 (fun x => (if x<2732 then (if x<1650 then (if x<1622 then (if x<144 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<2650 then (if x<1690 then 2 else 2) else (if x<2710 then 2 else 1))) else (if x<3188 then (if x<3150 then (if x<2738 then 1 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3228 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4942 : Finset ℕ := ([40,66,144,192,222,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4942 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4942 192 4
  · have he : independentCachedBranchMembers4942.erase 192=independentCachedBranchMembers4940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4940
  · have he : independentCachedBranchMembers4942.filter (independentCachedEdge 192)=independentCachedBranchMembers4941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4941
def independentCachedBranchMembers4943 : Finset ℕ := ([66,144,1596,1738,1748,1776,2606,2758,2776,2786,3150,3178,3188,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4943 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4943 4 (fun x => (if x<2776 then (if x<1748 then (if x<1596 then (if x<144 then 0 else 0) else (if x<1738 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2758 then 1 else 1))) else (if x<3188 then (if x<3150 then (if x<2786 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3228 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4944 : Finset ℕ := ([18,40,66,144,192,222,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4944 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4944 18 4
  · have he : independentCachedBranchMembers4944.erase 18=independentCachedBranchMembers4942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4942
  · have he : independentCachedBranchMembers4944.filter (independentCachedEdge 18)=independentCachedBranchMembers4943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4943
def independentCachedBranchMembers4945 : Finset ℕ := ([40,250,1622,1690,1738,1748,2650,2710,2758,2776,3130,3178,3188,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4945 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4945 4 (fun x => (if x<2758 then (if x<1738 then (if x<1622 then (if x<250 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1748 then 2 else 2) else (if x<2710 then 1 else 1))) else (if x<3188 then (if x<3130 then (if x<2776 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4946 : Finset ℕ := ([12,18,40,66,144,192,222,250,1596,1622,1644,1650,1690,1738,1748,1776,2606,2650,2710,2732,2738,2758,2776,2786,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4946 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4946 12 4
  · have he : independentCachedBranchMembers4946.erase 12=independentCachedBranchMembers4944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4944
  · have he : independentCachedBranchMembers4946.filter (independentCachedEdge 12)=independentCachedBranchMembers4945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4945
def independentCachedBranchMembers4947 : Finset ℕ := ([12,18,40,48,66,68,136,144,192,222,250,252,1594,1596,1614,1622,1644,1650,1652,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3072,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4947 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4947 1652 5
  · have he : independentCachedBranchMembers4947.erase 1652=independentCachedBranchMembers4927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4927
  · have he : independentCachedBranchMembers4947.filter (independentCachedEdge 1652)=independentCachedBranchMembers4946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4946
def independentCachedBranchMembers4948 : Finset ℕ := ([136,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3132,3158,3178,3188,3226,3238,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4948 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4948 5 (fun x => (if x<2732 then (if x<1692 then (if x<1614 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1768 then (if x<1738 then 0 else (if x<1748 then 2 else 2)) else (if x<2652 then (if x<2614 then 0 else 3) else (if x<2702 then 3 else 3)))) else (if x<3178 then (if x<2776 then (if x<2738 then 0 else (if x<2758 then 1 else 1)) else (if x<3132 then (if x<2788 then 0 else 3) else (if x<3158 then 4 else 4))) else (if x<3238 then (if x<3188 then 2 else (if x<3226 then 2 else 4)) else (if x<3276 then (if x<3256 then 3 else 0) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4949 : Finset ℕ := ([1650,1692,1738,1768,2614,2702,2732,2776,3132,3178,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4949 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4949 4 (fun x => (if x<2732 then (if x<1768 then (if x<1692 then 0 else (if x<1738 then 1 else 0)) else (if x<2614 then 1 else (if x<2702 then 0 else 0))) else (if x<3178 then (if x<2776 then 1 else (if x<3132 then 1 else 2)) else (if x<3238 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4950 : Finset ℕ := ([68,136,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3132,3158,3178,3188,3226,3238,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4950 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4950 68 4
  · have he : independentCachedBranchMembers4950.erase 68=independentCachedBranchMembers4948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4948
  · have he : independentCachedBranchMembers4950.filter (independentCachedEdge 68)=independentCachedBranchMembers4949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4949
def independentCachedBranchMembers4951 : Finset ℕ := ([1644,1692,1748,1768,2652,2732,2776,2788,3158,3178,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4951 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4951 4 (fun x => (if x<2776 then (if x<1768 then (if x<1692 then 0 else (if x<1748 then 0 else 1)) else (if x<2652 then 1 else (if x<2732 then 0 else 0))) else (if x<3178 then (if x<2788 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4952 : Finset ℕ := ([48,68,136,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3132,3158,3178,3188,3226,3238,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4952 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4952 48 4
  · have he : independentCachedBranchMembers4952.erase 48=independentCachedBranchMembers4950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4950
  · have he : independentCachedBranchMembers4952.filter (independentCachedEdge 48)=independentCachedBranchMembers4951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4951
def independentCachedBranchMembers4953 : Finset ℕ := ([48,68,136,252,1594,1614,1692,1768,2614,2652,2702,2788,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4953 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4953 4 (fun x => (if x<2614 then (if x<1594 then (if x<136 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3132 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4954 : Finset ℕ := ([48,68,136,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4954 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4954 3282 4
  · have he : independentCachedBranchMembers4954.erase 3282=independentCachedBranchMembers4952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4952
  · have he : independentCachedBranchMembers4954.filter (independentCachedEdge 3282)=independentCachedBranchMembers4953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4953
def independentCachedBranchMembers4955 : Finset ℕ := ([48,68,136,252,1644,1650,1738,1748,2732,2738,2758,2776,3132,3158,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4955 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4955 4 (fun x => (if x<2732 then (if x<1644 then (if x<136 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1738 then (if x<1650 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3132 then (if x<2758 then (if x<2738 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4956 : Finset ℕ := ([48,68,136,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4956 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4956 3102 4
  · have he : independentCachedBranchMembers4956.erase 3102=independentCachedBranchMembers4954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4954
  · have he : independentCachedBranchMembers4956.filter (independentCachedEdge 3102)=independentCachedBranchMembers4955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4955
def independentCachedBranchMembers4957 : Finset ℕ := ([1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788] : List ℕ).toFinset
theorem independentCachedBranchBound4957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4957 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4957 4 (fun x => (if x<2614 then (if x<1692 then (if x<1644 then (if x<1614 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<2738 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2776 then (if x<2758 then 3 else 3) else (if x<2788 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4958 : Finset ℕ := ([48,68,136,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4958 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4958 3072 4
  · have he : independentCachedBranchMembers4958.erase 3072=independentCachedBranchMembers4956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4956
  · have he : independentCachedBranchMembers4958.filter (independentCachedEdge 3072)=independentCachedBranchMembers4957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4957
def independentCachedBranchMembers4959 : Finset ℕ := ([48,252,1594,1644,1650,1768,2614,2732,2738,2788,3132,3178,3188,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4959 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4959 4 (fun x => (if x<2738 then (if x<1650 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2732 then 2 else 2))) else (if x<3188 then (if x<3132 then (if x<2788 then 1 else 1) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
