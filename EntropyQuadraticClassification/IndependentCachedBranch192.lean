/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch191
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8928 : Finset ℕ := ([40,48,130,252,1596,1614,1622,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2740,2744,2758,2762,2770,3102,3180,3188,3192,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8928 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8928 2762 4
  · have he : independentCachedBranchMembers8928.erase 2762=independentCachedBranchMembers8926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8926
  · have he : independentCachedBranchMembers8928.filter (independentCachedEdge 2762)=independentCachedBranchMembers8927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8927
def independentCachedBranchMembers8929 : Finset ℕ := ([48,130,1614,1686,1690,1776,2668,2740,2744,2770,3102,3188,3192,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8929 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8929 4 (fun x => (if x<2744 then (if x<1690 then (if x<1614 then (if x<130 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2668 then (if x<1776 then 2 else 2) else (if x<2740 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2770 then 2 else 2) else (if x<3188 then 3 else 0)) else (if x<3270 then (if x<3244 then 3 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8930 : Finset ℕ := ([40,48,130,252,1596,1614,1622,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2732,2740,2744,2758,2762,2770,3102,3180,3188,3192,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8930 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8930 2732 4
  · have he : independentCachedBranchMembers8930.erase 2732=independentCachedBranchMembers8928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8928
  · have he : independentCachedBranchMembers8930.filter (independentCachedEdge 2732)=independentCachedBranchMembers8929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8929
def independentCachedBranchMembers8931 : Finset ℕ := ([40,48,130,252,1614,1622,1690,1764,2668,2676,2744,2758,3180,3188,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8931 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8931 4 (fun x => (if x<2668 then (if x<1614 then (if x<130 then (if x<48 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1690 then (if x<1622 then 2 else 3) else (if x<1764 then 2 else 3))) else (if x<3180 then (if x<2744 then (if x<2676 then 0 else 1) else (if x<2758 then 1 else 0)) else (if x<3256 then (if x<3188 then 2 else 3) else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8932 : Finset ℕ := ([40,48,130,252,1596,1614,1622,1626,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2732,2740,2744,2758,2762,2770,3102,3180,3188,3192,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8932 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8932 1626 4
  · have he : independentCachedBranchMembers8932.erase 1626=independentCachedBranchMembers8930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8930
  · have he : independentCachedBranchMembers8932.filter (independentCachedEdge 1626)=independentCachedBranchMembers8931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8931
def independentCachedBranchMembers8933 : Finset ℕ := ([130,252,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,3102,3180,3188,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8933 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8933 4 (fun x => (if x<2590 then (if x<1690 then (if x<1678 then (if x<252 then 0 else 1) else (if x<1686 then 0 else 2)) else (if x<1768 then (if x<1764 then 3 else 1) else (if x<1776 then 3 else 2))) else (if x<3102 then (if x<2676 then (if x<2668 then 2 else 1) else (if x<2680 then 0 else 2)) else (if x<3188 then (if x<3180 then 3 else 3) else (if x<3192 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8934 : Finset ℕ := ([40,48,66,130,252,1596,1614,1622,1626,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2732,2740,2744,2758,2762,2770,3102,3180,3188,3192,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8934 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8934 66 4
  · have he : independentCachedBranchMembers8934.erase 66=independentCachedBranchMembers8932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8932
  · have he : independentCachedBranchMembers8934.filter (independentCachedEdge 66)=independentCachedBranchMembers8933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8933
def independentCachedBranchMembers8935 : Finset ℕ := ([40,48,1614,1622,1678,1686,1768,1776,2590,2680,2744,2758,3102,3192,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound8935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8935 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8935 4 (fun x => (if x<2590 then (if x<1678 then (if x<1614 then (if x<48 then 0 else 1) else (if x<1622 then 1 else 0)) else (if x<1768 then (if x<1686 then 2 else 3) else (if x<1776 then 2 else 3))) else (if x<3102 then (if x<2744 then (if x<2680 then 2 else 2) else (if x<2758 then 0 else 1)) else (if x<3256 then (if x<3192 then 3 else 3) else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8936 : Finset ℕ := ([36,40,48,66,130,252,1596,1614,1622,1626,1678,1686,1690,1764,1768,1776,2590,2668,2676,2680,2732,2740,2744,2758,2762,2770,3102,3180,3188,3192,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8936 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8936 36 4
  · have he : independentCachedBranchMembers8936.erase 36=independentCachedBranchMembers8934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8934
  · have he : independentCachedBranchMembers8936.filter (independentCachedEdge 36)=independentCachedBranchMembers8935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8935
def independentCachedBranchMembers8937 : Finset ℕ := ([34,36,40,48,66,68,72,80,130,132,136,144,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1678,1686,1690,1692,1762,1764,1768,1776,2560,2590,2662,2666,2668,2674,2676,2680,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound8937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8937 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8937 34 5
  · have he : independentCachedBranchMembers8937.erase 34=independentCachedBranchMembers8913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8913
  · have he : independentCachedBranchMembers8937.filter (independentCachedEdge 34)=independentCachedBranchMembers8936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8936
def independentCachedBranchMembers8938 : Finset ℕ := ([10,12,18,20,34,36,40,48,66,68,72,80,130,132,136,144,160,190,192,222,238,246,250,252,1566,1582,1590,1594,1596,1614,1622,1626,1628,1638,1642,1644,1650,1652,1656,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8938 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8938 1566 6
  · have he : independentCachedBranchMembers8938.erase 1566=independentCachedBranchMembers8484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8484
  · have he : independentCachedBranchMembers8938.filter (independentCachedEdge 1566)=independentCachedBranchMembers8937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8937
def independentCachedBranchMembers8939 : Finset ℕ := ([2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3252,3276,3282,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8939 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8939 6 (fun x => (if x<3158 then (if x<2762 then (if x<2732 then (if x<2676 then (if x<2674 then 0 else 0) else (if x<2726 then 1 else 0)) else (if x<2744 then (if x<2738 then 1 else 1) else (if x<2758 then 0 else 1))) else (if x<3118 then (if x<2776 then (if x<2772 then 0 else 0) else (if x<3072 then 1 else 2)) else (if x<3130 then (if x<3126 then 2 else 3) else (if x<3132 then 4 else (if x<3150 then 5 else 3))))) else (if x<3228 then (if x<3192 then (if x<3164 then (if x<3162 then 2 else 5) else (if x<3174 then 4 else 4)) else (if x<3222 then (if x<3214 then 2 else 4) else (if x<3226 then 5 else 2))) else (if x<3282 then (if x<3252 then (if x<3242 then 3 else 3) else (if x<3276 then 2 else 2)) else (if x<3300 then (if x<3298 then 3 else 2) else (if x<3304 then 3 else (if x<3312 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8940 : Finset ℕ := ([2668,2674,2762,2772,3072,3126,3132,3158,3164,3214,3226,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8940 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8940 5 (fun x => (if x<3158 then (if x<2772 then (if x<2674 then 0 else (if x<2762 then 0 else 0)) else (if x<3126 then (if x<3072 then 0 else 1) else (if x<3132 then 1 else 2))) else (if x<3276 then (if x<3214 then (if x<3164 then 2 else 1) else (if x<3226 then 1 else 2)) else (if x<3300 then (if x<3282 then 0 else 0) else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8941 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3252,3276,3282,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8941 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8941 2666 5
  · have he : independentCachedBranchMembers8941.erase 2666=independentCachedBranchMembers8939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8939
  · have he : independentCachedBranchMembers8941.filter (independentCachedEdge 2666)=independentCachedBranchMembers8940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8940
def independentCachedBranchMembers8942 : Finset ℕ := ([2668,2674,2726,2732,2738,2744,2762,2772,3118,3130,3158,3164,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8942 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8942 5 (fun x => (if x<3158 then (if x<2744 then (if x<2726 then (if x<2674 then 0 else 0) else (if x<2732 then 0 else (if x<2738 then 1 else 1))) else (if x<2772 then (if x<2762 then 0 else 0) else (if x<3118 then 0 else (if x<3130 then 2 else 3)))) else (if x<3252 then (if x<3222 then (if x<3164 then 2 else 3) else (if x<3228 then 3 else (if x<3242 then 2 else 1))) else (if x<3282 then (if x<3276 then 1 else 1) else (if x<3300 then 1 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8943 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3252,3276,3282,3284,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8943 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8943 3284 5
  · have he : independentCachedBranchMembers8943.erase 3284=independentCachedBranchMembers8941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8941
  · have he : independentCachedBranchMembers8943.filter (independentCachedEdge 3284)=independentCachedBranchMembers8942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8942
def independentCachedBranchMembers8944 : Finset ℕ := ([2668,2674,2726,2732,2738,2744,2762,2772,3126,3132,3150,3162,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8944 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8944 5 (fun x => (if x<3150 then (if x<2744 then (if x<2726 then (if x<2674 then 0 else 0) else (if x<2732 then 0 else (if x<2738 then 1 else 1))) else (if x<2772 then (if x<2762 then 0 else 0) else (if x<3126 then 0 else (if x<3132 then 2 else 3)))) else (if x<3252 then (if x<3214 then (if x<3162 then 2 else 3) else (if x<3226 then 3 else (if x<3242 then 2 else 1))) else (if x<3282 then (if x<3276 then 1 else 1) else (if x<3298 then 1 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8945 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3252,3274,3276,3282,3284,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8945 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8945 3274 5
  · have he : independentCachedBranchMembers8945.erase 3274=independentCachedBranchMembers8943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8943
  · have he : independentCachedBranchMembers8945.filter (independentCachedEdge 3274)=independentCachedBranchMembers8944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8944
def independentCachedBranchMembers8946 : Finset ℕ := ([2666,2676,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3222,3226,3242,3252,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8946 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8946 5 (fun x => (if x<3150 then (if x<2762 then (if x<2732 then (if x<2676 then 0 else 0) else (if x<2738 then 0 else (if x<2758 then 0 else 0))) else (if x<2776 then (if x<2772 then 1 else 1) else (if x<3126 then 0 else (if x<3130 then 2 else 3)))) else (if x<3252 then (if x<3222 then (if x<3164 then 2 else 3) else (if x<3226 then 3 else (if x<3242 then 2 else 1))) else (if x<3282 then (if x<3276 then 1 else 1) else (if x<3298 then 1 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8947 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3250,3252,3274,3276,3282,3284,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8947 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8947 3250 5
  · have he : independentCachedBranchMembers8947.erase 3250=independentCachedBranchMembers8945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8945
  · have he : independentCachedBranchMembers8947.filter (independentCachedEdge 3250)=independentCachedBranchMembers8946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8946
def independentCachedBranchMembers8948 : Finset ℕ := ([2666,2676,2732,2738,2758,2762,2772,2776,3118,3132,3158,3162,3214,3228,3242,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8948 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8948 5 (fun x => (if x<3158 then (if x<2762 then (if x<2732 then (if x<2676 then 0 else 0) else (if x<2738 then 0 else (if x<2758 then 0 else 0))) else (if x<2776 then (if x<2772 then 1 else 1) else (if x<3118 then 0 else (if x<3132 then 2 else 3)))) else (if x<3252 then (if x<3214 then (if x<3162 then 2 else 3) else (if x<3228 then 3 else (if x<3242 then 2 else 1))) else (if x<3282 then (if x<3276 then 1 else 1) else (if x<3300 then 1 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8949 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8949 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8949 3244 5
  · have he : independentCachedBranchMembers8949.erase 3244=independentCachedBranchMembers8947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8947
  · have he : independentCachedBranchMembers8949.filter (independentCachedEdge 3244)=independentCachedBranchMembers8948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8948
def independentCachedBranchMembers8950 : Finset ℕ := ([2666,2668,2674,2676,2732,2738,2758,2776,3118,3126,3162,3164,3174,3192,3226,3228,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8950 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8950 5 (fun x => (if x<3164 then (if x<2738 then (if x<2674 then (if x<2668 then 0 else 1) else (if x<2676 then 1 else (if x<2732 then 0 else 0))) else (if x<3118 then (if x<2758 then 0 else (if x<2776 then 0 else 0)) else (if x<3126 then 2 else (if x<3162 then 3 else 2)))) else (if x<3274 then (if x<3192 then (if x<3174 then 3 else 1) else (if x<3226 then 1 else (if x<3228 then 3 else 2))) else (if x<3284 then (if x<3276 then 4 else (if x<3282 then 1 else 1)) else (if x<3304 then 4 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8951 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8951 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8951 3288 5
  · have he : independentCachedBranchMembers8951.erase 3288=independentCachedBranchMembers8949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8949
  · have he : independentCachedBranchMembers8951.filter (independentCachedEdge 3288)=independentCachedBranchMembers8950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8950
def independentCachedBranchMembers8952 : Finset ℕ := ([2666,2668,2674,2676,2732,2738,2758,2776,3130,3132,3150,3158,3174,3192,3214,3222,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound8952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8952 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8952 5 (fun x => (if x<3158 then (if x<2738 then (if x<2674 then (if x<2668 then 0 else 1) else (if x<2676 then 1 else (if x<2732 then 0 else 0))) else (if x<3130 then (if x<2758 then 0 else (if x<2776 then 0 else 0)) else (if x<3132 then 2 else (if x<3150 then 3 else 2)))) else (if x<3274 then (if x<3192 then (if x<3174 then 3 else 1) else (if x<3214 then 1 else (if x<3222 then 3 else 2))) else (if x<3284 then (if x<3276 then 4 else (if x<3282 then 1 else 1)) else (if x<3298 then 4 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8953 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3244,3250,3252,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8953 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8953 3270 5
  · have he : independentCachedBranchMembers8953.erase 3270=independentCachedBranchMembers8951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8951
  · have he : independentCachedBranchMembers8953.filter (independentCachedEdge 3270)=independentCachedBranchMembers8952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8952
def independentCachedBranchMembers8954 : Finset ℕ := ([2668,2674,2726,2744,2758,2762,2772,2776,3126,3130,3158,3162,3174,3192,3214,3228,3244,3250,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8954 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8954 5 (fun x => (if x<3162 then (if x<2762 then (if x<2726 then (if x<2674 then 0 else 0) else (if x<2744 then 0 else (if x<2758 then 0 else 1))) else (if x<3126 then (if x<2772 then 0 else (if x<2776 then 0 else 1)) else (if x<3130 then 2 else (if x<3158 then 3 else 3)))) else (if x<3244 then (if x<3192 then (if x<3174 then 2 else 1) else (if x<3214 then 1 else (if x<3228 then 2 else 3))) else (if x<3282 then (if x<3250 then 4 else (if x<3276 then 4 else 1)) else (if x<3298 then 1 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8955 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3186,3192,3214,3222,3226,3228,3242,3244,3250,3252,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8955 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8955 3186 5
  · have he : independentCachedBranchMembers8955.erase 3186=independentCachedBranchMembers8953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8953
  · have he : independentCachedBranchMembers8955.filter (independentCachedEdge 3186)=independentCachedBranchMembers8954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8954
def independentCachedBranchMembers8956 : Finset ℕ := ([2668,2674,2726,2744,2758,2762,2772,2776,3118,3132,3150,3164,3174,3192,3222,3226,3244,3250,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8956 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8956 5 (fun x => (if x<3164 then (if x<2762 then (if x<2726 then (if x<2674 then 0 else 0) else (if x<2744 then 0 else (if x<2758 then 0 else 1))) else (if x<3118 then (if x<2772 then 0 else (if x<2776 then 0 else 1)) else (if x<3132 then 2 else (if x<3150 then 3 else 3)))) else (if x<3244 then (if x<3192 then (if x<3174 then 2 else 1) else (if x<3222 then 1 else (if x<3226 then 2 else 3))) else (if x<3282 then (if x<3250 then 4 else (if x<3276 then 4 else 1)) else (if x<3300 then 1 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8957 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3180,3186,3192,3214,3222,3226,3228,3242,3244,3250,3252,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8957 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8957 3180 5
  · have he : independentCachedBranchMembers8957.erase 3180=independentCachedBranchMembers8955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8955
  · have he : independentCachedBranchMembers8957.filter (independentCachedEdge 3180)=independentCachedBranchMembers8956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8956
def independentCachedBranchMembers8958 : Finset ℕ := ([2666,2668,2674,2676,2726,2744,2762,2772,3130,3132,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3270,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8958 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8958 5 (fun x => (if x<3174 then (if x<2762 then (if x<2676 then (if x<2668 then 0 else (if x<2674 then 1 else 1)) else (if x<2726 then 0 else (if x<2744 then 0 else 0))) else (if x<3132 then (if x<2772 then 1 else (if x<3130 then 1 else 2)) else (if x<3150 then 3 else (if x<3158 then 2 else 3)))) else (if x<3250 then (if x<3228 then (if x<3192 then 0 else (if x<3226 then 0 else 3)) else (if x<3242 then 2 else (if x<3244 then 0 else 4))) else (if x<3288 then (if x<3252 then 4 else (if x<3270 then 0 else 4)) else (if x<3304 then 4 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8959 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3180,3186,3192,3214,3222,3226,3228,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8959 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8959 3256 5
  · have he : independentCachedBranchMembers8959.erase 3256=independentCachedBranchMembers8957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8957
  · have he : independentCachedBranchMembers8959.filter (independentCachedEdge 3256)=independentCachedBranchMembers8958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8958
end EntropyDesigns.QuadraticRefinement
