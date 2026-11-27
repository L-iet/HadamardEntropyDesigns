/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch196
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9088 : Finset ℕ := ([2618,2650,2668,2676,2702,2710,2716,2738,2744,2762,2776,2788,3072,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9088 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9088 2618 4
  · have he : independentCachedBranchMembers9088.erase 2618=independentCachedBranchMembers9086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9086
  · have he : independentCachedBranchMembers9088.filter (independentCachedEdge 2618)=independentCachedBranchMembers9087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9087
def independentCachedBranchMembers9089 : Finset ℕ := ([2618,2650,2668,2676,2702,2710,2744,2776,3132,3164,3178,3186,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9089 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9089 4 (fun x => (if x<3132 then (if x<2702 then (if x<2668 then (if x<2650 then 0 else 1) else (if x<2676 then 0 else 1)) else (if x<2744 then (if x<2710 then 0 else 1) else (if x<2776 then 1 else 0))) else (if x<3238 then (if x<3178 then (if x<3164 then 2 else 3) else (if x<3186 then 2 else 3)) else (if x<3304 then (if x<3270 then 2 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9090 : Finset ℕ := ([2618,2650,2668,2676,2702,2710,2716,2738,2744,2762,2776,2788,3072,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9090 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9090 3298 4
  · have he : independentCachedBranchMembers9090.erase 3298=independentCachedBranchMembers9088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9088
  · have he : independentCachedBranchMembers9090.filter (independentCachedEdge 3298)=independentCachedBranchMembers9089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9089
def independentCachedBranchMembers9091 : Finset ℕ := ([2618,2668,2702,2716,2738,2762,2776,2788,3126,3150,3164,3186,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9091 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9091 4 (fun x => (if x<3126 then (if x<2738 then (if x<2702 then (if x<2668 then 0 else 0) else (if x<2716 then 0 else 1)) else (if x<2776 then (if x<2762 then 1 else 1) else (if x<2788 then 0 else 1))) else (if x<3244 then (if x<3164 then (if x<3150 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3284 then (if x<3270 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9092 : Finset ℕ := ([2618,2650,2668,2676,2702,2710,2716,2738,2744,2762,2776,2788,3072,3126,3132,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9092 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9092 3158 4
  · have he : independentCachedBranchMembers9092.erase 3158=independentCachedBranchMembers9090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9090
  · have he : independentCachedBranchMembers9092.filter (independentCachedEdge 3158)=independentCachedBranchMembers9091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9091
def independentCachedBranchMembers9093 : Finset ℕ := ([2650,2676,2710,2716,2738,2744,2762,2788,3126,3132,3150,3178,3238,3244,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9093 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9093 4 (fun x => (if x<3126 then (if x<2738 then (if x<2710 then (if x<2676 then 0 else 0) else (if x<2716 then 0 else 1)) else (if x<2762 then (if x<2744 then 1 else 0) else (if x<2788 then 1 else 1))) else (if x<3238 then (if x<3150 then (if x<3132 then 2 else 3) else (if x<3178 then 2 else 3)) else (if x<3284 then (if x<3244 then 3 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9094 : Finset ℕ := ([2618,2650,2668,2676,2702,2710,2716,2738,2744,2762,2776,2788,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9094 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9094 3118 4
  · have he : independentCachedBranchMembers9094.erase 3118=independentCachedBranchMembers9092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9092
  · have he : independentCachedBranchMembers9094.filter (independentCachedEdge 3118)=independentCachedBranchMembers9093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9093
def independentCachedBranchMembers9095 : Finset ℕ := ([2614,2618,2620,2638,2650,2652,2666,2668,2674,2676,2702,2710,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9095 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9095 2714 5
  · have he : independentCachedBranchMembers9095.erase 2714=independentCachedBranchMembers9085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9085
  · have he : independentCachedBranchMembers9095.filter (independentCachedEdge 2714)=independentCachedBranchMembers9094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9094
def independentCachedBranchMembers9096 : Finset ℕ := ([2638,2650,2652,2674,2676,2710,2732,2744,2758,2772,2792,3072,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9096 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9096 5 (fun x => (if x<3158 then (if x<2744 then (if x<2674 then (if x<2650 then 0 else (if x<2652 then 1 else 2)) else (if x<2710 then (if x<2676 then 0 else 1) else (if x<2732 then 0 else 2))) else (if x<2792 then (if x<2758 then 1 else (if x<2772 then 2 else 3)) else (if x<3130 then (if x<3072 then 3 else 4) else (if x<3132 then 4 else 2)))) else (if x<3250 then (if x<3192 then (if x<3178 then 0 else (if x<3180 then 0 else 4)) else (if x<3228 then (if x<3214 then 1 else 0) else (if x<3238 then 4 else 2))) else (if x<3276 then (if x<3252 then 0 else (if x<3274 then 1 else 4)) else (if x<3300 then (if x<3288 then 2 else 3) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9097 : Finset ℕ := ([2674,2676,2710,2792,3072,3178,3180,3192,3214,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9097 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9097 4 (fun x => (if x<3180 then (if x<2792 then (if x<2676 then 0 else (if x<2710 then 1 else 0)) else (if x<3072 then 1 else (if x<3178 then 2 else 0))) else (if x<3228 then (if x<3192 then 1 else (if x<3214 then 2 else 0)) else (if x<3300 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9098 : Finset ℕ := ([2614,2638,2650,2652,2674,2676,2710,2732,2744,2758,2772,2792,3072,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9098 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9098 2614 4
  · have he : independentCachedBranchMembers9098.erase 2614=independentCachedBranchMembers9096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9096
  · have he : independentCachedBranchMembers9098.filter (independentCachedEdge 2614)=independentCachedBranchMembers9097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9097
def independentCachedBranchMembers9099 : Finset ℕ := ([2614,2638,2650,2676,2710,2732,2744,2772,3132,3178,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9099 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9099 4 (fun x => (if x<3132 then (if x<2710 then (if x<2650 then (if x<2638 then 0 else 0) else (if x<2676 then 1 else 1)) else (if x<2744 then (if x<2732 then 1 else 0) else (if x<2772 then 1 else 0))) else (if x<3250 then (if x<3228 then (if x<3178 then 2 else 2) else (if x<3238 then 3 else 2)) else (if x<3300 then (if x<3274 then 3 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9100 : Finset ℕ := ([2614,2638,2650,2652,2674,2676,2710,2732,2744,2758,2772,2792,3072,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9100 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9100 3298 4
  · have he : independentCachedBranchMembers9100.erase 3298=independentCachedBranchMembers9098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9098
  · have he : independentCachedBranchMembers9100.filter (independentCachedEdge 3298)=independentCachedBranchMembers9099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9099
def independentCachedBranchMembers9101 : Finset ℕ := ([2614,2638,2652,2674,2732,2758,2772,2792,3130,3180,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9101 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9101 4 (fun x => (if x<3130 then (if x<2732 then (if x<2652 then (if x<2638 then 0 else 0) else (if x<2674 then 1 else 1)) else (if x<2772 then (if x<2758 then 0 else 1) else (if x<2792 then 0 else 1))) else (if x<3250 then (if x<3214 then (if x<3180 then 2 else 2) else (if x<3228 then 2 else 3)) else (if x<3288 then (if x<3274 then 3 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9102 : Finset ℕ := ([2614,2638,2650,2652,2674,2676,2710,2732,2744,2758,2772,2792,3072,3130,3132,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9102 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9102 3226 4
  · have he : independentCachedBranchMembers9102.erase 3226=independentCachedBranchMembers9100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9100
  · have he : independentCachedBranchMembers9102.filter (independentCachedEdge 3226)=independentCachedBranchMembers9101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9101
def independentCachedBranchMembers9103 : Finset ℕ := ([2650,2652,2674,2676,2710,2744,2758,2792,3130,3132,3178,3180,3214,3238,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9103 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9103 4 (fun x => (if x<3130 then (if x<2710 then (if x<2674 then (if x<2652 then 0 else 1) else (if x<2676 then 1 else 0)) else (if x<2758 then (if x<2744 then 0 else 0) else (if x<2792 then 1 else 1))) else (if x<3214 then (if x<3178 then (if x<3132 then 2 else 3) else (if x<3180 then 3 else 2)) else (if x<3288 then (if x<3238 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9104 : Finset ℕ := ([2614,2638,2650,2652,2674,2676,2710,2732,2744,2758,2772,2792,3072,3118,3130,3132,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9104 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9104 3118 4
  · have he : independentCachedBranchMembers9104.erase 3118=independentCachedBranchMembers9102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9102
  · have he : independentCachedBranchMembers9104.filter (independentCachedEdge 3118)=independentCachedBranchMembers9103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9103
def independentCachedBranchMembers9105 : Finset ℕ := ([2614,2618,2620,2638,2646,2650,2652,2666,2668,2674,2676,2702,2710,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9105 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9105 2646 5
  · have he : independentCachedBranchMembers9105.erase 2646=independentCachedBranchMembers9095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9095
  · have he : independentCachedBranchMembers9105.filter (independentCachedEdge 2646)=independentCachedBranchMembers9104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9104
def independentCachedBranchMembers9106 : Finset ℕ := ([2618,2620,2638,2666,2668,2702,2726,2732,2772,2776,2800,3072,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9106 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9106 5 (fun x => (if x<3164 then (if x<2732 then (if x<2666 then (if x<2620 then 0 else (if x<2638 then 1 else 0)) else (if x<2702 then (if x<2668 then 1 else 2) else (if x<2726 then 1 else 0))) else (if x<2800 then (if x<2772 then 3 else (if x<2776 then 2 else 1)) else (if x<3118 then (if x<3072 then 3 else 4) else (if x<3162 then 0 else 0)))) else (if x<3252 then (if x<3192 then (if x<3186 then 2 else (if x<3188 then 3 else 4)) else (if x<3228 then (if x<3222 then 1 else 2) else (if x<3250 then 1 else 0))) else (if x<3274 then (if x<3256 then 3 else (if x<3270 then 4 else 0)) else (if x<3300 then (if x<3276 then 1 else 4) else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9107 : Finset ℕ := ([2618,2620,2726,2776,3072,3162,3164,3192,3228,3256,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9107 4 (fun x => (if x<3164 then (if x<2776 then (if x<2620 then 0 else (if x<2726 then 1 else 0)) else (if x<3072 then 1 else (if x<3162 then 2 else 0))) else (if x<3256 then (if x<3192 then 1 else (if x<3228 then 2 else 2)) else (if x<3270 then 1 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9108 : Finset ℕ := ([2614,2618,2620,2638,2666,2668,2702,2726,2732,2772,2776,2800,3072,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9108 2614 4
  · have he : independentCachedBranchMembers9108.erase 2614=independentCachedBranchMembers9106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9106
  · have he : independentCachedBranchMembers9108.filter (independentCachedEdge 2614)=independentCachedBranchMembers9107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9107
def independentCachedBranchMembers9109 : Finset ℕ := ([2614,2618,2638,2668,2702,2732,2772,2776,3164,3186,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9109 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9109 4 (fun x => (if x<3164 then (if x<2702 then (if x<2638 then (if x<2618 then 0 else 1) else (if x<2668 then 0 else 1)) else (if x<2772 then (if x<2732 then 1 else 0) else (if x<2776 then 0 else 1))) else (if x<3270 then (if x<3228 then (if x<3186 then 2 else 2) else (if x<3250 then 3 else 3)) else (if x<3300 then (if x<3274 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9110 : Finset ℕ := ([2614,2618,2620,2638,2666,2668,2702,2726,2732,2772,2776,2800,3072,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9110 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9110 3298 4
  · have he : independentCachedBranchMembers9110.erase 3298=independentCachedBranchMembers9108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9108
  · have he : independentCachedBranchMembers9110.filter (independentCachedEdge 3298)=independentCachedBranchMembers9109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9109
def independentCachedBranchMembers9111 : Finset ℕ := ([2614,2620,2638,2666,2726,2732,2772,2800,3162,3188,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9111 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9111 4 (fun x => (if x<3162 then (if x<2726 then (if x<2638 then (if x<2620 then 0 else 1) else (if x<2666 then 0 else 1)) else (if x<2772 then (if x<2732 then 1 else 0) else (if x<2800 then 0 else 1))) else (if x<3250 then (if x<3222 then (if x<3188 then 2 else 2) else (if x<3228 then 2 else 3)) else (if x<3274 then (if x<3256 then 3 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9112 : Finset ℕ := ([2614,2618,2620,2638,2666,2668,2702,2726,2732,2772,2776,2800,3072,3118,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9112 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9112 3226 4
  · have he : independentCachedBranchMembers9112.erase 3226=independentCachedBranchMembers9110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9110
  · have he : independentCachedBranchMembers9112.filter (independentCachedEdge 3226)=independentCachedBranchMembers9111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9111
def independentCachedBranchMembers9113 : Finset ℕ := ([2618,2620,2666,2668,2702,2726,2776,2800,3162,3164,3186,3188,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9113 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9113 4 (fun x => (if x<3162 then (if x<2702 then (if x<2666 then (if x<2620 then 0 else 1) else (if x<2668 then 1 else 0)) else (if x<2776 then (if x<2726 then 0 else 1) else (if x<2800 then 0 else 1))) else (if x<3222 then (if x<3186 then (if x<3164 then 2 else 3) else (if x<3188 then 3 else 2)) else (if x<3270 then (if x<3256 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9114 : Finset ℕ := ([2614,2618,2620,2638,2666,2668,2702,2726,2732,2772,2776,2800,3072,3118,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9114 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9114 3158 4
  · have he : independentCachedBranchMembers9114.erase 3158=independentCachedBranchMembers9112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9112
  · have he : independentCachedBranchMembers9114.filter (independentCachedEdge 3158)=independentCachedBranchMembers9113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9113
def independentCachedBranchMembers9115 : Finset ℕ := ([2606,2614,2618,2620,2638,2646,2650,2652,2666,2668,2674,2676,2702,2710,2714,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9115 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9115 2606 5
  · have he : independentCachedBranchMembers9115.erase 2606=independentCachedBranchMembers9105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9105
  · have he : independentCachedBranchMembers9115.filter (independentCachedEdge 2606)=independentCachedBranchMembers9114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9114
def independentCachedBranchMembers9116 : Finset ℕ := ([2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3072,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9116 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9116 5 (fun x => (if x<3150 then (if x<2762 then (if x<2710 then (if x<2668 then 0 else (if x<2674 then 0 else 1)) else (if x<2738 then (if x<2732 then 1 else 2) else (if x<2758 then 2 else 0))) else (if x<2800 then (if x<2772 then 1 else (if x<2776 then 2 else 3)) else (if x<3126 then (if x<3072 then 0 else 4) else (if x<3130 then 1 else 4)))) else (if x<3238 then (if x<3188 then (if x<3164 then 0 else (if x<3178 then 3 else 1)) else (if x<3214 then (if x<3192 then 4 else 0) else (if x<3228 then 1 else 4))) else (if x<3276 then (if x<3252 then 4 else (if x<3256 then 2 else 3)) else (if x<3300 then (if x<3282 then 2 else 0) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9117 : Finset ℕ := ([2668,2732,2758,2762,3072,3150,3178,3214,3238,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9117 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9117 4 (fun x => (if x<3178 then (if x<2762 then (if x<2732 then 0 else (if x<2758 then 1 else 0)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3276 then (if x<3214 then 2 else (if x<3238 then 1 else 2)) else (if x<3300 then 2 else (if x<3304 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9118 : Finset ℕ := ([2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3072,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9118 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9118 2620 4
  · have he : independentCachedBranchMembers9118.erase 2620=independentCachedBranchMembers9116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9116
  · have he : independentCachedBranchMembers9118.filter (independentCachedEdge 2620)=independentCachedBranchMembers9117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9117
def independentCachedBranchMembers9119 : Finset ℕ := ([2620,2650,2668,2674,2710,2758,2776,2800,3130,3164,3178,3188,3214,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9119 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9119 4 (fun x => (if x<3130 then (if x<2710 then (if x<2668 then (if x<2650 then 0 else 0) else (if x<2674 then 1 else 1)) else (if x<2776 then (if x<2758 then 0 else 1) else (if x<2800 then 1 else 0))) else (if x<3214 then (if x<3178 then (if x<3164 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
