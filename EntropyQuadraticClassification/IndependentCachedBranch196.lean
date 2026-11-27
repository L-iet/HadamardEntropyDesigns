/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch195
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9056 : Finset ℕ := ([2702,2744,3130,3188,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9056 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9056 3 (fun x => (if x<3188 then (if x<2744 then 0 else (if x<3130 then 0 else 1)) else (if x<3250 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9057 : Finset ℕ := ([2620,2674,2702,2744,3072,3126,3130,3150,3188,3192,3250,3270,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9057 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9057 3126 3
  · have he : independentCachedBranchMembers9057.erase 3126=independentCachedBranchMembers9055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9055
  · have he : independentCachedBranchMembers9057.filter (independentCachedEdge 3126)=independentCachedBranchMembers9056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9056
def independentCachedBranchMembers9058 : Finset ℕ := ([2620,2652,2666,2674,2702,2710,2732,2744,2772,2776,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3228,3238,3242,3250,3270,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9058 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9058 2732 4
  · have he : independentCachedBranchMembers9058.erase 2732=independentCachedBranchMembers9054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9054
  · have he : independentCachedBranchMembers9058.filter (independentCachedEdge 2732)=independentCachedBranchMembers9057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9057
def independentCachedBranchMembers9059 : Finset ℕ := ([2620,2652,2666,2674,2702,2710,2744,2776,3130,3162,3180,3188,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9059 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9059 4 (fun x => (if x<3130 then (if x<2702 then (if x<2666 then (if x<2652 then 0 else 1) else (if x<2674 then 0 else 1)) else (if x<2744 then (if x<2710 then 0 else 1) else (if x<2776 then 1 else 0))) else (if x<3238 then (if x<3180 then (if x<3162 then 2 else 3) else (if x<3188 then 2 else 3)) else (if x<3304 then (if x<3270 then 2 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9060 : Finset ℕ := ([2620,2652,2666,2674,2702,2710,2732,2744,2772,2776,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3228,3238,3242,3250,3270,3274,3282,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9060 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9060 3300 4
  · have he : independentCachedBranchMembers9060.erase 3300=independentCachedBranchMembers9058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9058
  · have he : independentCachedBranchMembers9060.filter (independentCachedEdge 3300)=independentCachedBranchMembers9059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9059
def independentCachedBranchMembers9061 : Finset ℕ := ([2618,2620,2650,2652,2666,2668,2674,2676,2702,2710,2716,2726,2732,2738,2744,2758,2762,2772,2776,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9061 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9061 2716 5
  · have he : independentCachedBranchMembers9061.erase 2716=independentCachedBranchMembers9049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9049
  · have he : independentCachedBranchMembers9061.filter (independentCachedEdge 2716)=independentCachedBranchMembers9060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9060
def independentCachedBranchMembers9062 : Finset ℕ := ([2650,2652,2666,2668,2702,2744,2758,2800,3072,3130,3132,3150,3186,3188,3192,3222,3226,3228,3238,3242,3244,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9062 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9062 5 (fun x => (if x<3188 then (if x<2758 then (if x<2668 then (if x<2652 then 0 else (if x<2666 then 1 else 1)) else (if x<2702 then 0 else (if x<2744 then 0 else 0))) else (if x<3130 then (if x<2800 then 1 else (if x<3072 then 1 else 2)) else (if x<3150 then (if x<3132 then 2 else 3) else (if x<3186 then 0 else 3)))) else (if x<3244 then (if x<3226 then (if x<3192 then 2 else (if x<3222 then 0 else 2)) else (if x<3238 then (if x<3228 then 0 else 4) else (if x<3242 then 3 else 4))) else (if x<3288 then (if x<3282 then 0 else (if x<3284 then 4 else 1)) else (if x<3300 then (if x<3298 then 2 else 1) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9063 : Finset ℕ := ([2650,2666,2702,2758,3072,3130,3186,3192,3222,3228,3238,3244,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9063 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9063 4 (fun x => (if x<3192 then (if x<2758 then (if x<2666 then 0 else (if x<2702 then 1 else 0)) else (if x<3130 then (if x<3072 then 1 else 2) else (if x<3186 then 1 else 0))) else (if x<3238 then (if x<3222 then 2 else (if x<3228 then 1 else 2)) else (if x<3284 then (if x<3244 then 0 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9064 : Finset ℕ := ([2650,2652,2666,2668,2702,2744,2758,2762,2800,3072,3130,3132,3150,3186,3188,3192,3222,3226,3228,3238,3242,3244,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9064 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9064 2762 4
  · have he : independentCachedBranchMembers9064.erase 2762=independentCachedBranchMembers9062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9062
  · have he : independentCachedBranchMembers9064.filter (independentCachedEdge 2762)=independentCachedBranchMembers9063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9063
def independentCachedBranchMembers9065 : Finset ℕ := ([2652,2668,2744,2800,3072,3132,3188,3192,3228,3244,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9065 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9065 4 (fun x => (if x<3192 then (if x<2800 then (if x<2668 then 0 else (if x<2744 then 1 else 0)) else (if x<3132 then (if x<3072 then 1 else 2) else (if x<3188 then 0 else 1))) else (if x<3284 then (if x<3228 then 2 else (if x<3244 then 2 else 3)) else (if x<3300 then (if x<3288 then 3 else 0) else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9066 : Finset ℕ := ([2650,2652,2666,2668,2702,2738,2744,2758,2762,2800,3072,3130,3132,3150,3186,3188,3192,3222,3226,3228,3238,3242,3244,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9066 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9066 2738 4
  · have he : independentCachedBranchMembers9066.erase 2738=independentCachedBranchMembers9064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9064
  · have he : independentCachedBranchMembers9066.filter (independentCachedEdge 2738)=independentCachedBranchMembers9065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9065
def independentCachedBranchMembers9067 : Finset ℕ := ([2650,2652,2666,2668,2702,2744,2758,2800,3130,3132,3186,3188,3222,3238,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9067 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9067 4 (fun x => (if x<3130 then (if x<2702 then (if x<2666 then (if x<2652 then 0 else 1) else (if x<2668 then 1 else 0)) else (if x<2758 then (if x<2744 then 0 else 0) else (if x<2800 then 1 else 1))) else (if x<3222 then (if x<3186 then (if x<3132 then 2 else 3) else (if x<3188 then 3 else 2)) else (if x<3288 then (if x<3238 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9068 : Finset ℕ := ([2650,2652,2666,2668,2702,2738,2744,2758,2762,2800,3072,3126,3130,3132,3150,3186,3188,3192,3222,3226,3228,3238,3242,3244,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9068 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9068 3126 4
  · have he : independentCachedBranchMembers9068.erase 3126=independentCachedBranchMembers9066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9066
  · have he : independentCachedBranchMembers9068.filter (independentCachedEdge 3126)=independentCachedBranchMembers9067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9067
def independentCachedBranchMembers9069 : Finset ℕ := ([2618,2620,2638,2650,2652,2666,2668,2674,2676,2702,2710,2716,2726,2732,2738,2744,2758,2762,2772,2776,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9069 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9069 2638 5
  · have he : independentCachedBranchMembers9069.erase 2638=independentCachedBranchMembers9061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9061
  · have he : independentCachedBranchMembers9069.filter (independentCachedEdge 2638)=independentCachedBranchMembers9068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9068
def independentCachedBranchMembers9070 : Finset ℕ := ([2618,2620,2674,2676,2710,2726,2762,2776,2792,3072,3126,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9070 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9070 5 (fun x => (if x<3180 then (if x<2776 then (if x<2676 then (if x<2620 then 0 else (if x<2674 then 1 else 1)) else (if x<2726 then (if x<2710 then 0 else 0) else (if x<2762 then 1 else 2))) else (if x<3126 then (if x<2792 then 0 else (if x<3072 then 1 else 3)) else (if x<3164 then (if x<3162 then 0 else 2) else (if x<3178 then 3 else 3)))) else (if x<3256 then (if x<3226 then (if x<3192 then 4 else (if x<3214 then 0 else 2)) else (if x<3242 then (if x<3228 then 0 else 4) else (if x<3244 then 4 else 1))) else (if x<3284 then (if x<3270 then 3 else (if x<3282 then 4 else 3)) else (if x<3300 then (if x<3298 then 0 else 1) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9071 : Finset ℕ := ([2618,2674,2710,2726,3072,3162,3178,3192,3214,3228,3244,3270,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9071 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9071 4 (fun x => (if x<3192 then (if x<2726 then (if x<2674 then 0 else (if x<2710 then 1 else 0)) else (if x<3162 then (if x<3072 then 1 else 2) else (if x<3178 then 1 else 0))) else (if x<3244 then (if x<3214 then 2 else (if x<3228 then 1 else 2)) else (if x<3284 then (if x<3270 then 3 else 0) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9072 : Finset ℕ := ([2618,2620,2674,2676,2710,2726,2738,2762,2776,2792,3072,3126,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9072 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9072 2738 4
  · have he : independentCachedBranchMembers9072.erase 2738=independentCachedBranchMembers9070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9070
  · have he : independentCachedBranchMembers9072.filter (independentCachedEdge 2738)=independentCachedBranchMembers9071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9071
def independentCachedBranchMembers9073 : Finset ℕ := ([2618,2620,2674,2676,2710,2726,2776,2792,3162,3164,3178,3180,3214,3256,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9073 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9073 4 (fun x => (if x<3162 then (if x<2710 then (if x<2674 then (if x<2620 then 0 else 1) else (if x<2676 then 1 else 0)) else (if x<2776 then (if x<2726 then 0 else 1) else (if x<2792 then 0 else 1))) else (if x<3214 then (if x<3178 then (if x<3164 then 2 else 3) else (if x<3180 then 3 else 2)) else (if x<3270 then (if x<3256 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9074 : Finset ℕ := ([2618,2620,2674,2676,2710,2726,2738,2762,2776,2792,3072,3126,3150,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9074 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9074 3150 4
  · have he : independentCachedBranchMembers9074.erase 3150=independentCachedBranchMembers9072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9072
  · have he : independentCachedBranchMembers9074.filter (independentCachedEdge 3150)=independentCachedBranchMembers9073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9073
def independentCachedBranchMembers9075 : Finset ℕ := ([2614,2618,2620,2638,2650,2652,2666,2668,2674,2676,2702,2710,2716,2726,2732,2738,2744,2758,2762,2772,2776,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9075 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9075 2614 5
  · have he : independentCachedBranchMembers9075.erase 2614=independentCachedBranchMembers9069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9069
  · have he : independentCachedBranchMembers9075.filter (independentCachedEdge 2614)=independentCachedBranchMembers9074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9074
def independentCachedBranchMembers9076 : Finset ℕ := ([2652,2666,2674,2716,2726,2738,2758,2762,2788,2792,2800,3072,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9076 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9076 5 (fun x => (if x<3150 then (if x<2762 then (if x<2716 then (if x<2666 then 0 else (if x<2674 then 0 else 1)) else (if x<2738 then (if x<2726 then 2 else 1) else (if x<2758 then 2 else 0))) else (if x<2800 then (if x<2788 then 1 else (if x<2792 then 2 else 3)) else (if x<3126 then (if x<3072 then 0 else 4) else (if x<3130 then 1 else 4)))) else (if x<3244 then (if x<3188 then (if x<3162 then 0 else (if x<3180 then 1 else 3)) else (if x<3214 then (if x<3192 then 4 else 0) else (if x<3222 then 1 else 4))) else (if x<3276 then (if x<3252 then 4 else (if x<3256 then 2 else 3)) else (if x<3288 then (if x<3284 then 2 else 0) else (if x<3298 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9077 : Finset ℕ := ([2652,2716,2758,2762,3072,3150,3162,3214,3222,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9077 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9077 4 (fun x => (if x<3162 then (if x<2762 then (if x<2716 then 0 else (if x<2758 then 1 else 0)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3276 then (if x<3214 then 2 else (if x<3222 then 1 else 2)) else (if x<3284 then 2 else (if x<3288 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9078 : Finset ℕ := ([2620,2652,2666,2674,2716,2726,2738,2758,2762,2788,2792,2800,3072,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9078 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9078 2620 4
  · have he : independentCachedBranchMembers9078.erase 2620=independentCachedBranchMembers9076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9076
  · have he : independentCachedBranchMembers9078.filter (independentCachedEdge 2620)=independentCachedBranchMembers9077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9077
def independentCachedBranchMembers9079 : Finset ℕ := ([2620,2652,2666,2674,2726,2758,2792,2800,3130,3162,3180,3188,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9079 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9079 4 (fun x => (if x<3130 then (if x<2726 then (if x<2666 then (if x<2652 then 0 else 1) else (if x<2674 then 0 else 1)) else (if x<2792 then (if x<2758 then 0 else 1) else (if x<2800 then 1 else 0))) else (if x<3214 then (if x<3180 then (if x<3162 then 2 else 3) else (if x<3188 then 2 else 3)) else (if x<3256 then (if x<3222 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9080 : Finset ℕ := ([2620,2652,2666,2674,2716,2726,2738,2758,2762,2788,2792,2800,3072,3126,3130,3150,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9080 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9080 3226 4
  · have he : independentCachedBranchMembers9080.erase 3226=independentCachedBranchMembers9078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9078
  · have he : independentCachedBranchMembers9080.filter (independentCachedEdge 3226)=independentCachedBranchMembers9079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9079
def independentCachedBranchMembers9081 : Finset ℕ := ([2620,2666,2716,2726,2738,2762,2788,2800,3126,3150,3162,3188,3222,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9081 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9081 4 (fun x => (if x<3126 then (if x<2738 then (if x<2716 then (if x<2666 then 0 else 0) else (if x<2726 then 1 else 0)) else (if x<2788 then (if x<2762 then 1 else 1) else (if x<2800 then 1 else 0))) else (if x<3222 then (if x<3162 then (if x<3150 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3244 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9082 : Finset ℕ := ([2620,2652,2666,2674,2716,2726,2738,2758,2762,2788,2792,2800,3072,3126,3130,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9082 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9082 3158 4
  · have he : independentCachedBranchMembers9082.erase 3158=independentCachedBranchMembers9080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9080
  · have he : independentCachedBranchMembers9082.filter (independentCachedEdge 3158)=independentCachedBranchMembers9081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9081
def independentCachedBranchMembers9083 : Finset ℕ := ([2652,2674,2716,2738,2758,2762,2788,2792,3126,3130,3150,3180,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9083 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9083 4 (fun x => (if x<3126 then (if x<2758 then (if x<2716 then (if x<2674 then 0 else 0) else (if x<2738 then 1 else 1)) else (if x<2788 then (if x<2762 then 0 else 1) else (if x<2792 then 1 else 0))) else (if x<3214 then (if x<3150 then (if x<3130 then 2 else 3) else (if x<3180 then 2 else 3)) else (if x<3284 then (if x<3244 then 3 else 2) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9084 : Finset ℕ := ([2620,2652,2666,2674,2716,2726,2738,2758,2762,2788,2792,2800,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9084 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9084 3118 4
  · have he : independentCachedBranchMembers9084.erase 3118=independentCachedBranchMembers9082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9082
  · have he : independentCachedBranchMembers9084.filter (independentCachedEdge 3118)=independentCachedBranchMembers9083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9083
def independentCachedBranchMembers9085 : Finset ℕ := ([2614,2618,2620,2638,2650,2652,2666,2668,2674,2676,2702,2710,2716,2726,2732,2738,2744,2758,2762,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9085 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9085 2786 5
  · have he : independentCachedBranchMembers9085.erase 2786=independentCachedBranchMembers9075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9075
  · have he : independentCachedBranchMembers9085.filter (independentCachedEdge 2786)=independentCachedBranchMembers9084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9084
def independentCachedBranchMembers9086 : Finset ℕ := ([2650,2668,2676,2702,2710,2716,2738,2744,2762,2776,2788,3072,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9086 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9086 5 (fun x => (if x<3150 then (if x<2744 then (if x<2702 then (if x<2668 then 0 else (if x<2676 then 0 else 1)) else (if x<2716 then (if x<2710 then 0 else 1) else (if x<2738 then 2 else 2))) else (if x<2788 then (if x<2762 then 0 else (if x<2776 then 2 else 1)) else (if x<3126 then (if x<3072 then 2 else 3) else (if x<3132 then 1 else 3)))) else (if x<3244 then (if x<3186 then (if x<3164 then 0 else (if x<3178 then 4 else 3)) else (if x<3226 then (if x<3192 then 4 else 0) else (if x<3238 then 0 else 3))) else (if x<3276 then (if x<3252 then 0 else (if x<3270 then 2 else 4)) else (if x<3304 then (if x<3284 then 2 else 1) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9087 : Finset ℕ := ([2650,2738,2744,2788,3072,3150,3164,3238,3244,3252,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9087 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9087 4 (fun x => (if x<3164 then (if x<2788 then (if x<2738 then 0 else (if x<2744 then 0 else 1)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3252 then (if x<3238 then 2 else (if x<3244 then 0 else 1)) else (if x<3304 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
