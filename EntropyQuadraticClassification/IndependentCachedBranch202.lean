/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch201
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9248 : Finset ℕ := ([2614,2618,2620,2638,2650,2652,2702,2710,2716,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9248 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9248 3174 4
  · have he : independentCachedBranchMembers9248.erase 3174=independentCachedBranchMembers9246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9246
  · have he : independentCachedBranchMembers9248.filter (independentCachedEdge 3174)=independentCachedBranchMembers9247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9247
def independentCachedBranchMembers9249 : Finset ℕ := ([2620,2652,2716,2788,2792,2800,3072,3180,3188,3192,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9249 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9249 4 (fun x => (if x<3188 then (if x<2792 then (if x<2716 then (if x<2652 then 0 else 1) else (if x<2788 then 2 else 0)) else (if x<3072 then (if x<2800 then 1 else 2) else (if x<3180 then 3 else 0))) else (if x<3256 then (if x<3244 then (if x<3192 then 3 else 1) else (if x<3252 then 3 else 0)) else (if x<3284 then (if x<3276 then 2 else 1) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9250 : Finset ℕ := ([2614,2618,2620,2638,2650,2652,2702,2710,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9250 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9250 2786 4
  · have he : independentCachedBranchMembers9250.erase 2786=independentCachedBranchMembers9248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9248
  · have he : independentCachedBranchMembers9250.filter (independentCachedEdge 2786)=independentCachedBranchMembers9249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9249
def independentCachedBranchMembers9251 : Finset ℕ := ([2618,2650,2702,2710,2716,2788,3072,3178,3186,3192,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9251 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9251 4 (fun x => (if x<3186 then (if x<2716 then (if x<2702 then (if x<2650 then 0 else 1) else (if x<2710 then 0 else 1)) else (if x<3072 then (if x<2788 then 2 else 2) else (if x<3178 then 3 else 1))) else (if x<3252 then (if x<3238 then (if x<3192 then 0 else 3) else (if x<3244 then 1 else 2)) else (if x<3276 then (if x<3270 then 3 else 0) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9252 : Finset ℕ := ([2614,2618,2620,2638,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9252 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9252 2714 4
  · have he : independentCachedBranchMembers9252.erase 2714=independentCachedBranchMembers9250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9250
  · have he : independentCachedBranchMembers9252.filter (independentCachedEdge 2714)=independentCachedBranchMembers9251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9251
def independentCachedBranchMembers9253 : Finset ℕ := ([2614,2638,2650,2652,2710,2792,3072,3178,3180,3192,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9253 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9253 4 (fun x => (if x<3180 then (if x<2710 then (if x<2650 then (if x<2638 then 0 else 0) else (if x<2652 then 1 else 2)) else (if x<3072 then (if x<2792 then 1 else 2) else (if x<3178 then 3 else 1))) else (if x<3252 then (if x<3238 then (if x<3192 then 2 else 3) else (if x<3250 then 1 else 0)) else (if x<3276 then (if x<3274 then 3 else 0) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9254 : Finset ℕ := ([2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9254 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9254 2646 4
  · have he : independentCachedBranchMembers9254.erase 2646=independentCachedBranchMembers9252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9252
  · have he : independentCachedBranchMembers9254.filter (independentCachedEdge 2646)=independentCachedBranchMembers9253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9253
def independentCachedBranchMembers9255 : Finset ℕ := ([2614,2618,2620,2638,2702,2800,3072,3186,3188,3192,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9255 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9255 4 (fun x => (if x<3188 then (if x<2702 then (if x<2620 then (if x<2618 then 0 else 1) else (if x<2638 then 2 else 0)) else (if x<3072 then (if x<2800 then 1 else 2) else (if x<3186 then 3 else 1))) else (if x<3256 then (if x<3250 then (if x<3192 then 2 else 3) else (if x<3252 then 0 else 3)) else (if x<3274 then (if x<3270 then 2 else 1) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9256 : Finset ℕ := ([2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9256 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9256 2606 4
  · have he : independentCachedBranchMembers9256.erase 2606=independentCachedBranchMembers9254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9254
  · have he : independentCachedBranchMembers9256.filter (independentCachedEdge 2606)=independentCachedBranchMembers9255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9255
def independentCachedBranchMembers9257 : Finset ℕ := ([2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9257 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9257 2590 5
  · have he : independentCachedBranchMembers9257.erase 2590=independentCachedBranchMembers9239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9239
  · have he : independentCachedBranchMembers9257.filter (independentCachedEdge 2590)=independentCachedBranchMembers9256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9256
def independentCachedBranchMembers9258 : Finset ℕ := ([3072,3130,3132,3150,3162,3164,3178,3180,3186,3188,3214,3222,3228,3238,3244,3250,3256,3270,3274,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9258 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9258 5 (fun x => (if x<3228 then (if x<3178 then (if x<3150 then (if x<3130 then 0 else (if x<3132 then 0 else 1)) else (if x<3162 then 0 else (if x<3164 then 1 else 2))) else (if x<3188 then (if x<3180 then 2 else (if x<3186 then 3 else 3)) else (if x<3214 then 0 else (if x<3222 then 1 else 0)))) else (if x<3274 then (if x<3250 then (if x<3238 then 4 else (if x<3244 then 3 else 0)) else (if x<3256 then 1 else (if x<3270 then 2 else 4))) else (if x<3300 then (if x<3284 then 3 else (if x<3288 then 1 else 0)) else (if x<3304 then 2 else (if x<3312 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9259 : Finset ℕ := ([3130,3132,3186,3188,3222,3238,3250,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9259 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9259 4 (fun x => (if x<3238 then (if x<3186 then (if x<3132 then 0 else 1) else (if x<3188 then 1 else (if x<3222 then 0 else 0))) else (if x<3274 then (if x<3250 then 1 else 2) else (if x<3288 then 2 else (if x<3304 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9260 : Finset ℕ := ([3072,3126,3130,3132,3150,3162,3164,3178,3180,3186,3188,3214,3222,3228,3238,3244,3250,3256,3270,3274,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9260 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9260 3126 4
  · have he : independentCachedBranchMembers9260.erase 3126=independentCachedBranchMembers9258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9258
  · have he : independentCachedBranchMembers9260.filter (independentCachedEdge 3126)=independentCachedBranchMembers9259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9259
def independentCachedBranchMembers9261 : Finset ℕ := ([3132,3164,3178,3186,3228,3238,3250,3270,3274,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9261 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9261 4 (fun x => (if x<3250 then (if x<3186 then (if x<3164 then 0 else (if x<3178 then 1 else 0)) else (if x<3228 then 1 else (if x<3238 then 2 else 0))) else (if x<3300 then (if x<3270 then 2 else (if x<3274 then 1 else 2)) else (if x<3304 then 2 else (if x<3312 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9262 : Finset ℕ := ([3072,3126,3130,3132,3150,3162,3164,3178,3180,3186,3188,3214,3222,3228,3238,3244,3250,3256,3270,3274,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9262 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9262 3298 4
  · have he : independentCachedBranchMembers9262.erase 3298=independentCachedBranchMembers9260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9260
  · have he : independentCachedBranchMembers9262.filter (independentCachedEdge 3298)=independentCachedBranchMembers9261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9261
def independentCachedBranchMembers9263 : Finset ℕ := ([3130,3162,3180,3188,3214,3222,3228,3250,3256,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9263 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9263 4 (fun x => (if x<3228 then (if x<3188 then (if x<3162 then 0 else (if x<3180 then 1 else 0)) else (if x<3214 then 1 else (if x<3222 then 0 else 1))) else (if x<3274 then (if x<3250 then 2 else (if x<3256 then 2 else 1)) else (if x<3288 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9264 : Finset ℕ := ([3072,3126,3130,3132,3150,3162,3164,3178,3180,3186,3188,3214,3222,3226,3228,3238,3244,3250,3256,3270,3274,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9264 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9264 3226 4
  · have he : independentCachedBranchMembers9264.erase 3226=independentCachedBranchMembers9262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9262
  · have he : independentCachedBranchMembers9264.filter (independentCachedEdge 3226)=independentCachedBranchMembers9263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9263
def independentCachedBranchMembers9265 : Finset ℕ := ([3126,3150,3162,3164,3186,3188,3222,3244,3256,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9265 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9265 4 (fun x => (if x<3222 then (if x<3164 then (if x<3150 then 0 else (if x<3162 then 0 else 1)) else (if x<3186 then 2 else (if x<3188 then 2 else 1))) else (if x<3270 then (if x<3244 then 1 else (if x<3256 then 0 else 1)) else (if x<3284 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9266 : Finset ℕ := ([3072,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3214,3222,3226,3228,3238,3244,3250,3256,3270,3274,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9266 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9266 3158 4
  · have he : independentCachedBranchMembers9266.erase 3158=independentCachedBranchMembers9264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9264
  · have he : independentCachedBranchMembers9266.filter (independentCachedEdge 3158)=independentCachedBranchMembers9265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9265
def independentCachedBranchMembers9267 : Finset ℕ := ([3126,3130,3132,3150,3178,3180,3214,3238,3244,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9267 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9267 4 (fun x => (if x<3214 then (if x<3150 then (if x<3130 then 0 else (if x<3132 then 1 else 2)) else (if x<3178 then 0 else (if x<3180 then 2 else 1))) else (if x<3284 then (if x<3238 then 1 else (if x<3244 then 2 else 0)) else (if x<3288 then 0 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9268 : Finset ℕ := ([3072,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3214,3222,3226,3228,3238,3244,3250,3256,3270,3274,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9268 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9268 3118 4
  · have he : independentCachedBranchMembers9268.erase 3118=independentCachedBranchMembers9266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9266
  · have he : independentCachedBranchMembers9268.filter (independentCachedEdge 3118)=independentCachedBranchMembers9267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9267
def independentCachedBranchMembers9269 : Finset ℕ := ([3118,3132,3158,3162,3180,3186,3222,3226,3244,3250,3270,3274,3284,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9269 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9269 4 (fun x => (if x<3244 then (if x<3180 then (if x<3158 then (if x<3132 then 0 else 1) else (if x<3162 then 0 else 1)) else (if x<3222 then (if x<3186 then 2 else 2) else (if x<3226 then 1 else 0))) else (if x<3284 then (if x<3270 then (if x<3250 then 3 else 3) else (if x<3274 then 2 else 3)) else (if x<3298 then (if x<3288 then 3 else 2) else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9270 : Finset ℕ := ([3072,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3214,3222,3226,3228,3238,3244,3250,3256,3270,3274,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9270 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9270 3282 4
  · have he : independentCachedBranchMembers9270.erase 3282=independentCachedBranchMembers9268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9268
  · have he : independentCachedBranchMembers9270.filter (independentCachedEdge 3282)=independentCachedBranchMembers9269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9269
def independentCachedBranchMembers9271 : Finset ℕ := ([3126,3130,3150,3164,3180,3186,3214,3228,3244,3250,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9271 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9271 4 (fun x => (if x<3244 then (if x<3180 then (if x<3150 then (if x<3130 then 0 else 1) else (if x<3164 then 0 else 1)) else (if x<3214 then (if x<3186 then 2 else 2) else (if x<3228 then 1 else 0))) else (if x<3284 then (if x<3270 then (if x<3250 then 3 else 3) else (if x<3274 then 2 else 3)) else (if x<3300 then (if x<3288 then 3 else 2) else (if x<3304 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9272 : Finset ℕ := ([3072,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3214,3222,3226,3228,3238,3244,3250,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9272 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9272 3276 4
  · have he : independentCachedBranchMembers9272.erase 3276=independentCachedBranchMembers9270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9270
  · have he : independentCachedBranchMembers9272.filter (independentCachedEdge 3276)=independentCachedBranchMembers9271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9271
def independentCachedBranchMembers9273 : Finset ℕ := ([3126,3132,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3274,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9273 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9273 4 (fun x => (if x<3238 then (if x<3178 then (if x<3150 then (if x<3132 then 0 else 1) else (if x<3162 then 0 else 1)) else (if x<3222 then (if x<3188 then 2 else 2) else (if x<3228 then 1 else 0))) else (if x<3274 then (if x<3250 then (if x<3244 then 2 else 3) else (if x<3256 then 3 else 2)) else (if x<3300 then (if x<3284 then 3 else 3) else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9274 : Finset ℕ := ([3072,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3214,3222,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9274 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9274 3252 4
  · have he : independentCachedBranchMembers9274.erase 3252=independentCachedBranchMembers9272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9272
  · have he : independentCachedBranchMembers9274.filter (independentCachedEdge 3252)=independentCachedBranchMembers9273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9273
def independentCachedBranchMembers9275 : Finset ℕ := ([3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9275 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9275 4 (fun x => (if x<3238 then (if x<3178 then (if x<3158 then (if x<3130 then 0 else 1) else (if x<3164 then 0 else 1)) else (if x<3214 then (if x<3188 then 2 else 2) else (if x<3226 then 1 else 0))) else (if x<3274 then (if x<3250 then (if x<3244 then 2 else 3) else (if x<3256 then 3 else 2)) else (if x<3298 then (if x<3284 then 3 else 3) else (if x<3304 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9276 : Finset ℕ := ([3072,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9276 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9276 3242 4
  · have he : independentCachedBranchMembers9276.erase 3242=independentCachedBranchMembers9274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9274
  · have he : independentCachedBranchMembers9276.filter (independentCachedEdge 3242)=independentCachedBranchMembers9275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9275
def independentCachedBranchMembers9277 : Finset ℕ := ([3130,3132,3162,3164,3178,3180,3186,3188,3214,3222,3238,3256,3270,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9277 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9277 4 (fun x => (if x<3214 then (if x<3178 then (if x<3162 then (if x<3132 then 0 else 1) else (if x<3164 then 1 else 0)) else (if x<3186 then (if x<3180 then 2 else 3) else (if x<3188 then 3 else 2))) else (if x<3270 then (if x<3238 then (if x<3222 then 0 else 1) else (if x<3256 then 2 else 2)) else (if x<3304 then (if x<3288 then 3 else 3) else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9278 : Finset ℕ := ([3072,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9278 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9278 3192 4
  · have he : independentCachedBranchMembers9278.erase 3192=independentCachedBranchMembers9276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9276
  · have he : independentCachedBranchMembers9278.filter (independentCachedEdge 3192)=independentCachedBranchMembers9277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9277
def independentCachedBranchMembers9279 : Finset ℕ := ([3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9279 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9279 4 (fun x => (if x<3226 then (if x<3178 then (if x<3150 then (if x<3126 then 0 else 1) else (if x<3158 then 1 else 0)) else (if x<3186 then (if x<3180 then 2 else 3) else (if x<3188 then 3 else 2))) else (if x<3270 then (if x<3238 then (if x<3228 then 0 else 1) else (if x<3256 then 2 else 2)) else (if x<3298 then (if x<3288 then 3 else 3) else (if x<3300 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
