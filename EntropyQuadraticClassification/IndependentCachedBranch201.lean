/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch200
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9216 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2702,2710,2726,2744,2758,2776,2792,2800,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9216 2702 4
  · have he : independentCachedBranchMembers9216.erase 2702=independentCachedBranchMembers9214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9214
  · have he : independentCachedBranchMembers9216.filter (independentCachedEdge 2702)=independentCachedBranchMembers9215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9215
def independentCachedBranchMembers9217 : Finset ℕ := ([2620,2650,2668,2676,2726,2776,3072,3118,3126,3174,3226,3244,3252,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9217 4 (fun x => (if x<3126 then (if x<2726 then (if x<2668 then (if x<2650 then 0 else 0) else (if x<2676 then 1 else 2)) else (if x<3072 then (if x<2776 then 1 else 2) else (if x<3118 then 3 else 1))) else (if x<3252 then (if x<3226 then (if x<3174 then 2 else 3) else (if x<3244 then 2 else 0)) else (if x<3282 then (if x<3274 then 3 else 0) else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9218 : Finset ℕ := ([2620,2650,2652,2666,2668,2674,2676,2702,2710,2726,2744,2758,2776,2792,2800,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9218 2652 4
  · have he : independentCachedBranchMembers9218.erase 2652=independentCachedBranchMembers9216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9216
  · have he : independentCachedBranchMembers9218.filter (independentCachedEdge 2652)=independentCachedBranchMembers9217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9217
def independentCachedBranchMembers9219 : Finset ℕ := ([2620,2650,2666,2674,2744,2758,3072,3150,3158,3174,3228,3244,3252,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9219 4 (fun x => (if x<3158 then (if x<2744 then (if x<2666 then (if x<2650 then 0 else 0) else (if x<2674 then 1 else 2)) else (if x<3072 then (if x<2758 then 1 else 2) else (if x<3150 then 3 else 1))) else (if x<3252 then (if x<3228 then (if x<3174 then 2 else 3) else (if x<3244 then 1 else 0)) else (if x<3282 then (if x<3274 then 3 else 0) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9220 : Finset ℕ := ([2618,2620,2650,2652,2666,2668,2674,2676,2702,2710,2726,2744,2758,2776,2792,2800,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9220 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9220 2618 4
  · have he : independentCachedBranchMembers9220.erase 2618=independentCachedBranchMembers9218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9218
  · have he : independentCachedBranchMembers9220.filter (independentCachedEdge 2618)=independentCachedBranchMembers9219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9219
def independentCachedBranchMembers9221 : Finset ℕ := ([2606,2614,2618,2620,2638,2646,2650,2652,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9221 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9221 2680 5
  · have he : independentCachedBranchMembers9221.erase 2680=independentCachedBranchMembers9203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9203
  · have he : independentCachedBranchMembers9221.filter (independentCachedEdge 2680)=independentCachedBranchMembers9220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9220
def independentCachedBranchMembers9222 : Finset ℕ := ([2638,2666,2668,2674,2676,2716,2726,2744,2758,2776,2788,3072,3130,3132,3162,3164,3174,3192,3214,3222,3244,3250,3252,3274,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9222 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9222 5 (fun x => (if x<3162 then (if x<2744 then (if x<2674 then (if x<2666 then 0 else (if x<2668 then 1 else 2)) else (if x<2716 then (if x<2676 then 0 else 1) else (if x<2726 then 2 else 0))) else (if x<2788 then (if x<2758 then 1 else (if x<2776 then 2 else 3)) else (if x<3130 then (if x<3072 then 3 else 4) else (if x<3132 then 4 else 2)))) else (if x<3250 then (if x<3192 then (if x<3164 then 0 else (if x<3174 then 4 else 0)) else (if x<3222 then (if x<3214 then 1 else 0) else (if x<3244 then 2 else 4))) else (if x<3276 then (if x<3252 then 0 else (if x<3274 then 1 else 4)) else (if x<3304 then (if x<3284 then 2 else 3) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9223 : Finset ℕ := ([2674,2676,2726,2776,3072,3162,3164,3192,3214,3244,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9223 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9223 4 (fun x => (if x<3164 then (if x<2776 then (if x<2676 then 0 else (if x<2726 then 1 else 0)) else (if x<3072 then 1 else (if x<3162 then 2 else 0))) else (if x<3244 then (if x<3192 then 1 else (if x<3214 then 2 else 0)) else (if x<3284 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9224 : Finset ℕ := ([2614,2638,2666,2668,2674,2676,2716,2726,2744,2758,2776,2788,3072,3130,3132,3162,3164,3174,3192,3214,3222,3244,3250,3252,3274,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9224 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9224 2614 4
  · have he : independentCachedBranchMembers9224.erase 2614=independentCachedBranchMembers9222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9222
  · have he : independentCachedBranchMembers9224.filter (independentCachedEdge 2614)=independentCachedBranchMembers9223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9223
def independentCachedBranchMembers9225 : Finset ℕ := ([2614,2638,2666,2676,2716,2726,2744,2788,3132,3162,3222,3244,3250,3274,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9225 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9225 4 (fun x => (if x<3132 then (if x<2716 then (if x<2666 then (if x<2638 then 0 else 0) else (if x<2676 then 1 else 1)) else (if x<2744 then (if x<2726 then 0 else 1) else (if x<2788 then 1 else 0))) else (if x<3250 then (if x<3222 then (if x<3162 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9226 : Finset ℕ := ([2614,2638,2666,2668,2674,2676,2716,2726,2744,2758,2776,2788,3072,3130,3132,3162,3164,3174,3192,3214,3222,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9226 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9226 3282 4
  · have he : independentCachedBranchMembers9226.erase 3282=independentCachedBranchMembers9224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9224
  · have he : independentCachedBranchMembers9226.filter (independentCachedEdge 3282)=independentCachedBranchMembers9225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9225
def independentCachedBranchMembers9227 : Finset ℕ := ([2614,2638,2668,2674,2716,2758,2776,2788,3130,3164,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9227 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9227 4 (fun x => (if x<3130 then (if x<2716 then (if x<2668 then (if x<2638 then 0 else 0) else (if x<2674 then 1 else 1)) else (if x<2776 then (if x<2758 then 0 else 1) else (if x<2788 then 1 else 0))) else (if x<3250 then (if x<3214 then (if x<3164 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9228 : Finset ℕ := ([2614,2638,2666,2668,2674,2676,2716,2726,2744,2758,2776,2788,3072,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9228 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9228 3242 4
  · have he : independentCachedBranchMembers9228.erase 3242=independentCachedBranchMembers9226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9226
  · have he : independentCachedBranchMembers9228.filter (independentCachedEdge 3242)=independentCachedBranchMembers9227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9227
def independentCachedBranchMembers9229 : Finset ℕ := ([2666,2668,2674,2676,2726,2744,2758,2776,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9229 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9229 4 (fun x => (if x<3130 then (if x<2726 then (if x<2674 then (if x<2668 then 0 else 1) else (if x<2676 then 1 else 0)) else (if x<2758 then (if x<2744 then 0 else 0) else (if x<2776 then 1 else 1))) else (if x<3214 then (if x<3162 then (if x<3132 then 2 else 3) else (if x<3164 then 3 else 2)) else (if x<3304 then (if x<3222 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9230 : Finset ℕ := ([2614,2638,2666,2668,2674,2676,2716,2726,2744,2758,2776,2788,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9230 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9230 3102 4
  · have he : independentCachedBranchMembers9230.erase 3102=independentCachedBranchMembers9228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9228
  · have he : independentCachedBranchMembers9230.filter (independentCachedEdge 3102)=independentCachedBranchMembers9229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9229
def independentCachedBranchMembers9231 : Finset ℕ := ([2666,2674,2716,2726,2758,2788,3072,3130,3162,3192,3214,3222,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9231 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9231 4 (fun x => (if x<3162 then (if x<2758 then (if x<2716 then (if x<2674 then 0 else 1) else (if x<2726 then 2 else 0)) else (if x<3072 then (if x<2788 then 1 else 2) else (if x<3130 then 3 else 1))) else (if x<3244 then (if x<3214 then (if x<3192 then 0 else 3) else (if x<3222 then 1 else 0)) else (if x<3276 then (if x<3252 then 2 else 3) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9232 : Finset ℕ := ([2614,2638,2666,2668,2674,2676,2716,2726,2744,2758,2776,2786,2788,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9232 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9232 2786 4
  · have he : independentCachedBranchMembers9232.erase 2786=independentCachedBranchMembers9230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9230
  · have he : independentCachedBranchMembers9232.filter (independentCachedEdge 2786)=independentCachedBranchMembers9231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9231
def independentCachedBranchMembers9233 : Finset ℕ := ([2668,2676,2716,2744,2776,2788,3072,3132,3164,3192,3244,3252,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9233 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9233 4 (fun x => (if x<3164 then (if x<2776 then (if x<2716 then (if x<2676 then 0 else 1) else (if x<2744 then 0 else 1)) else (if x<3072 then (if x<2788 then 2 else 2) else (if x<3132 then 3 else 0))) else (if x<3276 then (if x<3244 then (if x<3192 then 3 else 1) else (if x<3252 then 3 else 1)) else (if x<3304 then (if x<3284 then 0 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9234 : Finset ℕ := ([2614,2638,2666,2668,2674,2676,2714,2716,2726,2744,2758,2776,2786,2788,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9234 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9234 2714 4
  · have he : independentCachedBranchMembers9234.erase 2714=independentCachedBranchMembers9232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9232
  · have he : independentCachedBranchMembers9234.filter (independentCachedEdge 2714)=independentCachedBranchMembers9233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9233
def independentCachedBranchMembers9235 : Finset ℕ := ([2614,2638,2674,2676,2744,2758,3072,3130,3132,3192,3214,3250,3252,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9235 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9235 4 (fun x => (if x<3132 then (if x<2744 then (if x<2674 then (if x<2638 then 0 else 0) else (if x<2676 then 1 else 2)) else (if x<3072 then (if x<2758 then 1 else 2) else (if x<3130 then 3 else 1))) else (if x<3252 then (if x<3214 then (if x<3192 then 2 else 3) else (if x<3250 then 2 else 0)) else (if x<3276 then (if x<3274 then 3 else 0) else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9236 : Finset ℕ := ([2614,2638,2646,2666,2668,2674,2676,2714,2716,2726,2744,2758,2776,2786,2788,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9236 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9236 2646 4
  · have he : independentCachedBranchMembers9236.erase 2646=independentCachedBranchMembers9234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9234
  · have he : independentCachedBranchMembers9236.filter (independentCachedEdge 2646)=independentCachedBranchMembers9235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9235
def independentCachedBranchMembers9237 : Finset ℕ := ([2614,2638,2666,2668,2726,2776,3072,3162,3164,3192,3222,3250,3252,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9237 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9237 4 (fun x => (if x<3164 then (if x<2726 then (if x<2666 then (if x<2638 then 0 else 0) else (if x<2668 then 1 else 2)) else (if x<3072 then (if x<2776 then 1 else 2) else (if x<3162 then 3 else 1))) else (if x<3252 then (if x<3222 then (if x<3192 then 2 else 3) else (if x<3250 then 1 else 0)) else (if x<3276 then (if x<3274 then 3 else 0) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9238 : Finset ℕ := ([2606,2614,2638,2646,2666,2668,2674,2676,2714,2716,2726,2744,2758,2776,2786,2788,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9238 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9238 2606 4
  · have he : independentCachedBranchMembers9238.erase 2606=independentCachedBranchMembers9236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9236
  · have he : independentCachedBranchMembers9238.filter (independentCachedEdge 2606)=independentCachedBranchMembers9237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9237
def independentCachedBranchMembers9239 : Finset ℕ := ([2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9239 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9239 2662 5
  · have he : independentCachedBranchMembers9239.erase 2662=independentCachedBranchMembers9221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9221
  · have he : independentCachedBranchMembers9239.filter (independentCachedEdge 2662)=independentCachedBranchMembers9238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9238
def independentCachedBranchMembers9240 : Finset ℕ := ([2618,2620,2638,2650,2652,2702,2710,2716,2788,2792,2800,3072,3102,3178,3180,3186,3188,3192,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9240 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9240 5 (fun x => (if x<3180 then (if x<2716 then (if x<2650 then (if x<2620 then 0 else (if x<2638 then 1 else 0)) else (if x<2702 then (if x<2652 then 1 else 2) else (if x<2710 then 1 else 0))) else (if x<2800 then (if x<2788 then 3 else (if x<2792 then 2 else 1)) else (if x<3102 then (if x<3072 then 3 else 4) else (if x<3178 then 0 else 0)))) else (if x<3252 then (if x<3192 then (if x<3186 then 2 else (if x<3188 then 3 else 4)) else (if x<3244 then (if x<3238 then 1 else 2) else (if x<3250 then 1 else 0))) else (if x<3274 then (if x<3256 then 3 else (if x<3270 then 4 else 0)) else (if x<3284 then (if x<3276 then 1 else 4) else (if x<3288 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9241 : Finset ℕ := ([2618,2620,2710,2792,3072,3178,3180,3192,3244,3256,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9241 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9241 4 (fun x => (if x<3180 then (if x<2792 then (if x<2620 then 0 else (if x<2710 then 1 else 0)) else (if x<3072 then 1 else (if x<3178 then 2 else 0))) else (if x<3256 then (if x<3192 then 1 else (if x<3244 then 2 else 2)) else (if x<3270 then 1 else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9242 : Finset ℕ := ([2614,2618,2620,2638,2650,2652,2702,2710,2716,2788,2792,2800,3072,3102,3178,3180,3186,3188,3192,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9242 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9242 2614 4
  · have he : independentCachedBranchMembers9242.erase 2614=independentCachedBranchMembers9240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9240
  · have he : independentCachedBranchMembers9242.filter (independentCachedEdge 2614)=independentCachedBranchMembers9241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9241
def independentCachedBranchMembers9243 : Finset ℕ := ([2614,2618,2638,2652,2702,2716,2788,2792,3180,3186,3244,3250,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9243 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9243 4 (fun x => (if x<3180 then (if x<2702 then (if x<2638 then (if x<2618 then 0 else 1) else (if x<2652 then 0 else 1)) else (if x<2788 then (if x<2716 then 1 else 0) else (if x<2792 then 0 else 1))) else (if x<3270 then (if x<3244 then (if x<3186 then 2 else 2) else (if x<3250 then 3 else 3)) else (if x<3284 then (if x<3274 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9244 : Finset ℕ := ([2614,2618,2620,2638,2650,2652,2702,2710,2716,2788,2792,2800,3072,3102,3178,3180,3186,3188,3192,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9244 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9244 3282 4
  · have he : independentCachedBranchMembers9244.erase 3282=independentCachedBranchMembers9242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9242
  · have he : independentCachedBranchMembers9244.filter (independentCachedEdge 3282)=independentCachedBranchMembers9243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9243
def independentCachedBranchMembers9245 : Finset ℕ := ([2614,2620,2638,2650,2710,2716,2788,2800,3178,3188,3238,3244,3250,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9245 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9245 4 (fun x => (if x<3178 then (if x<2710 then (if x<2638 then (if x<2620 then 0 else 1) else (if x<2650 then 0 else 1)) else (if x<2788 then (if x<2716 then 1 else 0) else (if x<2800 then 0 else 1))) else (if x<3250 then (if x<3238 then (if x<3188 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3274 then (if x<3256 then 3 else 2) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9246 : Finset ℕ := ([2614,2618,2620,2638,2650,2652,2702,2710,2716,2788,2792,2800,3072,3102,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9246 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9246 3242 4
  · have he : independentCachedBranchMembers9246.erase 3242=independentCachedBranchMembers9244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9244
  · have he : independentCachedBranchMembers9246.filter (independentCachedEdge 3242)=independentCachedBranchMembers9245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9245
def independentCachedBranchMembers9247 : Finset ℕ := ([2618,2620,2650,2652,2702,2710,2792,2800,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9247 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9247 4 (fun x => (if x<3178 then (if x<2702 then (if x<2650 then (if x<2620 then 0 else 1) else (if x<2652 then 1 else 0)) else (if x<2792 then (if x<2710 then 0 else 1) else (if x<2800 then 0 else 1))) else (if x<3238 then (if x<3186 then (if x<3180 then 2 else 3) else (if x<3188 then 3 else 2)) else (if x<3270 then (if x<3256 then 2 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
