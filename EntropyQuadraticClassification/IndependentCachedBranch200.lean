/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch199
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9184 : Finset ℕ := ([2618,2652,2666,2676,2702,2726,2732,2738,2744,2762,2772,2792,3072,3126,3132,3150,3162,3180,3186,3192,3222,3228,3242,3252,3270,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9184 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9184 2618 4
  · have he : independentCachedBranchMembers9184.erase 2618=independentCachedBranchMembers9182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9182
  · have he : independentCachedBranchMembers9184.filter (independentCachedEdge 2618)=independentCachedBranchMembers9183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9183
def independentCachedBranchMembers9185 : Finset ℕ := ([2618,2652,2666,2676,2702,2726,2744,2792,3132,3162,3180,3186,3222,3270,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9185 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9185 4 (fun x => (if x<3132 then (if x<2702 then (if x<2666 then (if x<2652 then 0 else 0) else (if x<2676 then 1 else 1)) else (if x<2744 then (if x<2726 then 0 else 1) else (if x<2792 then 1 else 0))) else (if x<3222 then (if x<3180 then (if x<3162 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3288 then (if x<3270 then 2 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9186 : Finset ℕ := ([2618,2652,2666,2676,2702,2726,2732,2738,2744,2762,2772,2792,3072,3126,3132,3150,3162,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9186 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9186 3282 4
  · have he : independentCachedBranchMembers9186.erase 3282=independentCachedBranchMembers9184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9184
  · have he : independentCachedBranchMembers9186.filter (independentCachedEdge 3282)=independentCachedBranchMembers9185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9185
def independentCachedBranchMembers9187 : Finset ℕ := ([2618,2652,2702,2732,2738,2762,2772,2792,3126,3150,3180,3186,3228,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9187 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9187 4 (fun x => (if x<3126 then (if x<2738 then (if x<2702 then (if x<2652 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<2772 then (if x<2762 then 1 else 1) else (if x<2792 then 1 else 0))) else (if x<3228 then (if x<3180 then (if x<3150 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3288 then (if x<3270 then 2 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9188 : Finset ℕ := ([2618,2652,2666,2676,2702,2726,2732,2738,2744,2762,2772,2792,3072,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9188 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9188 3174 4
  · have he : independentCachedBranchMembers9188.erase 3174=independentCachedBranchMembers9186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9186
  · have he : independentCachedBranchMembers9188.filter (independentCachedEdge 3174)=independentCachedBranchMembers9187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9187
def independentCachedBranchMembers9189 : Finset ℕ := ([2666,2676,2726,2732,2738,2744,2762,2772,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9189 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9189 4 (fun x => (if x<3126 then (if x<2738 then (if x<2726 then (if x<2676 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<2762 then (if x<2744 then 1 else 0) else (if x<2772 then 1 else 1))) else (if x<3222 then (if x<3150 then (if x<3132 then 2 else 3) else (if x<3162 then 2 else 3)) else (if x<3300 then (if x<3228 then 3 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9190 : Finset ℕ := ([2618,2652,2666,2676,2702,2726,2732,2738,2744,2762,2772,2792,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9190 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9190 3102 4
  · have he : independentCachedBranchMembers9190.erase 3102=independentCachedBranchMembers9188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9188
  · have he : independentCachedBranchMembers9190.filter (independentCachedEdge 3102)=independentCachedBranchMembers9189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9189
def independentCachedBranchMembers9191 : Finset ℕ := ([2666,2726,2738,2762,2792,3072,3126,3150,3162,3180,3192,3222,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9191 4 (fun x => (if x<3150 then (if x<2762 then (if x<2726 then 0 else (if x<2738 then 0 else 1)) else (if x<3072 then (if x<2792 then 1 else 2) else (if x<3126 then 3 else 1))) else (if x<3222 then (if x<3180 then (if x<3162 then 1 else 0) else (if x<3192 then 2 else 3)) else (if x<3276 then (if x<3252 then 0 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9192 : Finset ℕ := ([2726,2738,3072,3126,3222,3252] : List ℕ).toFinset
theorem independentCachedBranchBound9192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9192 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9192 3 (fun x => (if x<3126 then (if x<2738 then 0 else (if x<3072 then 1 else 2)) else (if x<3222 then 0 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9193 : Finset ℕ := ([2652,2666,2726,2738,2762,2792,3072,3126,3150,3162,3180,3192,3222,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9193 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9193 2652 3
  · have he : independentCachedBranchMembers9193.erase 2652=independentCachedBranchMembers9191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9191
  · have he : independentCachedBranchMembers9193.filter (independentCachedEdge 2652)=independentCachedBranchMembers9192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9192
def independentCachedBranchMembers9194 : Finset ℕ := ([2618,2652,2666,2676,2702,2726,2732,2738,2744,2762,2772,2786,2792,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9194 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9194 2786 4
  · have he : independentCachedBranchMembers9194.erase 2786=independentCachedBranchMembers9190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9190
  · have he : independentCachedBranchMembers9194.filter (independentCachedEdge 2786)=independentCachedBranchMembers9193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9193
def independentCachedBranchMembers9195 : Finset ℕ := ([2676,2702,2738,2744,2762,3072,3126,3132,3150,3186,3192,3252,3270,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9195 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9195 4 (fun x => (if x<3132 then (if x<2744 then (if x<2702 then 0 else (if x<2738 then 1 else 0)) else (if x<3072 then (if x<2762 then 1 else 2) else (if x<3126 then 3 else 0))) else (if x<3252 then (if x<3186 then (if x<3150 then 2 else 1) else (if x<3192 then 3 else 1)) else (if x<3276 then (if x<3270 then 3 else 3) else (if x<3312 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9196 : Finset ℕ := ([2738,2744,3072,3150,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9196 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9196 3 (fun x => (if x<3150 then (if x<2744 then 0 else (if x<3072 then 1 else 2)) else (if x<3252 then 0 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9197 : Finset ℕ := ([2618,2676,2702,2738,2744,2762,3072,3126,3132,3150,3186,3192,3252,3270,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9197 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9197 2618 3
  · have he : independentCachedBranchMembers9197.erase 2618=independentCachedBranchMembers9195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9195
  · have he : independentCachedBranchMembers9197.filter (independentCachedEdge 2618)=independentCachedBranchMembers9196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9196
def independentCachedBranchMembers9198 : Finset ℕ := ([2618,2652,2666,2676,2702,2714,2726,2732,2738,2744,2762,2772,2786,2792,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9198 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9198 2714 4
  · have he : independentCachedBranchMembers9198.erase 2714=independentCachedBranchMembers9194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9194
  · have he : independentCachedBranchMembers9198.filter (independentCachedEdge 2714)=independentCachedBranchMembers9197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9197
def independentCachedBranchMembers9199 : Finset ℕ := ([2652,2676,2732,2744,2772,2792,3072,3132,3180,3192,3228,3252,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9199 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9199 4 (fun x => (if x<3180 then (if x<2772 then (if x<2732 then (if x<2676 then 0 else 1) else (if x<2744 then 0 else 1)) else (if x<3072 then (if x<2792 then 2 else 2) else (if x<3132 then 3 else 0))) else (if x<3276 then (if x<3228 then (if x<3192 then 3 else 1) else (if x<3252 then 3 else 1)) else (if x<3300 then (if x<3288 then 0 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9200 : Finset ℕ := ([2618,2646,2652,2666,2676,2702,2714,2726,2732,2738,2744,2762,2772,2786,2792,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9200 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9200 2646 4
  · have he : independentCachedBranchMembers9200.erase 2646=independentCachedBranchMembers9198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9198
  · have he : independentCachedBranchMembers9200.filter (independentCachedEdge 2646)=independentCachedBranchMembers9199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9199
def independentCachedBranchMembers9201 : Finset ℕ := ([2618,2666,2702,2726,2732,2772,3072,3162,3186,3192,3222,3228,3252,3270,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9201 4 (fun x => (if x<3186 then (if x<2732 then (if x<2702 then (if x<2666 then 0 else 1) else (if x<2726 then 0 else 1)) else (if x<3072 then (if x<2772 then 2 else 2) else (if x<3162 then 3 else 1))) else (if x<3252 then (if x<3222 then (if x<3192 then 0 else 3) else (if x<3228 then 1 else 2)) else (if x<3276 then (if x<3270 then 3 else 0) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9202 : Finset ℕ := ([2606,2618,2646,2652,2666,2676,2702,2714,2726,2732,2738,2744,2762,2772,2786,2792,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9202 2606 4
  · have he : independentCachedBranchMembers9202.erase 2606=independentCachedBranchMembers9200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9200
  · have he : independentCachedBranchMembers9202.filter (independentCachedEdge 2606)=independentCachedBranchMembers9201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9201
def independentCachedBranchMembers9203 : Finset ℕ := ([2606,2614,2618,2620,2638,2646,2650,2652,2666,2668,2674,2676,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9203 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9203 2730 5
  · have he : independentCachedBranchMembers9203.erase 2730=independentCachedBranchMembers9181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9181
  · have he : independentCachedBranchMembers9203.filter (independentCachedEdge 2730)=independentCachedBranchMembers9202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9202
def independentCachedBranchMembers9204 : Finset ℕ := ([2650,2666,2668,2674,2676,2710,2726,2744,2758,2776,2800,3072,3118,3126,3150,3158,3174,3192,3226,3228,3244,3250,3252,3274,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9204 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9204 5 (fun x => (if x<3150 then (if x<2744 then (if x<2674 then (if x<2666 then 0 else (if x<2668 then 1 else 0)) else (if x<2710 then (if x<2676 then 2 else 1) else (if x<2726 then 2 else 1))) else (if x<2800 then (if x<2758 then 0 else (if x<2776 then 3 else 2)) else (if x<3118 then (if x<3072 then 3 else 4) else (if x<3126 then 4 else 2)))) else (if x<3250 then (if x<3192 then (if x<3158 then 0 else (if x<3174 then 4 else 1)) else (if x<3228 then (if x<3226 then 0 else 0) else (if x<3244 then 2 else 0))) else (if x<3282 then (if x<3252 then 4 else (if x<3274 then 1 else 4)) else (if x<3298 then (if x<3284 then 2 else 3) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9205 : Finset ℕ := ([2668,2676,2744,2758,3072,3150,3158,3174,3226,3250,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9205 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9205 4 (fun x => (if x<3158 then (if x<2758 then (if x<2676 then 0 else (if x<2744 then 1 else 0)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3250 then (if x<3174 then 1 else (if x<3226 then 2 else 0)) else (if x<3284 then 2 else (if x<3300 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9206 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2710,2726,2744,2758,2776,2800,3072,3118,3126,3150,3158,3174,3192,3226,3228,3244,3250,3252,3274,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9206 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9206 2620 4
  · have he : independentCachedBranchMembers9206.erase 2620=independentCachedBranchMembers9204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9204
  · have he : independentCachedBranchMembers9206.filter (independentCachedEdge 2620)=independentCachedBranchMembers9205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9205
def independentCachedBranchMembers9207 : Finset ℕ := ([2620,2650,2666,2676,2710,2726,2744,2800,3126,3150,3228,3244,3250,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9207 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9207 4 (fun x => (if x<3126 then (if x<2710 then (if x<2666 then (if x<2650 then 0 else 0) else (if x<2676 then 1 else 1)) else (if x<2744 then (if x<2726 then 0 else 1) else (if x<2800 then 1 else 0))) else (if x<3250 then (if x<3228 then (if x<3150 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9208 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2710,2726,2744,2758,2776,2800,3072,3118,3126,3150,3158,3174,3192,3226,3228,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9208 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9208 3276 4
  · have he : independentCachedBranchMembers9208.erase 3276=independentCachedBranchMembers9206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9206
  · have he : independentCachedBranchMembers9208.filter (independentCachedEdge 3276)=independentCachedBranchMembers9207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9207
def independentCachedBranchMembers9209 : Finset ℕ := ([2620,2650,2668,2674,2710,2758,2776,2800,3118,3158,3226,3244,3250,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9209 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9209 4 (fun x => (if x<3118 then (if x<2710 then (if x<2668 then (if x<2650 then 0 else 0) else (if x<2674 then 1 else 1)) else (if x<2776 then (if x<2758 then 0 else 1) else (if x<2800 then 1 else 0))) else (if x<3250 then (if x<3226 then (if x<3158 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9210 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2710,2726,2744,2758,2776,2800,3072,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9210 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9210 3242 4
  · have he : independentCachedBranchMembers9210.erase 3242=independentCachedBranchMembers9208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9208
  · have he : independentCachedBranchMembers9210.filter (independentCachedEdge 3242)=independentCachedBranchMembers9209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9209
def independentCachedBranchMembers9211 : Finset ℕ := ([2666,2668,2674,2676,2726,2744,2758,2776,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9211 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9211 4 (fun x => (if x<3118 then (if x<2726 then (if x<2674 then (if x<2668 then 0 else 1) else (if x<2676 then 1 else 0)) else (if x<2758 then (if x<2744 then 0 else 0) else (if x<2776 then 1 else 1))) else (if x<3226 then (if x<3150 then (if x<3126 then 2 else 3) else (if x<3158 then 3 else 2)) else (if x<3298 then (if x<3228 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9212 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2710,2726,2744,2758,2776,2800,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9212 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9212 3102 4
  · have he : independentCachedBranchMembers9212.erase 3102=independentCachedBranchMembers9210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9210
  · have he : independentCachedBranchMembers9212.filter (independentCachedEdge 3102)=independentCachedBranchMembers9211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9211
def independentCachedBranchMembers9213 : Finset ℕ := ([2666,2668,2710,2744,2776,2800,3072,3118,3150,3174,3226,3228,3250,3252,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9213 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9213 4 (fun x => (if x<3150 then (if x<2776 then (if x<2710 then (if x<2668 then 0 else 1) else (if x<2744 then 2 else 0)) else (if x<3072 then (if x<2800 then 1 else 2) else (if x<3118 then 3 else 1))) else (if x<3250 then (if x<3226 then (if x<3174 then 0 else 3) else (if x<3228 then 1 else 0)) else (if x<3282 then (if x<3252 then 2 else 3) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9214 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2710,2726,2744,2758,2776,2792,2800,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9214 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9214 2792 4
  · have he : independentCachedBranchMembers9214.erase 2792=independentCachedBranchMembers9212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9212
  · have he : independentCachedBranchMembers9214.filter (independentCachedEdge 2792)=independentCachedBranchMembers9213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9213
def independentCachedBranchMembers9215 : Finset ℕ := ([2674,2676,2710,2726,2758,2800,3072,3126,3158,3174,3250,3252,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9215 4 (fun x => (if x<3158 then (if x<2758 then (if x<2710 then (if x<2676 then 0 else 1) else (if x<2726 then 0 else 1)) else (if x<3072 then (if x<2800 then 2 else 2) else (if x<3126 then 3 else 0))) else (if x<3282 then (if x<3250 then (if x<3174 then 3 else 1) else (if x<3252 then 3 else 1)) else (if x<3298 then (if x<3284 then 0 else 2) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
