/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch194
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9024 : Finset ℕ := ([2620,2650,2668,2676,2726,2738,2772,2776,3072,3118,3126,3130,3164,3174,3178,3186,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9024 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9024 3304 4
  · have he : independentCachedBranchMembers9024.erase 3304=independentCachedBranchMembers9022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9022
  · have he : independentCachedBranchMembers9024.filter (independentCachedEdge 3304)=independentCachedBranchMembers9023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9023
def independentCachedBranchMembers9025 : Finset ℕ := ([2620,2650,2668,2738,2772,2776,3118,3186,3222,3226,3244,3270,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9025 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9025 4 (fun x => (if x<3186 then (if x<2738 then (if x<2650 then 0 else (if x<2668 then 0 else 1)) else (if x<2776 then (if x<2772 then 0 else 0) else (if x<3118 then 1 else 1))) else (if x<3244 then (if x<3222 then 2 else (if x<3226 then 2 else 1)) else (if x<3274 then (if x<3270 then 3 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9026 : Finset ℕ := ([2620,2650,2668,2676,2726,2738,2772,2776,3072,3118,3126,3130,3164,3174,3178,3186,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9026 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9026 3214 4
  · have he : independentCachedBranchMembers9026.erase 3214=independentCachedBranchMembers9024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9024
  · have he : independentCachedBranchMembers9026.filter (independentCachedEdge 3214)=independentCachedBranchMembers9025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9025
def independentCachedBranchMembers9027 : Finset ℕ := ([2620,2650,2652,2666,2668,2674,2676,2702,2710,2726,2732,2738,2744,2758,2762,2772,2776,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9027 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9027 2652 5
  · have he : independentCachedBranchMembers9027.erase 2652=independentCachedBranchMembers9017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9017
  · have he : independentCachedBranchMembers9027.filter (independentCachedEdge 2652)=independentCachedBranchMembers9026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9026
def independentCachedBranchMembers9028 : Finset ℕ := ([2620,2650,2674,2738,2758,2772,3072,3130,3150,3158,3164,3174,3180,3188,3222,3228,3238,3244,3252,3274,3282,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9028 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9028 5 (fun x => (if x<3180 then (if x<3072 then (if x<2738 then (if x<2650 then 0 else (if x<2674 then 0 else 1)) else (if x<2758 then 0 else (if x<2772 then 1 else 0))) else (if x<3158 then (if x<3130 then 2 else (if x<3150 then 0 else 2)) else (if x<3164 then 1 else (if x<3174 then 0 else 3)))) else (if x<3252 then (if x<3228 then (if x<3188 then 4 else (if x<3222 then 2 else 2)) else (if x<3238 then 4 else (if x<3244 then 4 else 2))) else (if x<3288 then (if x<3274 then 0 else (if x<3282 then 3 else 0)) else (if x<3298 then 2 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9029 : Finset ℕ := ([2620,2738,2758,3072,3164,3180,3188,3222,3238,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9029 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9029 4 (fun x => (if x<3188 then (if x<3072 then (if x<2738 then 0 else (if x<2758 then 0 else 1)) else (if x<3164 then 2 else (if x<3180 then 0 else 2))) else (if x<3274 then (if x<3222 then 3 else (if x<3238 then 1 else 2)) else (if x<3282 then 1 else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9030 : Finset ℕ := ([2620,2650,2674,2738,2744,2758,2772,3072,3130,3150,3158,3164,3174,3180,3188,3222,3228,3238,3244,3252,3274,3282,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9030 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9030 2744 4
  · have he : independentCachedBranchMembers9030.erase 2744=independentCachedBranchMembers9028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9028
  · have he : independentCachedBranchMembers9030.filter (independentCachedEdge 2744)=independentCachedBranchMembers9029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9029
def independentCachedBranchMembers9031 : Finset ℕ := ([2650,2674,2772,3072,3158,3164,3188,3238,3244,3282,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9031 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9031 4 (fun x => (if x<3188 then (if x<3072 then (if x<2674 then 0 else (if x<2772 then 1 else 0)) else (if x<3158 then 2 else (if x<3164 then 0 else 2))) else (if x<3282 then (if x<3238 then 1 else (if x<3244 then 3 else 1)) else (if x<3288 then 2 else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9032 : Finset ℕ := ([2620,2650,2666,2674,2738,2744,2758,2772,3072,3130,3150,3158,3164,3174,3180,3188,3222,3228,3238,3244,3252,3274,3282,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9032 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9032 2666 4
  · have he : independentCachedBranchMembers9032.erase 2666=independentCachedBranchMembers9030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9030
  · have he : independentCachedBranchMembers9032.filter (independentCachedEdge 2666)=independentCachedBranchMembers9031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9031
def independentCachedBranchMembers9033 : Finset ℕ := ([2620,2650,2674,2738,2758,2772,3158,3180,3222,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9033 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9033 4 (fun x => (if x<3180 then (if x<2738 then (if x<2650 then 0 else (if x<2674 then 0 else 1)) else (if x<2772 then (if x<2758 then 0 else 1) else (if x<3158 then 0 else 1))) else (if x<3274 then (if x<3222 then 2 else (if x<3244 then 3 else 3)) else (if x<3298 then (if x<3288 then 2 else 3) else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9034 : Finset ℕ := ([2620,2650,2666,2674,2738,2744,2758,2772,3072,3130,3150,3158,3164,3174,3180,3188,3222,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9034 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9034 3304 4
  · have he : independentCachedBranchMembers9034.erase 3304=independentCachedBranchMembers9032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9032
  · have he : independentCachedBranchMembers9034.filter (independentCachedEdge 3304)=independentCachedBranchMembers9033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9033
def independentCachedBranchMembers9035 : Finset ℕ := ([2620,2650,2666,2738,2744,2772,3150,3188,3222,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9035 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9035 4 (fun x => (if x<3188 then (if x<2738 then (if x<2650 then 0 else (if x<2666 then 0 else 1)) else (if x<2772 then (if x<2744 then 0 else 1) else (if x<3150 then 0 else 1))) else (if x<3238 then (if x<3222 then 2 else (if x<3228 then 2 else 1)) else (if x<3274 then (if x<3244 then 3 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9036 : Finset ℕ := ([2620,2650,2666,2674,2738,2744,2758,2772,3072,3130,3150,3158,3164,3174,3180,3188,3214,3222,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9036 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9036 3214 4
  · have he : independentCachedBranchMembers9036.erase 3214=independentCachedBranchMembers9034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9034
  · have he : independentCachedBranchMembers9036.filter (independentCachedEdge 3214)=independentCachedBranchMembers9035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9035
def independentCachedBranchMembers9037 : Finset ℕ := ([2618,2620,2650,2652,2666,2668,2674,2676,2702,2710,2726,2732,2738,2744,2758,2762,2772,2776,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9037 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9037 2618 5
  · have he : independentCachedBranchMembers9037.erase 2618=independentCachedBranchMembers9027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9027
  · have he : independentCachedBranchMembers9037.filter (independentCachedEdge 2618)=independentCachedBranchMembers9036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9036
def independentCachedBranchMembers9038 : Finset ℕ := ([2618,2650,2668,2676,2726,2758,2792,2800,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3214,3222,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9038 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9038 5 (fun x => (if x<3158 then (if x<2792 then (if x<2676 then (if x<2650 then 0 else (if x<2668 then 1 else 0)) else (if x<2726 then 1 else (if x<2758 then 0 else 1))) else (if x<3118 then (if x<2800 then 1 else (if x<3072 then 0 else 2)) else (if x<3132 then (if x<3126 then 0 else 2) else (if x<3150 then 3 else 2)))) else (if x<3242 then (if x<3186 then (if x<3164 then 1 else (if x<3178 then 4 else 3)) else (if x<3214 then (if x<3192 then 4 else 0) else (if x<3222 then 3 else 4))) else (if x<3274 then (if x<3250 then 2 else (if x<3256 then 0 else 4)) else (if x<3288 then (if x<3282 then 1 else 2) else (if x<3300 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9039 : Finset ℕ := ([2618,2676,2758,2800,3072,3132,3150,3186,3192,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9039 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9039 4 (fun x => (if x<3150 then (if x<2800 then (if x<2676 then 0 else (if x<2758 then 0 else 1)) else (if x<3072 then 1 else (if x<3132 then 2 else 0))) else (if x<3214 then (if x<3186 then 1 else (if x<3192 then 0 else 1)) else (if x<3256 then (if x<3250 then 2 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9040 : Finset ℕ := ([2758,2800,3132,3186,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9040 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9040 3 (fun x => (if x<3186 then (if x<2800 then 0 else (if x<3132 then 0 else 1)) else (if x<3250 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9041 : Finset ℕ := ([2618,2676,2758,2800,3072,3126,3132,3150,3186,3192,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9041 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9041 3126 3
  · have he : independentCachedBranchMembers9041.erase 3126=independentCachedBranchMembers9039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9039
  · have he : independentCachedBranchMembers9041.filter (independentCachedEdge 3126)=independentCachedBranchMembers9040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9040
def independentCachedBranchMembers9042 : Finset ℕ := ([2618,2650,2668,2676,2726,2758,2772,2792,2800,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3214,3222,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9042 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9042 2772 4
  · have he : independentCachedBranchMembers9042.erase 2772=independentCachedBranchMembers9038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9038
  · have he : independentCachedBranchMembers9042.filter (independentCachedEdge 2772)=independentCachedBranchMembers9041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9041
def independentCachedBranchMembers9043 : Finset ℕ := ([2650,2668,2726,2792,3072,3150,3164,3178,3192,3222,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9043 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9043 4 (fun x => (if x<3164 then (if x<2792 then (if x<2668 then 0 else (if x<2726 then 0 else 1)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3222 then (if x<3178 then 2 else (if x<3192 then 2 else 0)) else (if x<3274 then (if x<3250 then 1 else 3) else (if x<3288 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9044 : Finset ℕ := ([2650,2668,3222,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9044 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9044 3 (fun x => (if x<3250 then (if x<2668 then 0 else (if x<3222 then 0 else 1)) else (if x<3274 then 2 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9045 : Finset ℕ := ([2650,2668,2726,2792,3072,3126,3150,3164,3178,3192,3222,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9045 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9045 3126 3
  · have he : independentCachedBranchMembers9045.erase 3126=independentCachedBranchMembers9043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9043
  · have he : independentCachedBranchMembers9045.filter (independentCachedEdge 3126)=independentCachedBranchMembers9044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9044
def independentCachedBranchMembers9046 : Finset ℕ := ([2618,2650,2668,2676,2726,2732,2758,2772,2792,2800,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3214,3222,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9046 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9046 2732 4
  · have he : independentCachedBranchMembers9046.erase 2732=independentCachedBranchMembers9042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9042
  · have he : independentCachedBranchMembers9046.filter (independentCachedEdge 2732)=independentCachedBranchMembers9045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9045
def independentCachedBranchMembers9047 : Finset ℕ := ([2618,2650,2668,2676,2726,2758,2792,2800,3132,3164,3178,3186,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9047 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9047 4 (fun x => (if x<3132 then (if x<2726 then (if x<2668 then (if x<2650 then 0 else 1) else (if x<2676 then 0 else 1)) else (if x<2792 then (if x<2758 then 0 else 1) else (if x<2800 then 1 else 0))) else (if x<3214 then (if x<3178 then (if x<3164 then 2 else 3) else (if x<3186 then 2 else 3)) else (if x<3256 then (if x<3222 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9048 : Finset ℕ := ([2618,2650,2668,2676,2726,2732,2758,2772,2792,2800,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3214,3222,3228,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9048 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9048 3228 4
  · have he : independentCachedBranchMembers9048.erase 3228=independentCachedBranchMembers9046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9046
  · have he : independentCachedBranchMembers9048.filter (independentCachedEdge 3228)=independentCachedBranchMembers9047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9047
def independentCachedBranchMembers9049 : Finset ℕ := ([2618,2620,2650,2652,2666,2668,2674,2676,2702,2710,2726,2732,2738,2744,2758,2762,2772,2776,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9049 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9049 2788 5
  · have he : independentCachedBranchMembers9049.erase 2788=independentCachedBranchMembers9037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9037
  · have he : independentCachedBranchMembers9049.filter (independentCachedEdge 2788)=independentCachedBranchMembers9048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9048
def independentCachedBranchMembers9050 : Finset ℕ := ([2620,2652,2666,2674,2702,2710,2744,2776,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3228,3238,3242,3250,3270,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9050 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9050 5 (fun x => (if x<3158 then (if x<2744 then (if x<2674 then (if x<2652 then 0 else (if x<2666 then 1 else 0)) else (if x<2702 then 1 else (if x<2710 then 0 else 1))) else (if x<3118 then (if x<2776 then 1 else (if x<3072 then 0 else 2)) else (if x<3130 then (if x<3126 then 0 else 2) else (if x<3150 then 3 else 2)))) else (if x<3242 then (if x<3188 then (if x<3162 then 1 else (if x<3180 then 4 else 3)) else (if x<3228 then (if x<3192 then 4 else 0) else (if x<3238 then 0 else 3))) else (if x<3274 then (if x<3250 then 2 else (if x<3270 then 1 else 4)) else (if x<3304 then (if x<3282 then 0 else 2) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9051 : Finset ℕ := ([2652,2666,2710,2776,3072,3150,3162,3180,3192,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9051 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9051 4 (fun x => (if x<3162 then (if x<2776 then (if x<2666 then 0 else (if x<2710 then 0 else 1)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3238 then (if x<3180 then 2 else (if x<3192 then 2 else 0)) else (if x<3274 then (if x<3250 then 1 else 3) else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9052 : Finset ℕ := ([2652,2666,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9052 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9052 3 (fun x => (if x<3250 then (if x<2666 then 0 else (if x<3238 then 0 else 1)) else (if x<3274 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9053 : Finset ℕ := ([2652,2666,2710,2776,3072,3126,3150,3162,3180,3192,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9053 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9053 3126 3
  · have he : independentCachedBranchMembers9053.erase 3126=independentCachedBranchMembers9051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9051
  · have he : independentCachedBranchMembers9053.filter (independentCachedEdge 3126)=independentCachedBranchMembers9052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9052
def independentCachedBranchMembers9054 : Finset ℕ := ([2620,2652,2666,2674,2702,2710,2744,2772,2776,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3228,3238,3242,3250,3270,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9054 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9054 2772 4
  · have he : independentCachedBranchMembers9054.erase 2772=independentCachedBranchMembers9050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9050
  · have he : independentCachedBranchMembers9054.filter (independentCachedEdge 2772)=independentCachedBranchMembers9053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9053
def independentCachedBranchMembers9055 : Finset ℕ := ([2620,2674,2702,2744,3072,3130,3150,3188,3192,3250,3270,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9055 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9055 4 (fun x => (if x<3150 then (if x<2744 then (if x<2674 then 0 else (if x<2702 then 0 else 1)) else (if x<3072 then 1 else (if x<3130 then 2 else 0))) else (if x<3250 then (if x<3188 then 1 else (if x<3192 then 0 else 1)) else (if x<3274 then (if x<3270 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
