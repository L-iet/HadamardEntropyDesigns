/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch192
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8960 : Finset ℕ := ([2666,2668,2674,2676,2726,2744,2762,2772,3118,3126,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound8960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8960 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8960 5 (fun x => (if x<3174 then (if x<2762 then (if x<2676 then (if x<2668 then 0 else (if x<2674 then 1 else 1)) else (if x<2726 then 0 else (if x<2744 then 0 else 0))) else (if x<3126 then (if x<2772 then 1 else (if x<3118 then 1 else 2)) else (if x<3162 then 3 else (if x<3164 then 2 else 3)))) else (if x<3250 then (if x<3222 then (if x<3192 then 0 else (if x<3214 then 0 else 3)) else (if x<3242 then 2 else (if x<3244 then 0 else 4))) else (if x<3288 then (if x<3252 then 4 else (if x<3270 then 0 else 4)) else (if x<3298 then 4 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8961 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3180,3186,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8961 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8961 3238 5
  · have he : independentCachedBranchMembers8961.erase 3238=independentCachedBranchMembers8959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8959
  · have he : independentCachedBranchMembers8961.filter (independentCachedEdge 3238)=independentCachedBranchMembers8960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8960
def independentCachedBranchMembers8962 : Finset ℕ := ([2666,2676,2726,2732,2738,2744,2758,2776,3126,3132,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3274,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8962 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8962 5 (fun x => (if x<3174 then (if x<2758 then (if x<2732 then (if x<2676 then 0 else (if x<2726 then 0 else 0)) else (if x<2738 then 1 else (if x<2744 then 1 else 0))) else (if x<3132 then (if x<2776 then 1 else (if x<3126 then 1 else 2)) else (if x<3158 then 3 else (if x<3164 then 3 else 2)))) else (if x<3242 then (if x<3192 then (if x<3180 then 0 else (if x<3186 then 4 else 4)) else (if x<3214 then 0 else (if x<3226 then 2 else 3))) else (if x<3284 then (if x<3252 then 0 else (if x<3274 then 0 else 4)) else (if x<3300 then 4 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8963 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8963 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8963 3188 5
  · have he : independentCachedBranchMembers8963.erase 3188=independentCachedBranchMembers8961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8961
  · have he : independentCachedBranchMembers8963.filter (independentCachedEdge 3188)=independentCachedBranchMembers8962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8962
def independentCachedBranchMembers8964 : Finset ℕ := ([2666,2676,2726,2732,2738,2744,2758,2776,3118,3130,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8964 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8964 5 (fun x => (if x<3174 then (if x<2758 then (if x<2732 then (if x<2676 then 0 else (if x<2726 then 0 else 0)) else (if x<2738 then 1 else (if x<2744 then 1 else 0))) else (if x<3130 then (if x<2776 then 1 else (if x<3118 then 1 else 2)) else (if x<3150 then 3 else (if x<3162 then 3 else 2)))) else (if x<3242 then (if x<3192 then (if x<3180 then 0 else (if x<3186 then 4 else 4)) else (if x<3222 then 0 else (if x<3228 then 2 else 3))) else (if x<3284 then (if x<3252 then 0 else (if x<3274 then 0 else 4)) else (if x<3298 then 4 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8965 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8965 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8965 3178 5
  · have he : independentCachedBranchMembers8965.erase 3178=independentCachedBranchMembers8963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8963
  · have he : independentCachedBranchMembers8965.filter (independentCachedEdge 3178)=independentCachedBranchMembers8964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8964
def independentCachedBranchMembers8966 : Finset ℕ := ([2676,2738,2776,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3222,3226,3228,3238,3242,3244,3270,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8966 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8966 5 (fun x => (if x<3178 then (if x<3130 then (if x<2776 then (if x<2738 then 0 else 0) else (if x<3072 then 0 else (if x<3126 then 1 else 0))) else (if x<3162 then (if x<3132 then 1 else (if x<3158 then 2 else 1)) else (if x<3164 then 2 else (if x<3174 then 0 else 2)))) else (if x<3242 then (if x<3226 then (if x<3180 then 3 else (if x<3222 then 1 else 2)) else (if x<3228 then 0 else (if x<3238 then 1 else 1))) else (if x<3274 then (if x<3244 then 2 else (if x<3270 then 3 else 3)) else (if x<3276 then 1 else (if x<3312 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8967 : Finset ℕ := ([2676,2776,3072,3126,3132,3162,3174,3180,3226,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8967 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8967 4 (fun x => (if x<3174 then (if x<3126 then (if x<2776 then 0 else (if x<3072 then 0 else 1)) else (if x<3132 then 0 else (if x<3162 then 1 else 1))) else (if x<3238 then (if x<3180 then 1 else (if x<3226 then 2 else 0)) else (if x<3244 then 2 else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8968 : Finset ℕ := ([2676,2738,2772,2776,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3222,3226,3228,3238,3242,3244,3270,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8968 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8968 2772 4
  · have he : independentCachedBranchMembers8968.erase 2772=independentCachedBranchMembers8966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8966
  · have he : independentCachedBranchMembers8968.filter (independentCachedEdge 2772)=independentCachedBranchMembers8967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8967
def independentCachedBranchMembers8969 : Finset ℕ := ([2738,2776,3072,3126,3162,3164,3178,3180,3222,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8969 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8969 4 (fun x => (if x<3178 then (if x<3126 then (if x<2776 then 0 else (if x<3072 then 0 else 1)) else (if x<3162 then 0 else (if x<3164 then 1 else 0))) else (if x<3238 then (if x<3180 then 2 else (if x<3222 then 1 else 3)) else (if x<3274 then 2 else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8970 : Finset ℕ := ([2676,2738,2744,2772,2776,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3222,3226,3228,3238,3242,3244,3270,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8970 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8970 2744 4
  · have he : independentCachedBranchMembers8970.erase 2744=independentCachedBranchMembers8968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8968
  · have he : independentCachedBranchMembers8970.filter (independentCachedEdge 2744)=independentCachedBranchMembers8969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8969
def independentCachedBranchMembers8971 : Finset ℕ := ([2676,2738,3072,3132,3164,3180,3222,3226,3238,3242,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8971 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8971 4 (fun x => (if x<3222 then (if x<3132 then (if x<2738 then 0 else (if x<3072 then 0 else 1)) else (if x<3164 then 1 else (if x<3180 then 0 else 2))) else (if x<3242 then (if x<3226 then 1 else (if x<3238 then 0 else 2)) else (if x<3270 then 1 else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8972 : Finset ℕ := ([2674,2676,2738,2744,2772,2776,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3222,3226,3228,3238,3242,3244,3270,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8972 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8972 2674 4
  · have he : independentCachedBranchMembers8972.erase 2674=independentCachedBranchMembers8970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8970
  · have he : independentCachedBranchMembers8972.filter (independentCachedEdge 2674)=independentCachedBranchMembers8971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8971
def independentCachedBranchMembers8973 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,2800,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8973 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8973 2800 5
  · have he : independentCachedBranchMembers8973.erase 2800=independentCachedBranchMembers8965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8965
  · have he : independentCachedBranchMembers8973.filter (independentCachedEdge 2800)=independentCachedBranchMembers8972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8972
def independentCachedBranchMembers8974 : Finset ℕ := ([2668,2726,2738,2758,2772,3072,3118,3130,3132,3150,3162,3164,3174,3186,3188,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8974 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8974 5 (fun x => (if x<3174 then (if x<3118 then (if x<2758 then (if x<2726 then 0 else (if x<2738 then 0 else 1)) else (if x<2772 then 1 else (if x<3072 then 0 else 2))) else (if x<3150 then (if x<3130 then 0 else (if x<3132 then 1 else 2)) else (if x<3162 then 1 else (if x<3164 then 2 else 0)))) else (if x<3256 then (if x<3222 then (if x<3186 then 2 else (if x<3188 then 3 else 4)) else (if x<3242 then 0 else (if x<3244 then 2 else 4))) else (if x<3288 then (if x<3274 then 3 else (if x<3276 then 3 else 2)) else (if x<3300 then (if x<3298 then 4 else 1) else (if x<3312 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8975 : Finset ℕ := ([2668,2772,3072,3132,3164,3188,3244,3256,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8975 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8975 4 (fun x => (if x<3244 then (if x<3132 then (if x<2772 then 0 else (if x<3072 then 0 else 1)) else (if x<3164 then 1 else (if x<3188 then 0 else 2))) else (if x<3288 then (if x<3256 then 2 else (if x<3276 then 3 else 1)) else (if x<3300 then 2 else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8976 : Finset ℕ := ([2666,2668,2726,2738,2758,2772,3072,3118,3130,3132,3150,3162,3164,3174,3186,3188,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8976 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8976 2666 4
  · have he : independentCachedBranchMembers8976.erase 2666=independentCachedBranchMembers8974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8974
  · have he : independentCachedBranchMembers8976.filter (independentCachedEdge 2666)=independentCachedBranchMembers8975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8975
def independentCachedBranchMembers8977 : Finset ℕ := ([2666,2668,2674,2676,2710,2726,2732,2738,2744,2758,2762,2772,2776,2800,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8977 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8977 2710 5
  · have he : independentCachedBranchMembers8977.erase 2710=independentCachedBranchMembers8973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8973
  · have he : independentCachedBranchMembers8977.filter (independentCachedEdge 2710)=independentCachedBranchMembers8976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8976
def independentCachedBranchMembers8978 : Finset ℕ := ([2674,2726,2732,2762,2776,3072,3118,3126,3132,3162,3174,3180,3188,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8978 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8978 5 (fun x => (if x<3188 then (if x<3118 then (if x<2762 then (if x<2726 then 0 else (if x<2732 then 0 else 1)) else (if x<2776 then 0 else (if x<3072 then 1 else 2))) else (if x<3162 then (if x<3126 then 1 else (if x<3132 then 0 else 2)) else (if x<3174 then 0 else (if x<3180 then 2 else 3)))) else (if x<3256 then (if x<3228 then (if x<3214 then 4 else (if x<3222 then 0 else 2)) else (if x<3242 then 1 else (if x<3250 then 2 else 4))) else (if x<3284 then (if x<3270 then 3 else (if x<3276 then 4 else 2)) else (if x<3304 then (if x<3298 then 3 else 0) else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8979 : Finset ℕ := ([2674,2762,3072,3126,3132,3188,3214,3250,3256,3270,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8979 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8979 4 (fun x => (if x<3214 then (if x<3126 then (if x<2762 then 0 else (if x<3072 then 0 else 1)) else (if x<3132 then 0 else (if x<3188 then 1 else 2))) else (if x<3270 then (if x<3250 then 0 else (if x<3256 then 1 else 2)) else (if x<3276 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8980 : Finset ℕ := ([2666,2674,2726,2732,2762,2776,3072,3118,3126,3132,3162,3174,3180,3188,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8980 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8980 2666 4
  · have he : independentCachedBranchMembers8980.erase 2666=independentCachedBranchMembers8978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8978
  · have he : independentCachedBranchMembers8980.filter (independentCachedEdge 2666)=independentCachedBranchMembers8979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8979
def independentCachedBranchMembers8981 : Finset ℕ := ([2650,2666,2668,2674,2676,2710,2726,2732,2738,2744,2758,2762,2772,2776,2800,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8981 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8981 2650 5
  · have he : independentCachedBranchMembers8981.erase 2650=independentCachedBranchMembers8977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8977
  · have he : independentCachedBranchMembers8981.filter (independentCachedEdge 2650)=independentCachedBranchMembers8980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8980
def independentCachedBranchMembers8982 : Finset ℕ := ([2676,2732,2758,3072,3132,3150,3158,3162,3174,3178,3186,3214,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8982 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8982 5 (fun x => (if x<3214 then (if x<3150 then (if x<2758 then (if x<2732 then 0 else 0) else (if x<3072 then 0 else (if x<3132 then 1 else 0))) else (if x<3174 then (if x<3158 then 1 else (if x<3162 then 0 else 2)) else (if x<3178 then 2 else (if x<3186 then 3 else 1)))) else (if x<3276 then (if x<3238 then (if x<3222 then 0 else (if x<3226 then 1 else 3)) else (if x<3242 then 3 else (if x<3250 then 1 else 2))) else (if x<3300 then (if x<3284 then 3 else (if x<3288 then 2 else 1)) else (if x<3304 then 0 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8983 : Finset ℕ := ([2676,2758,3072,3158,3174,3186,3222,3238,3250,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8983 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8983 4 (fun x => (if x<3222 then (if x<3158 then (if x<2758 then 0 else (if x<3072 then 0 else 1)) else (if x<3174 then 0 else (if x<3186 then 1 else 2))) else (if x<3284 then (if x<3238 then 1 else (if x<3250 then 2 else 3)) else (if x<3300 then 2 else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8984 : Finset ℕ := ([2676,2732,2758,2762,3072,3132,3150,3158,3162,3174,3178,3186,3214,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8984 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8984 2762 4
  · have he : independentCachedBranchMembers8984.erase 2762=independentCachedBranchMembers8982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8982
  · have he : independentCachedBranchMembers8984.filter (independentCachedEdge 2762)=independentCachedBranchMembers8983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8983
def independentCachedBranchMembers8985 : Finset ℕ := ([2732,2758,3072,3162,3178,3186,3214,3222,3238,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound8985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8985 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8985 4 (fun x => (if x<3214 then (if x<3162 then (if x<2758 then 0 else (if x<3072 then 0 else 1)) else (if x<3178 then 1 else (if x<3186 then 2 else 3))) else (if x<3276 then (if x<3222 then 0 else (if x<3238 then 1 else 2)) else (if x<3284 then 1 else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8986 : Finset ℕ := ([2676,2732,2744,2758,2762,3072,3132,3150,3158,3162,3174,3178,3186,3214,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8986 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8986 2744 4
  · have he : independentCachedBranchMembers8986.erase 2744=independentCachedBranchMembers8984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8984
  · have he : independentCachedBranchMembers8986.filter (independentCachedEdge 2744)=independentCachedBranchMembers8985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8985
def independentCachedBranchMembers8987 : Finset ℕ := ([2676,2732,3072,3158,3162,3186,3214,3238,3242,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8987 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8987 4 (fun x => (if x<3214 then (if x<3158 then (if x<2732 then 0 else (if x<3072 then 0 else 1)) else (if x<3162 then 0 else (if x<3186 then 1 else 2))) else (if x<3284 then (if x<3238 then 0 else (if x<3242 then 2 else 1)) else (if x<3288 then 2 else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8988 : Finset ℕ := ([2668,2676,2732,2744,2758,2762,3072,3132,3150,3158,3162,3174,3178,3186,3214,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8988 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8988 2668 4
  · have he : independentCachedBranchMembers8988.erase 2668=independentCachedBranchMembers8986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8986
  · have he : independentCachedBranchMembers8988.filter (independentCachedEdge 2668)=independentCachedBranchMembers8987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8987
def independentCachedBranchMembers8989 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2710,2726,2732,2738,2744,2758,2762,2772,2776,2800,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8989 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8989 2620 5
  · have he : independentCachedBranchMembers8989.erase 2620=independentCachedBranchMembers8981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8981
  · have he : independentCachedBranchMembers8989.filter (independentCachedEdge 2620)=independentCachedBranchMembers8988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8988
def independentCachedBranchMembers8990 : Finset ℕ := ([2732,2738,2762,2772,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8990 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8990 5 (fun x => (if x<3162 then (if x<3126 then (if x<2762 then (if x<2738 then 0 else 0) else (if x<2772 then 0 else (if x<3118 then 0 else 1))) else (if x<3132 then (if x<3130 then 2 else 3) else (if x<3150 then 4 else (if x<3158 then 2 else 1)))) else (if x<3228 then (if x<3214 then (if x<3164 then 4 else 3) else (if x<3222 then 3 else (if x<3226 then 4 else 1))) else (if x<3300 then (if x<3298 then 2 else 1) else (if x<3304 then 2 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8991 : Finset ℕ := ([2762,2772,3130,3132,3150,3158,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound8991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8991 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8991 4 (fun x => (if x<3158 then (if x<3130 then (if x<2772 then 0 else 0) else (if x<3132 then 1 else (if x<3150 then 2 else 1))) else (if x<3222 then (if x<3214 then 2 else 2) else (if x<3298 then 1 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
