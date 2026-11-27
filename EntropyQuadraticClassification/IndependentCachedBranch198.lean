/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch197
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9120 : Finset ℕ := ([2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3072,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9120 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9120 3242 4
  · have he : independentCachedBranchMembers9120.erase 3242=independentCachedBranchMembers9118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9118
  · have he : independentCachedBranchMembers9120.filter (independentCachedEdge 3242)=independentCachedBranchMembers9119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9119
def independentCachedBranchMembers9121 : Finset ℕ := ([2620,2650,2710,2732,2738,2762,2772,2800,3126,3150,3178,3188,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9121 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9121 4 (fun x => (if x<3126 then (if x<2738 then (if x<2710 then (if x<2650 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<2772 then (if x<2762 then 1 else 1) else (if x<2800 then 1 else 0))) else (if x<3228 then (if x<3178 then (if x<3150 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9122 : Finset ℕ := ([2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3072,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9122 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9122 3174 4
  · have he : independentCachedBranchMembers9122.erase 3174=independentCachedBranchMembers9120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9120
  · have he : independentCachedBranchMembers9122.filter (independentCachedEdge 3174)=independentCachedBranchMembers9121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9121
def independentCachedBranchMembers9123 : Finset ℕ := ([2668,2674,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3214,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9123 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9123 4 (fun x => (if x<3126 then (if x<2758 then (if x<2732 then (if x<2674 then 0 else 0) else (if x<2738 then 1 else 1)) else (if x<2772 then (if x<2762 then 0 else 1) else (if x<2776 then 1 else 0))) else (if x<3214 then (if x<3150 then (if x<3130 then 2 else 3) else (if x<3164 then 2 else 3)) else (if x<3300 then (if x<3228 then 3 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9124 : Finset ℕ := ([2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9124 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9124 3102 4
  · have he : independentCachedBranchMembers9124.erase 3102=independentCachedBranchMembers9122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9122
  · have he : independentCachedBranchMembers9124.filter (independentCachedEdge 3102)=independentCachedBranchMembers9123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9123
def independentCachedBranchMembers9125 : Finset ℕ := ([2674,2738,2758,2762,2800,3072,3126,3130,3150,3188,3192,3214,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9125 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9125 4 (fun x => (if x<3130 then (if x<2762 then (if x<2738 then 0 else (if x<2758 then 1 else 0)) else (if x<3072 then (if x<2800 then 1 else 2) else (if x<3126 then 3 else 1))) else (if x<3214 then (if x<3188 then (if x<3150 then 0 else 1) else (if x<3192 then 2 else 3)) else (if x<3256 then (if x<3252 then 0 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9126 : Finset ℕ := ([2758,2762,3072,3150,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9126 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9126 3 (fun x => (if x<3150 then (if x<2762 then 0 else (if x<3072 then 1 else 2)) else (if x<3214 then 0 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9127 : Finset ℕ := ([2620,2674,2738,2758,2762,2800,3072,3126,3130,3150,3188,3192,3214,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9127 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9127 2620 3
  · have he : independentCachedBranchMembers9127.erase 2620=independentCachedBranchMembers9125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9125
  · have he : independentCachedBranchMembers9127.filter (independentCachedEdge 2620)=independentCachedBranchMembers9126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9126
def independentCachedBranchMembers9128 : Finset ℕ := ([2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2786,2800,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9128 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9128 2786 4
  · have he : independentCachedBranchMembers9128.erase 2786=independentCachedBranchMembers9124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9124
  · have he : independentCachedBranchMembers9128.filter (independentCachedEdge 2786)=independentCachedBranchMembers9127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9127
def independentCachedBranchMembers9129 : Finset ℕ := ([2668,2710,2738,2762,2776,3072,3126,3150,3164,3178,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9129 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9129 4 (fun x => (if x<3150 then (if x<2762 then (if x<2710 then 0 else (if x<2738 then 1 else 2)) else (if x<3072 then (if x<2776 then 0 else 1) else (if x<3126 then 3 else 1))) else (if x<3238 then (if x<3178 then (if x<3164 then 0 else 2) else (if x<3192 then 3 else 1)) else (if x<3276 then (if x<3252 then 3 else 2) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9130 : Finset ℕ := ([2762,2776,3072,3126,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9130 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9130 3 (fun x => (if x<3126 then (if x<2776 then 0 else (if x<3072 then 1 else 2)) else (if x<3276 then 0 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9131 : Finset ℕ := ([2650,2668,2710,2738,2762,2776,3072,3126,3150,3164,3178,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9131 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9131 2650 3
  · have he : independentCachedBranchMembers9131.erase 2650=independentCachedBranchMembers9129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9129
  · have he : independentCachedBranchMembers9131.filter (independentCachedEdge 2650)=independentCachedBranchMembers9130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9130
def independentCachedBranchMembers9132 : Finset ℕ := ([2620,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9132 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9132 2714 4
  · have he : independentCachedBranchMembers9132.erase 2714=independentCachedBranchMembers9128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9128
  · have he : independentCachedBranchMembers9132.filter (independentCachedEdge 2714)=independentCachedBranchMembers9131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9131
def independentCachedBranchMembers9133 : Finset ℕ := ([2650,2674,2710,2732,2758,2772,3072,3130,3178,3192,3214,3228,3238,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound9133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9133 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9133 4 (fun x => (if x<3178 then (if x<2758 then (if x<2710 then (if x<2674 then 0 else 1) else (if x<2732 then 0 else 2)) else (if x<3072 then (if x<2772 then 1 else 2) else (if x<3130 then 3 else 1))) else (if x<3238 then (if x<3214 then (if x<3192 then 0 else 3) else (if x<3228 then 1 else 2)) else (if x<3276 then (if x<3252 then 0 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9134 : Finset ℕ := ([2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9134 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9134 2646 4
  · have he : independentCachedBranchMembers9134.erase 2646=independentCachedBranchMembers9132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9132
  · have he : independentCachedBranchMembers9134.filter (independentCachedEdge 2646)=independentCachedBranchMembers9133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9133
def independentCachedBranchMembers9135 : Finset ℕ := ([2620,2668,2732,2772,2776,2800,3072,3164,3188,3192,3228,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9135 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9135 4 (fun x => (if x<3188 then (if x<2776 then (if x<2732 then (if x<2668 then 0 else 1) else (if x<2772 then 2 else 0)) else (if x<3072 then (if x<2800 then 1 else 2) else (if x<3164 then 3 else 0))) else (if x<3256 then (if x<3228 then (if x<3192 then 3 else 1) else (if x<3252 then 3 else 0)) else (if x<3300 then (if x<3276 then 2 else 1) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9136 : Finset ℕ := ([2606,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9136 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9136 2606 4
  · have he : independentCachedBranchMembers9136.erase 2606=independentCachedBranchMembers9134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9134
  · have he : independentCachedBranchMembers9136.filter (independentCachedEdge 2606)=independentCachedBranchMembers9135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9135
def independentCachedBranchMembers9137 : Finset ℕ := ([2606,2614,2618,2620,2638,2646,2650,2652,2666,2668,2674,2676,2702,2710,2714,2716,2726,2732,2738,2744,2758,2762,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9137 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9137 2770 5
  · have he : independentCachedBranchMembers9137.erase 2770=independentCachedBranchMembers9115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9115
  · have he : independentCachedBranchMembers9137.filter (independentCachedEdge 2770)=independentCachedBranchMembers9136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9136
def independentCachedBranchMembers9138 : Finset ℕ := ([2652,2668,2674,2702,2732,2738,2758,2762,2772,2776,2792,3072,3118,3132,3158,3162,3178,3188,3192,3222,3226,3238,3242,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9138 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9138 5 (fun x => (if x<3158 then (if x<2762 then (if x<2702 then (if x<2668 then 0 else (if x<2674 then 1 else 0)) else (if x<2738 then (if x<2732 then 1 else 2) else (if x<2758 then 2 else 0))) else (if x<2792 then (if x<2772 then 2 else (if x<2776 then 1 else 3)) else (if x<3118 then (if x<3072 then 0 else 4) else (if x<3132 then 1 else 4)))) else (if x<3238 then (if x<3188 then (if x<3162 then 0 else (if x<3178 then 3 else 4)) else (if x<3222 then (if x<3192 then 1 else 0) else (if x<3226 then 1 else 4))) else (if x<3276 then (if x<3242 then 4 else (if x<3256 then 2 else 3)) else (if x<3298 then (if x<3282 then 0 else 2) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9139 : Finset ℕ := ([2674,2738,2758,2772,3072,3158,3188,3222,3238,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9139 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9139 4 (fun x => (if x<3188 then (if x<2772 then (if x<2738 then 0 else (if x<2758 then 1 else 0)) else (if x<3072 then 1 else (if x<3158 then 2 else 0))) else (if x<3282 then (if x<3222 then 2 else (if x<3238 then 1 else 2)) else (if x<3298 then 2 else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9140 : Finset ℕ := ([2618,2652,2668,2674,2702,2732,2738,2758,2762,2772,2776,2792,3072,3118,3132,3158,3162,3178,3188,3192,3222,3226,3238,3242,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9140 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9140 2618 4
  · have he : independentCachedBranchMembers9140.erase 2618=independentCachedBranchMembers9138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9138
  · have he : independentCachedBranchMembers9140.filter (independentCachedEdge 2618)=independentCachedBranchMembers9139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9139
def independentCachedBranchMembers9141 : Finset ℕ := ([2618,2652,2668,2674,2702,2758,2776,2792,3132,3162,3178,3188,3222,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9141 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9141 4 (fun x => (if x<3132 then (if x<2702 then (if x<2668 then (if x<2652 then 0 else 0) else (if x<2674 then 1 else 1)) else (if x<2776 then (if x<2758 then 0 else 1) else (if x<2792 then 1 else 0))) else (if x<3222 then (if x<3178 then (if x<3162 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9142 : Finset ℕ := ([2618,2652,2668,2674,2702,2732,2738,2758,2762,2772,2776,2792,3072,3118,3132,3158,3162,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9142 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9142 3252 4
  · have he : independentCachedBranchMembers9142.erase 3252=independentCachedBranchMembers9140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9140
  · have he : independentCachedBranchMembers9142.filter (independentCachedEdge 3252)=independentCachedBranchMembers9141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9141
def independentCachedBranchMembers9143 : Finset ℕ := ([2618,2652,2702,2732,2738,2762,2772,2792,3118,3158,3178,3188,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9143 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9143 4 (fun x => (if x<3118 then (if x<2738 then (if x<2702 then (if x<2652 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<2772 then (if x<2762 then 1 else 1) else (if x<2792 then 1 else 0))) else (if x<3226 then (if x<3178 then (if x<3158 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9144 : Finset ℕ := ([2618,2652,2668,2674,2702,2732,2738,2758,2762,2772,2776,2792,3072,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9144 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9144 3174 4
  · have he : independentCachedBranchMembers9144.erase 3174=independentCachedBranchMembers9142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9142
  · have he : independentCachedBranchMembers9144.filter (independentCachedEdge 3174)=independentCachedBranchMembers9143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9143
def independentCachedBranchMembers9145 : Finset ℕ := ([2668,2674,2732,2738,2758,2762,2772,2776,3118,3132,3158,3162,3222,3226,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9145 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9145 4 (fun x => (if x<3118 then (if x<2758 then (if x<2732 then (if x<2674 then 0 else 0) else (if x<2738 then 1 else 1)) else (if x<2772 then (if x<2762 then 0 else 1) else (if x<2776 then 1 else 0))) else (if x<3222 then (if x<3158 then (if x<3132 then 2 else 3) else (if x<3162 then 2 else 3)) else (if x<3298 then (if x<3226 then 3 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9146 : Finset ℕ := ([2618,2652,2668,2674,2702,2732,2738,2758,2762,2772,2776,2792,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9146 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9146 3102 4
  · have he : independentCachedBranchMembers9146.erase 3102=independentCachedBranchMembers9144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9144
  · have he : independentCachedBranchMembers9146.filter (independentCachedEdge 3102)=independentCachedBranchMembers9145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9145
def independentCachedBranchMembers9147 : Finset ℕ := ([2668,2732,2758,2772,2792,3072,3118,3132,3158,3178,3192,3222,3242,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9147 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9147 4 (fun x => (if x<3132 then (if x<2772 then (if x<2732 then 0 else (if x<2758 then 1 else 0)) else (if x<3072 then (if x<2792 then 1 else 2) else (if x<3118 then 3 else 1))) else (if x<3222 then (if x<3178 then (if x<3158 then 0 else 1) else (if x<3192 then 2 else 3)) else (if x<3256 then (if x<3242 then 0 else 3) else (if x<3282 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9148 : Finset ℕ := ([2758,2772,3072,3158,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9148 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9148 3 (fun x => (if x<3158 then (if x<2772 then 0 else (if x<3072 then 1 else 2)) else (if x<3222 then 0 else (if x<3282 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9149 : Finset ℕ := ([2618,2668,2732,2758,2772,2792,3072,3118,3132,3158,3178,3192,3222,3242,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9149 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9149 2618 3
  · have he : independentCachedBranchMembers9149.erase 2618=independentCachedBranchMembers9147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9147
  · have he : independentCachedBranchMembers9149.filter (independentCachedEdge 2618)=independentCachedBranchMembers9148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9148
def independentCachedBranchMembers9150 : Finset ℕ := ([2618,2652,2668,2674,2702,2732,2738,2758,2762,2772,2776,2788,2792,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9150 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9150 2788 4
  · have he : independentCachedBranchMembers9150.erase 2788=independentCachedBranchMembers9146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9146
  · have he : independentCachedBranchMembers9150.filter (independentCachedEdge 2788)=independentCachedBranchMembers9149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9149
def independentCachedBranchMembers9151 : Finset ℕ := ([2674,2702,2732,2772,2776,3072,3118,3158,3162,3188,3192,3238,3242,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9151 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9151 4 (fun x => (if x<3158 then (if x<2772 then (if x<2702 then 0 else (if x<2732 then 1 else 2)) else (if x<3072 then (if x<2776 then 0 else 1) else (if x<3118 then 3 else 1))) else (if x<3238 then (if x<3188 then (if x<3162 then 0 else 2) else (if x<3192 then 3 else 1)) else (if x<3282 then (if x<3242 then 3 else 2) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
