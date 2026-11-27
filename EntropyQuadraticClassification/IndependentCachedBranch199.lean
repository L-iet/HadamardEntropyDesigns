/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch198
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9152 : Finset ℕ := ([2772,2776,3072,3118,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9152 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9152 3 (fun x => (if x<3118 then (if x<2776 then 0 else (if x<3072 then 1 else 2)) else (if x<3282 then 0 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9153 : Finset ℕ := ([2652,2674,2702,2732,2772,2776,3072,3118,3158,3162,3188,3192,3238,3242,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9153 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9153 2652 3
  · have he : independentCachedBranchMembers9153.erase 2652=independentCachedBranchMembers9151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9151
  · have he : independentCachedBranchMembers9153.filter (independentCachedEdge 2652)=independentCachedBranchMembers9152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9152
def independentCachedBranchMembers9154 : Finset ℕ := ([2618,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9154 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9154 2716 4
  · have he : independentCachedBranchMembers9154.erase 2716=independentCachedBranchMembers9150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9150
  · have he : independentCachedBranchMembers9154.filter (independentCachedEdge 2716)=independentCachedBranchMembers9153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9153
def independentCachedBranchMembers9155 : Finset ℕ := ([2652,2668,2702,2738,2758,2762,3072,3132,3188,3192,3222,3226,3238,3242,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9155 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9155 4 (fun x => (if x<3188 then (if x<2758 then (if x<2702 then (if x<2668 then 0 else 1) else (if x<2738 then 0 else 2)) else (if x<3072 then (if x<2762 then 1 else 2) else (if x<3132 then 3 else 1))) else (if x<3238 then (if x<3222 then (if x<3192 then 0 else 3) else (if x<3226 then 1 else 2)) else (if x<3282 then (if x<3242 then 0 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9156 : Finset ℕ := ([2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9156 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9156 2638 4
  · have he : independentCachedBranchMembers9156.erase 2638=independentCachedBranchMembers9154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9154
  · have he : independentCachedBranchMembers9156.filter (independentCachedEdge 2638)=independentCachedBranchMembers9155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9155
def independentCachedBranchMembers9157 : Finset ℕ := ([2618,2674,2738,2762,2776,2792,3072,3162,3178,3192,3226,3242,3256,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9157 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9157 4 (fun x => (if x<3178 then (if x<2776 then (if x<2738 then (if x<2674 then 0 else 1) else (if x<2762 then 2 else 0)) else (if x<3072 then (if x<2792 then 1 else 2) else (if x<3162 then 3 else 0))) else (if x<3256 then (if x<3226 then (if x<3192 then 3 else 1) else (if x<3242 then 3 else 0)) else (if x<3298 then (if x<3282 then 2 else 1) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9158 : Finset ℕ := ([2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9158 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9158 2614 4
  · have he : independentCachedBranchMembers9158.erase 2614=independentCachedBranchMembers9156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9156
  · have he : independentCachedBranchMembers9158.filter (independentCachedEdge 2614)=independentCachedBranchMembers9157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9157
def independentCachedBranchMembers9159 : Finset ℕ := ([2606,2614,2618,2620,2638,2646,2650,2652,2666,2668,2674,2676,2702,2710,2714,2716,2726,2732,2738,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9159 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9159 2764 5
  · have he : independentCachedBranchMembers9159.erase 2764=independentCachedBranchMembers9137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9137
  · have he : independentCachedBranchMembers9159.filter (independentCachedEdge 2764)=independentCachedBranchMembers9158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9158
def independentCachedBranchMembers9160 : Finset ℕ := ([2650,2666,2676,2710,2726,2732,2738,2744,2762,2772,2800,3072,3118,3130,3158,3164,3180,3186,3192,3214,3226,3242,3252,3270,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9160 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9160 5 (fun x => (if x<3158 then (if x<2744 then (if x<2710 then (if x<2666 then 0 else (if x<2676 then 1 else 0)) else (if x<2732 then (if x<2726 then 0 else 1) else (if x<2738 then 2 else 2))) else (if x<2800 then (if x<2762 then 0 else (if x<2772 then 2 else 2)) else (if x<3118 then (if x<3072 then 1 else 3) else (if x<3130 then 1 else 3)))) else (if x<3242 then (if x<3186 then (if x<3164 then 0 else (if x<3180 then 3 else 4)) else (if x<3214 then (if x<3192 then 4 else 0) else (if x<3226 then 3 else 0))) else (if x<3282 then (if x<3252 then 2 else (if x<3270 then 0 else 4)) else (if x<3298 then (if x<3288 then 2 else 4) else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9161 : Finset ℕ := ([2676,2732,2744,2762,3072,3158,3186,3214,3226,3242,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9161 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9161 4 (fun x => (if x<3186 then (if x<2762 then (if x<2732 then 0 else (if x<2744 then 0 else 1)) else (if x<3072 then 1 else (if x<3158 then 2 else 0))) else (if x<3242 then (if x<3214 then 2 else (if x<3226 then 0 else 1)) else (if x<3288 then 2 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9162 : Finset ℕ := ([2620,2650,2666,2676,2710,2726,2732,2738,2744,2762,2772,2800,3072,3118,3130,3158,3164,3180,3186,3192,3214,3226,3242,3252,3270,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9162 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9162 2620 4
  · have he : independentCachedBranchMembers9162.erase 2620=independentCachedBranchMembers9160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9160
  · have he : independentCachedBranchMembers9162.filter (independentCachedEdge 2620)=independentCachedBranchMembers9161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9161
def independentCachedBranchMembers9163 : Finset ℕ := ([2620,2650,2666,2676,2710,2726,2744,2800,3130,3164,3180,3186,3214,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9163 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9163 4 (fun x => (if x<3130 then (if x<2710 then (if x<2666 then (if x<2650 then 0 else 0) else (if x<2676 then 1 else 1)) else (if x<2744 then (if x<2726 then 0 else 1) else (if x<2800 then 1 else 0))) else (if x<3214 then (if x<3180 then (if x<3164 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3288 then (if x<3270 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9164 : Finset ℕ := ([2620,2650,2666,2676,2710,2726,2732,2738,2744,2762,2772,2800,3072,3118,3130,3158,3164,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9164 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9164 3276 4
  · have he : independentCachedBranchMembers9164.erase 3276=independentCachedBranchMembers9162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9162
  · have he : independentCachedBranchMembers9164.filter (independentCachedEdge 3276)=independentCachedBranchMembers9163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9163
def independentCachedBranchMembers9165 : Finset ℕ := ([2620,2650,2710,2732,2738,2762,2772,2800,3118,3158,3180,3186,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9165 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9165 4 (fun x => (if x<3118 then (if x<2738 then (if x<2710 then (if x<2650 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<2772 then (if x<2762 then 1 else 1) else (if x<2800 then 1 else 0))) else (if x<3226 then (if x<3180 then (if x<3158 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3288 then (if x<3270 then 2 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9166 : Finset ℕ := ([2620,2650,2666,2676,2710,2726,2732,2738,2744,2762,2772,2800,3072,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9166 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9166 3174 4
  · have he : independentCachedBranchMembers9166.erase 3174=independentCachedBranchMembers9164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9164
  · have he : independentCachedBranchMembers9166.filter (independentCachedEdge 3174)=independentCachedBranchMembers9165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9165
def independentCachedBranchMembers9167 : Finset ℕ := ([2666,2676,2726,2732,2738,2744,2762,2772,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9167 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9167 4 (fun x => (if x<3118 then (if x<2738 then (if x<2726 then (if x<2676 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<2762 then (if x<2744 then 1 else 0) else (if x<2772 then 1 else 1))) else (if x<3214 then (if x<3158 then (if x<3130 then 2 else 3) else (if x<3164 then 2 else 3)) else (if x<3298 then (if x<3226 then 3 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9168 : Finset ℕ := ([2620,2650,2666,2676,2710,2726,2732,2738,2744,2762,2772,2800,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9168 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9168 3102 4
  · have he : independentCachedBranchMembers9168.erase 3102=independentCachedBranchMembers9166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9166
  · have he : independentCachedBranchMembers9168.filter (independentCachedEdge 3102)=independentCachedBranchMembers9167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9167
def independentCachedBranchMembers9169 : Finset ℕ := ([2676,2726,2732,2772,2800,3072,3118,3158,3164,3186,3192,3214,3242,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9169 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9169 4 (fun x => (if x<3158 then (if x<2772 then (if x<2726 then 0 else (if x<2732 then 0 else 1)) else (if x<3072 then (if x<2800 then 1 else 2) else (if x<3118 then 3 else 1))) else (if x<3214 then (if x<3186 then (if x<3164 then 1 else 0) else (if x<3192 then 2 else 3)) else (if x<3282 then (if x<3242 then 0 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9170 : Finset ℕ := ([2726,2732,3072,3118,3214,3242] : List ℕ).toFinset
theorem independentCachedBranchBound9170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9170 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9170 3 (fun x => (if x<3118 then (if x<2732 then 0 else (if x<3072 then 1 else 2)) else (if x<3214 then 0 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9171 : Finset ℕ := ([2650,2676,2726,2732,2772,2800,3072,3118,3158,3164,3186,3192,3214,3242,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9171 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9171 2650 3
  · have he : independentCachedBranchMembers9171.erase 2650=independentCachedBranchMembers9169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9169
  · have he : independentCachedBranchMembers9171.filter (independentCachedEdge 2650)=independentCachedBranchMembers9170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9170
def independentCachedBranchMembers9172 : Finset ℕ := ([2620,2650,2666,2676,2710,2726,2732,2738,2744,2762,2772,2788,2800,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9172 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9172 2788 4
  · have he : independentCachedBranchMembers9172.erase 2788=independentCachedBranchMembers9168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9168
  · have he : independentCachedBranchMembers9172.filter (independentCachedEdge 2788)=independentCachedBranchMembers9171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9171
def independentCachedBranchMembers9173 : Finset ℕ := ([2666,2710,2732,2744,2772,3072,3118,3130,3158,3180,3192,3242,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9173 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9173 4 (fun x => (if x<3130 then (if x<2744 then (if x<2710 then 0 else (if x<2732 then 1 else 0)) else (if x<3072 then (if x<2772 then 1 else 2) else (if x<3118 then 3 else 0))) else (if x<3242 then (if x<3180 then (if x<3158 then 2 else 1) else (if x<3192 then 3 else 1)) else (if x<3282 then (if x<3270 then 3 else 3) else (if x<3304 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9174 : Finset ℕ := ([2732,2744,3072,3158,3242,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9174 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9174 3 (fun x => (if x<3158 then (if x<2744 then 0 else (if x<3072 then 1 else 2)) else (if x<3242 then 0 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9175 : Finset ℕ := ([2620,2666,2710,2732,2744,2772,3072,3118,3130,3158,3180,3192,3242,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9175 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9175 2620 3
  · have he : independentCachedBranchMembers9175.erase 2620=independentCachedBranchMembers9173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9173
  · have he : independentCachedBranchMembers9175.filter (independentCachedEdge 2620)=independentCachedBranchMembers9174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9174
def independentCachedBranchMembers9176 : Finset ℕ := ([2620,2650,2666,2676,2710,2716,2726,2732,2738,2744,2762,2772,2788,2800,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9176 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9176 2716 4
  · have he : independentCachedBranchMembers9176.erase 2716=independentCachedBranchMembers9172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9172
  · have he : independentCachedBranchMembers9176.filter (independentCachedEdge 2716)=independentCachedBranchMembers9175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9175
def independentCachedBranchMembers9177 : Finset ℕ := ([2650,2666,2738,2744,2762,2800,3072,3130,3186,3192,3226,3242,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9177 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9177 4 (fun x => (if x<3186 then (if x<2762 then (if x<2738 then (if x<2666 then 0 else 1) else (if x<2744 then 0 else 1)) else (if x<3072 then (if x<2800 then 2 else 2) else (if x<3130 then 3 else 0))) else (if x<3282 then (if x<3226 then (if x<3192 then 3 else 1) else (if x<3242 then 3 else 1)) else (if x<3298 then (if x<3288 then 0 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9178 : Finset ℕ := ([2620,2638,2650,2666,2676,2710,2716,2726,2732,2738,2744,2762,2772,2788,2800,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9178 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9178 2638 4
  · have he : independentCachedBranchMembers9178.erase 2638=independentCachedBranchMembers9176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9176
  · have he : independentCachedBranchMembers9178.filter (independentCachedEdge 2638)=independentCachedBranchMembers9177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9177
def independentCachedBranchMembers9179 : Finset ℕ := ([2620,2676,2710,2726,2738,2762,3072,3164,3180,3192,3214,3226,3242,3270,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound9179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9179 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9179 4 (fun x => (if x<3180 then (if x<2738 then (if x<2710 then (if x<2676 then 0 else 1) else (if x<2726 then 0 else 1)) else (if x<3072 then (if x<2762 then 2 else 2) else (if x<3164 then 3 else 1))) else (if x<3242 then (if x<3214 then (if x<3192 then 0 else 3) else (if x<3226 then 1 else 2)) else (if x<3282 then (if x<3270 then 3 else 0) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9180 : Finset ℕ := ([2614,2620,2638,2650,2666,2676,2710,2716,2726,2732,2738,2744,2762,2772,2788,2800,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9180 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9180 2614 4
  · have he : independentCachedBranchMembers9180.erase 2614=independentCachedBranchMembers9178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9178
  · have he : independentCachedBranchMembers9180.filter (independentCachedEdge 2614)=independentCachedBranchMembers9179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9179
def independentCachedBranchMembers9181 : Finset ℕ := ([2606,2614,2618,2620,2638,2646,2650,2652,2666,2668,2674,2676,2702,2710,2714,2716,2726,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9181 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9181 2740 5
  · have he : independentCachedBranchMembers9181.erase 2740=independentCachedBranchMembers9159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9159
  · have he : independentCachedBranchMembers9181.filter (independentCachedEdge 2740)=independentCachedBranchMembers9180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9180
def independentCachedBranchMembers9182 : Finset ℕ := ([2652,2666,2676,2702,2726,2732,2738,2744,2762,2772,2792,3072,3126,3132,3150,3162,3180,3186,3192,3222,3228,3242,3252,3270,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9182 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9182 5 (fun x => (if x<3150 then (if x<2744 then (if x<2702 then (if x<2666 then 0 else (if x<2676 then 0 else 1)) else (if x<2732 then (if x<2726 then 0 else 1) else (if x<2738 then 2 else 2))) else (if x<2792 then (if x<2762 then 0 else (if x<2772 then 2 else 2)) else (if x<3126 then (if x<3072 then 1 else 3) else (if x<3132 then 1 else 3)))) else (if x<3242 then (if x<3186 then (if x<3162 then 0 else (if x<3180 then 3 else 4)) else (if x<3222 then (if x<3192 then 4 else 0) else (if x<3228 then 3 else 0))) else (if x<3276 then (if x<3252 then 0 else (if x<3270 then 2 else 4)) else (if x<3300 then (if x<3288 then 2 else 4) else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9183 : Finset ℕ := ([2666,2738,2744,2772,3072,3150,3180,3222,3228,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9183 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9183 4 (fun x => (if x<3180 then (if x<2772 then (if x<2738 then 0 else (if x<2744 then 0 else 1)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3252 then (if x<3222 then 2 else (if x<3228 then 0 else 1)) else (if x<3288 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
