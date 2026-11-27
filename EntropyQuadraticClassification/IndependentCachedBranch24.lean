/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch23
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3072 : Finset ℕ := ([40,250,252,1594,1596,1642,1644,1708,1720,1768,2618,2620,2668,2680,2730,2732,2792,3118,3132,3178,3192,3242,3244,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3072 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3072 1596 4
  · have he : independentCachedBranchMembers3072.erase 1596=independentCachedBranchMembers3070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3070
  · have he : independentCachedBranchMembers3072.filter (independentCachedEdge 1596)=independentCachedBranchMembers3071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3071
def independentCachedBranchMembers3073 : Finset ℕ := ([250,1594,1644,1720,2618,2668,2730,3118,3132,3178,3192,3244,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3073 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3073 4 (fun x => (if x<2730 then (if x<1720 then (if x<1594 then 0 else (if x<1644 then 0 else 1)) else (if x<2618 then 1 else (if x<2668 then 2 else 2))) else (if x<3178 then (if x<3118 then 0 else (if x<3132 then 2 else 1)) else (if x<3244 then (if x<3192 then 0 else 2) else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3074 : Finset ℕ := ([40,250,252,1594,1596,1642,1644,1708,1720,1768,2618,2620,2668,2680,2730,2732,2792,3118,3132,3178,3180,3192,3242,3244,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3074 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3074 3180 4
  · have he : independentCachedBranchMembers3074.erase 3180=independentCachedBranchMembers3072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3072
  · have he : independentCachedBranchMembers3074.filter (independentCachedEdge 3180)=independentCachedBranchMembers3073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3073
def independentCachedBranchMembers3075 : Finset ℕ := ([250,252,1720,1768,2618,2620,2668,2730,2732,3118,3192,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3075 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3075 4 (fun x => (if x<2668 then (if x<1768 then (if x<252 then 0 else (if x<1720 then 1 else 0)) else (if x<2618 then 1 else (if x<2620 then 0 else 2))) else (if x<3118 then (if x<2730 then 1 else (if x<2732 then 2 else 3)) else (if x<3256 then (if x<3192 then 2 else 0) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3076 : Finset ℕ := ([40,250,252,1594,1596,1642,1644,1708,1720,1768,2606,2618,2620,2668,2680,2730,2732,2792,3118,3132,3178,3180,3192,3242,3244,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3076 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3076 2606 4
  · have he : independentCachedBranchMembers3076.erase 2606=independentCachedBranchMembers3074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3074
  · have he : independentCachedBranchMembers3076.filter (independentCachedEdge 2606)=independentCachedBranchMembers3075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3075
def independentCachedBranchMembers3077 : Finset ℕ := ([40,72,222,250,252,1594,1596,1626,1628,1642,1644,1678,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3077 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3077 222 5
  · have he : independentCachedBranchMembers3077.erase 222=independentCachedBranchMembers3069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3069
  · have he : independentCachedBranchMembers3077.filter (independentCachedEdge 222)=independentCachedBranchMembers3076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3076
def independentCachedBranchMembers3078 : Finset ℕ := ([40,72,250,1594,1626,1642,1720,1738,1752,1768,2618,2680,2730,2762,2776,2792,3162,3178,3192,3226,3242,3256,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3078 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3078 5 (fun x => (if x<2730 then (if x<1720 then (if x<1594 then (if x<72 then 0 else (if x<250 then 1 else 0)) else (if x<1626 then 0 else (if x<1642 then 1 else 2))) else (if x<1768 then (if x<1738 then 2 else (if x<1752 then 3 else 4)) else (if x<2618 then 0 else (if x<2680 then 2 else 0)))) else (if x<3192 then (if x<2792 then (if x<2762 then 0 else (if x<2776 then 1 else 3)) else (if x<3162 then 2 else (if x<3178 then 3 else 0))) else (if x<3256 then (if x<3226 then 2 else (if x<3242 then 4 else 2)) else (if x<3288 then 0 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3079 : Finset ℕ := ([40,72,1642,1768,2618,2730,2762,2776,3178,3192,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3079 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3079 4 (fun x => (if x<2762 then (if x<1768 then (if x<72 then 0 else (if x<1642 then 1 else 0)) else (if x<2618 then 1 else (if x<2730 then 0 else 2))) else (if x<3192 then (if x<2776 then 1 else (if x<3178 then 2 else 1)) else (if x<3226 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3080 : Finset ℕ := ([40,72,250,1594,1626,1642,1720,1738,1752,1768,2618,2680,2714,2730,2762,2776,2792,3162,3178,3192,3226,3242,3256,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3080 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3080 2714 4
  · have he : independentCachedBranchMembers3080.erase 2714=independentCachedBranchMembers3078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3078
  · have he : independentCachedBranchMembers3080.filter (independentCachedEdge 2714)=independentCachedBranchMembers3079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3079
def independentCachedBranchMembers3081 : Finset ℕ := ([40,1594,1720,1738,2618,2680,2762,3162,3178,3226,3242,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3081 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3081 4 (fun x => (if x<2762 then (if x<1738 then (if x<1594 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2680 then 2 else 0))) else (if x<3226 then (if x<3162 then 2 else (if x<3178 then 2 else 0)) else (if x<3288 then (if x<3242 then 1 else 2) else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3082 : Finset ℕ := ([40,72,250,1594,1626,1642,1720,1738,1752,1768,2618,2680,2714,2730,2762,2776,2792,3162,3178,3192,3226,3242,3256,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3082 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3082 3274 4
  · have he : independentCachedBranchMembers3082.erase 3274=independentCachedBranchMembers3080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3080
  · have he : independentCachedBranchMembers3082.filter (independentCachedEdge 3274)=independentCachedBranchMembers3081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3081
def independentCachedBranchMembers3083 : Finset ℕ := ([40,1626,1720,1768,2618,2680,2714,2762,2776,3162,3242,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3083 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3083 4 (fun x => (if x<2714 then (if x<1768 then (if x<1626 then 0 else (if x<1720 then 1 else 0)) else (if x<2618 then 1 else (if x<2680 then 0 else 1))) else (if x<3162 then (if x<2762 then 2 else (if x<2776 then 1 else 3)) else (if x<3256 then (if x<3242 then 2 else 0) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3084 : Finset ℕ := ([40,72,250,1594,1626,1642,1720,1738,1752,1768,2618,2650,2680,2714,2730,2762,2776,2792,3162,3178,3192,3226,3242,3256,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3084 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3084 2650 4
  · have he : independentCachedBranchMembers3084.erase 2650=independentCachedBranchMembers3082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3082
  · have he : independentCachedBranchMembers3084.filter (independentCachedEdge 2650)=independentCachedBranchMembers3083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3083
def independentCachedBranchMembers3085 : Finset ℕ := ([12,40,72,222,250,252,1594,1596,1626,1628,1642,1644,1678,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3085 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3085 12 5
  · have he : independentCachedBranchMembers3085.erase 12=independentCachedBranchMembers3077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3077
  · have he : independentCachedBranchMembers3085.filter (independentCachedEdge 12)=independentCachedBranchMembers3084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3084
def independentCachedBranchMembers3086 : Finset ℕ := ([40,72,250,1596,1628,1642,1678,1708,1720,1740,1752,2618,2638,2668,2680,2716,2730,2762,2792,3118,3162,3180,3192,3228,3242,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3086 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3086 5 (fun x => (if x<2668 then (if x<1678 then (if x<1596 then (if x<72 then 0 else (if x<250 then 1 else 0)) else (if x<1628 then 2 else (if x<1642 then 1 else 0))) else (if x<1740 then (if x<1708 then 2 else (if x<1720 then 3 else 0)) else (if x<2618 then (if x<1752 then 4 else 2) else (if x<2638 then 0 else 1)))) else (if x<3162 then (if x<2730 then (if x<2680 then 3 else (if x<2716 then 1 else 2)) else (if x<2792 then (if x<2762 then 3 else 2) else (if x<3118 then 0 else 3))) else (if x<3228 then (if x<3180 then 1 else (if x<3192 then 1 else 0)) else (if x<3274 then (if x<3242 then 4 else 0) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3087 : Finset ℕ := ([40,1596,1708,1752,2638,2680,2716,2730,2792,3118,3162,3180,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3087 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3087 4 (fun x => (if x<2716 then (if x<1752 then (if x<1596 then 0 else (if x<1708 then 0 else 1)) else (if x<2638 then 1 else (if x<2680 then 2 else 0))) else (if x<3118 then (if x<2730 then 1 else (if x<2792 then 2 else 1)) else (if x<3180 then (if x<3162 then 2 else 3) else (if x<3274 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3088 : Finset ℕ := ([1708,1752,2680,2730,3180,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3088 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3088 3 (fun x => (if x<2730 then (if x<1752 then 0 else (if x<2680 then 0 else 1)) else (if x<3180 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3089 : Finset ℕ := ([40,1596,1708,1752,2618,2638,2680,2716,2730,2792,3118,3162,3180,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3089 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3089 2618 3
  · have he : independentCachedBranchMembers3089.erase 2618=independentCachedBranchMembers3087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3087
  · have he : independentCachedBranchMembers3089.filter (independentCachedEdge 2618)=independentCachedBranchMembers3088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3088
def independentCachedBranchMembers3090 : Finset ℕ := ([1596,1708,2638,2716,3118,3180] : List ℕ).toFinset
theorem independentCachedBranchBound3090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3090 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3090 3 (fun x => (if x<2716 then (if x<1708 then 0 else (if x<2638 then 1 else 2)) else (if x<3118 then 0 else (if x<3180 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3091 : Finset ℕ := ([40,250,1596,1708,1752,2618,2638,2680,2716,2730,2792,3118,3162,3180,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3091 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3091 250 3
  · have he : independentCachedBranchMembers3091.erase 250=independentCachedBranchMembers3089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3089
  · have he : independentCachedBranchMembers3091.filter (independentCachedEdge 250)=independentCachedBranchMembers3090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3090
def independentCachedBranchMembers3092 : Finset ℕ := ([40,72,250,1596,1628,1642,1678,1708,1720,1740,1752,2618,2638,2668,2680,2716,2730,2762,2792,3118,3150,3162,3180,3192,3228,3242,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3092 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3092 3150 4
  · have he : independentCachedBranchMembers3092.erase 3150=independentCachedBranchMembers3086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3086
  · have he : independentCachedBranchMembers3092.filter (independentCachedEdge 3150)=independentCachedBranchMembers3091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3091
def independentCachedBranchMembers3093 : Finset ℕ := ([40,1596,1678,1720,1740,2618,2638,2680,2762,3118,3162,3180,3228,3242,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3093 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3093 4 (fun x => (if x<2680 then (if x<1720 then (if x<1596 then 0 else (if x<1678 then 0 else 1)) else (if x<2618 then (if x<1740 then 1 else 2) else (if x<2638 then 0 else 1))) else (if x<3180 then (if x<3118 then (if x<2762 then 1 else 2) else (if x<3162 then 0 else 3)) else (if x<3242 then (if x<3228 then 3 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3094 : Finset ℕ := ([40,72,250,1596,1628,1642,1678,1708,1720,1740,1752,2618,2638,2650,2668,2680,2716,2730,2762,2792,3118,3150,3162,3180,3192,3228,3242,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3094 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3094 2650 4
  · have he : independentCachedBranchMembers3094.erase 2650=independentCachedBranchMembers3092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3092
  · have he : independentCachedBranchMembers3094.filter (independentCachedEdge 2650)=independentCachedBranchMembers3093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3093
def independentCachedBranchMembers3095 : Finset ℕ := ([72,250,1628,1720,1740,2618,2638,2668,2730,3118,3162,3192,3228,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3095 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3095 4 (fun x => (if x<2668 then (if x<1720 then (if x<250 then 0 else (if x<1628 then 0 else 1)) else (if x<2618 then (if x<1740 then 1 else 2) else (if x<2638 then 2 else 1))) else (if x<3192 then (if x<3118 then (if x<2730 then 2 else 1) else (if x<3162 then 3 else 0)) else (if x<3274 then (if x<3228 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3096 : Finset ℕ := ([40,72,250,1596,1628,1642,1678,1708,1720,1740,1752,2606,2618,2638,2650,2668,2680,2716,2730,2762,2792,3118,3150,3162,3180,3192,3228,3242,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3096 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3096 2606 4
  · have he : independentCachedBranchMembers3096.erase 2606=independentCachedBranchMembers3094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3094
  · have he : independentCachedBranchMembers3096.filter (independentCachedEdge 2606)=independentCachedBranchMembers3095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3095
def independentCachedBranchMembers3097 : Finset ℕ := ([12,40,72,222,250,252,1594,1596,1626,1628,1642,1644,1678,1692,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3097 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3097 1692 5
  · have he : independentCachedBranchMembers3097.erase 1692=independentCachedBranchMembers3085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3085
  · have he : independentCachedBranchMembers3097.filter (independentCachedEdge 1692)=independentCachedBranchMembers3096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3096
def independentCachedBranchMembers3098 : Finset ℕ := ([40,250,252,1626,1628,1642,1644,1678,1720,1738,1740,2618,2638,2680,2716,2730,2732,2776,2792,3132,3150,3192,3226,3242,3244,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3098 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3098 5 (fun x => (if x<2680 then (if x<1644 then (if x<1626 then (if x<250 then 0 else (if x<252 then 0 else 1)) else (if x<1628 then 2 else (if x<1642 then 1 else 0))) else (if x<1738 then (if x<1678 then 2 else (if x<1720 then 2 else 0)) else (if x<2618 then (if x<1740 then 3 else 4) else (if x<2638 then 0 else 2)))) else (if x<3150 then (if x<2732 then (if x<2716 then 1 else (if x<2730 then 1 else 3)) else (if x<2792 then (if x<2776 then 2 else 3) else (if x<3132 then 0 else 1))) else (if x<3242 then (if x<3192 then 4 else (if x<3226 then 0 else 3)) else (if x<3288 then (if x<3244 then 0 else 4) else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3099 : Finset ℕ := ([250,1626,1644,1738,2638,2680,2716,2730,2792,3132,3226,3244,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3099 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3099 4 (fun x => (if x<2716 then (if x<1738 then (if x<1626 then 0 else (if x<1644 then 0 else 1)) else (if x<2638 then 1 else (if x<2680 then 1 else 0))) else (if x<3132 then (if x<2730 then 2 else (if x<2792 then 2 else 1)) else (if x<3244 then (if x<3226 then 3 else 2) else (if x<3288 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3100 : Finset ℕ := ([1644,1738,2680,2730,3244,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3100 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3100 3 (fun x => (if x<2730 then (if x<1738 then 0 else (if x<2680 then 0 else 1)) else (if x<3244 then 1 else (if x<3288 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3101 : Finset ℕ := ([250,1626,1644,1738,2618,2638,2680,2716,2730,2792,3132,3226,3244,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3101 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3101 2618 3
  · have he : independentCachedBranchMembers3101.erase 2618=independentCachedBranchMembers3099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3099
  · have he : independentCachedBranchMembers3101.filter (independentCachedEdge 2618)=independentCachedBranchMembers3100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3100
def independentCachedBranchMembers3102 : Finset ℕ := ([1626,1738,2638,2716,3226,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3102 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3102 3 (fun x => (if x<2716 then (if x<1738 then 0 else (if x<2638 then 1 else 0)) else (if x<3226 then 2 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3103 : Finset ℕ := ([40,250,1626,1644,1738,2618,2638,2680,2716,2730,2792,3132,3226,3244,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3103 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3103 40 3
  · have he : independentCachedBranchMembers3103.erase 40=independentCachedBranchMembers3101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3101
  · have he : independentCachedBranchMembers3103.filter (independentCachedEdge 40)=independentCachedBranchMembers3102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3102
def independentCachedBranchMembers3104 : Finset ℕ := ([40,250,252,1626,1628,1642,1644,1678,1720,1738,1740,2618,2638,2680,2716,2730,2732,2776,2792,3132,3150,3192,3226,3228,3242,3244,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3104 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3104 3228 4
  · have he : independentCachedBranchMembers3104.erase 3228=independentCachedBranchMembers3098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3098
  · have he : independentCachedBranchMembers3104.filter (independentCachedEdge 3228)=independentCachedBranchMembers3103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3103
def independentCachedBranchMembers3105 : Finset ℕ := ([40,252,1628,1642,1740,2618,2716,2730,2776,3132,3150,3192,3226,3244,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3105 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3105 4 (fun x => (if x<2730 then (if x<1642 then (if x<252 then 0 else (if x<1628 then 0 else 1)) else (if x<2618 then (if x<1740 then 1 else 2) else (if x<2716 then 2 else 1))) else (if x<3192 then (if x<3132 then (if x<2776 then 1 else 2) else (if x<3150 then 0 else 3)) else (if x<3244 then (if x<3226 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3106 : Finset ℕ := ([40,250,252,1626,1628,1642,1644,1678,1720,1738,1740,2618,2638,2680,2714,2716,2730,2732,2776,2792,3132,3150,3192,3226,3228,3242,3244,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3106 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3106 2714 4
  · have he : independentCachedBranchMembers3106.erase 2714=independentCachedBranchMembers3104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3104
  · have he : independentCachedBranchMembers3106.filter (independentCachedEdge 2714)=independentCachedBranchMembers3105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3105
def independentCachedBranchMembers3107 : Finset ℕ := ([250,1626,1642,1678,1740,2618,2680,2716,2732,3132,3150,3226,3242,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3107 4 (fun x => (if x<2716 then (if x<1678 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<2618 then (if x<1740 then 1 else 2) else (if x<2680 then 0 else 1))) else (if x<3226 then (if x<3132 then (if x<2732 then 1 else 2) else (if x<3150 then 3 else 3)) else (if x<3288 then (if x<3242 then 0 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3108 : Finset ℕ := ([40,250,252,1626,1628,1642,1644,1678,1720,1738,1740,2618,2620,2638,2680,2714,2716,2730,2732,2776,2792,3132,3150,3192,3226,3228,3242,3244,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3108 2620 4
  · have he : independentCachedBranchMembers3108.erase 2620=independentCachedBranchMembers3106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3106
  · have he : independentCachedBranchMembers3108.filter (independentCachedEdge 2620)=independentCachedBranchMembers3107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3107
def independentCachedBranchMembers3109 : Finset ℕ := ([12,40,72,222,250,252,1594,1596,1614,1626,1628,1642,1644,1678,1692,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3109 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3109 1614 5
  · have he : independentCachedBranchMembers3109.erase 1614=independentCachedBranchMembers3097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3097
  · have he : independentCachedBranchMembers3109.filter (independentCachedEdge 1614)=independentCachedBranchMembers3108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3108
def independentCachedBranchMembers3110 : Finset ℕ := ([40,72,250,252,1596,1626,1628,1642,1644,1678,1720,1752,1768,2618,2620,2650,2668,2776,2792,3102,3118,3192,3226,3244,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3110 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3110 5 (fun x => (if x<2618 then (if x<1628 then (if x<252 then (if x<72 then 0 else (if x<250 then 1 else 0)) else (if x<1596 then 1 else (if x<1626 then 2 else 2))) else (if x<1678 then (if x<1642 then 1 else (if x<1644 then 0 else 3)) else (if x<1752 then (if x<1720 then 2 else 0) else (if x<1768 then 3 else 1)))) else (if x<3102 then (if x<2668 then (if x<2620 then 0 else (if x<2650 then 4 else 4)) else (if x<2776 then 1 else (if x<2792 then 1 else 0))) else (if x<3226 then (if x<3118 then 2 else (if x<3192 then 3 else 0)) else (if x<3274 then (if x<3244 then 3 else 2) else (if x<3276 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3111 : Finset ℕ := ([72,252,1596,1626,1642,1720,2618,2668,2776,2792,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3111 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3111 4 (fun x => (if x<2618 then (if x<1626 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1642 then 1 else (if x<1720 then 2 else 2))) else (if x<2792 then (if x<2668 then 1 else (if x<2776 then 0 else 0)) else (if x<3244 then 2 else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3112 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1720,1752,1768,2618,2620,2650,2668,2776,2792,3102,3118,3192,3226,3244,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3112 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3112 1594 4
  · have he : independentCachedBranchMembers3112.erase 1594=independentCachedBranchMembers3110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3110
  · have he : independentCachedBranchMembers3112.filter (independentCachedEdge 1594)=independentCachedBranchMembers3111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3111
def independentCachedBranchMembers3113 : Finset ℕ := ([72,252,1596,1626,1644,1752,2620,2650,2668,2776,3118,3226,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3113 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3113 4 (fun x => (if x<2650 then (if x<1626 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1752 then (if x<1644 then 1 else 0) else (if x<2620 then 0 else 2))) else (if x<3118 then (if x<2668 then 2 else (if x<2776 then 3 else 3)) else (if x<3244 then (if x<3226 then 3 else 3) else (if x<3274 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3114 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1720,1752,1768,2618,2620,2650,2668,2776,2792,3102,3118,3192,3226,3242,3244,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3114 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3114 3242 4
  · have he : independentCachedBranchMembers3114.erase 3242=independentCachedBranchMembers3112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3112
  · have he : independentCachedBranchMembers3114.filter (independentCachedEdge 3242)=independentCachedBranchMembers3113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3113
def independentCachedBranchMembers3115 : Finset ℕ := ([40,72,250,1594,1626,1644,1768,2618,2650,2668,2792,3102,3226,3244,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3115 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3115 4 (fun x => (if x<2618 then (if x<1594 then (if x<72 then 0 else (if x<250 then 1 else 0)) else (if x<1644 then (if x<1626 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3102 then (if x<2668 then (if x<2650 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3244 then (if x<3226 then 3 else 2) else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3116 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1720,1752,1768,2618,2620,2650,2668,2776,2792,3102,3118,3192,3226,3228,3242,3244,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3116 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3116 3228 4
  · have he : independentCachedBranchMembers3116.erase 3228=independentCachedBranchMembers3114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3114
  · have he : independentCachedBranchMembers3116.filter (independentCachedEdge 3228)=independentCachedBranchMembers3115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3115
def independentCachedBranchMembers3117 : Finset ℕ := ([40,250,252,1594,1596,1752,1768,2618,2620,2776,2792,3102,3118,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3117 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3117 4 (fun x => (if x<2618 then (if x<1594 then (if x<250 then 0 else (if x<252 then 0 else 1)) else (if x<1752 then (if x<1596 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3102 then (if x<2776 then (if x<2620 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3274 then (if x<3118 then 3 else 2) else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3118 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1720,1752,1768,2618,2620,2650,2668,2776,2792,3102,3118,3150,3192,3226,3228,3242,3244,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3118 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3118 3150 4
  · have he : independentCachedBranchMembers3118.erase 3150=independentCachedBranchMembers3116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3116
  · have he : independentCachedBranchMembers3118.filter (independentCachedEdge 3150)=independentCachedBranchMembers3117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3117
def independentCachedBranchMembers3119 : Finset ℕ := ([40,250,1594,1628,1642,1678,1720,1768,2620,2650,2668,2776,3118,3226,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3119 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3119 4 (fun x => (if x<2620 then (if x<1642 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 0 else 1)) else (if x<1720 then (if x<1678 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3118 then (if x<2668 then (if x<2650 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3244 then (if x<3226 then 3 else 3) else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3120 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1720,1752,1768,2618,2620,2650,2652,2668,2776,2792,3102,3118,3150,3192,3226,3228,3242,3244,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3120 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3120 2652 4
  · have he : independentCachedBranchMembers3120.erase 2652=independentCachedBranchMembers3118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3118
  · have he : independentCachedBranchMembers3120.filter (independentCachedEdge 2652)=independentCachedBranchMembers3119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3119
def independentCachedBranchMembers3121 : Finset ℕ := ([12,40,72,222,250,252,1594,1596,1614,1626,1628,1642,1644,1678,1692,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3121 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3121 3214 5
  · have he : independentCachedBranchMembers3121.erase 3214=independentCachedBranchMembers3109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3109
  · have he : independentCachedBranchMembers3121.filter (independentCachedEdge 3214)=independentCachedBranchMembers3120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3120
def independentCachedBranchMembers3122 : Finset ℕ := ([72,252,1594,1626,1644,1678,1692,1720,1738,1752,2606,2620,2638,2652,2680,2714,2764,2792,3132,3150,3164,3178,3192,3226,3244,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3122 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3122 5 (fun x => (if x<2652 then (if x<1692 then (if x<1626 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 2 else (if x<1678 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1738 then 3 else 3)) else (if x<2620 then (if x<2606 then 0 else 1) else (if x<2638 then 3 else 3)))) else (if x<3150 then (if x<2764 then (if x<2680 then 0 else (if x<2714 then 1 else 1)) else (if x<2792 then 1 else (if x<3132 then 0 else 4))) else (if x<3192 then (if x<3164 then 4 else (if x<3178 then 2 else 2)) else (if x<3244 then (if x<3226 then 0 else 2) else (if x<3276 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3123 : Finset ℕ := ([72,1594,1626,1720,1738,1752,2680,2714,2792,3178,3192,3226] : List ℕ).toFinset
theorem independentCachedBranchBound3123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3123 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3123 4 (fun x => (if x<2680 then (if x<1720 then (if x<1594 then 0 else (if x<1626 then 1 else 0)) else (if x<1738 then 2 else (if x<1752 then 1 else 3))) else (if x<3178 then (if x<2714 then 0 else (if x<2792 then 1 else 2)) else (if x<3192 then 0 else (if x<3226 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3124 : Finset ℕ := ([12,72,252,1594,1626,1644,1678,1692,1720,1738,1752,2606,2620,2638,2652,2680,2714,2764,2792,3132,3150,3164,3178,3192,3226,3244,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3124 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3124 12 4
  · have he : independentCachedBranchMembers3124.erase 12=independentCachedBranchMembers3122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3122
  · have he : independentCachedBranchMembers3124.filter (independentCachedEdge 12)=independentCachedBranchMembers3123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3123
def independentCachedBranchMembers3125 : Finset ℕ := ([72,1594,1738,1752,2606,2620,2764,2792,3150,3164,3178,3192,3226,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3125 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3125 4 (fun x => (if x<2792 then (if x<1752 then (if x<1594 then 0 else (if x<1738 then 1 else 0)) else (if x<2620 then (if x<2606 then 1 else 1) else (if x<2764 then 2 else 0))) else (if x<3178 then (if x<3150 then 2 else (if x<3164 then 0 else 3)) else (if x<3226 then (if x<3192 then 3 else 2) else (if x<3244 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3126 : Finset ℕ := ([12,72,252,1594,1626,1644,1678,1692,1720,1738,1752,2606,2620,2638,2652,2680,2714,2732,2764,2792,3132,3150,3164,3178,3192,3226,3244,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3126 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3126 2732 4
  · have he : independentCachedBranchMembers3126.erase 2732=independentCachedBranchMembers3124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3124
  · have he : independentCachedBranchMembers3126.filter (independentCachedEdge 2732)=independentCachedBranchMembers3125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3125
def independentCachedBranchMembers3127 : Finset ℕ := ([12,1594,1626,1678,1692,2606,2620,2638,2652,2714,2792,3178,3192,3244,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3127 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3127 4 (fun x => (if x<2638 then (if x<1678 then (if x<1594 then 0 else (if x<1626 then 1 else 2)) else (if x<2606 then (if x<1692 then 0 else 1) else (if x<2620 then 0 else 1))) else (if x<3178 then (if x<2714 then (if x<2652 then 2 else 3) else (if x<2792 then 1 else 3)) else (if x<3244 then (if x<3192 then 2 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3128 : Finset ℕ := ([12,72,252,1594,1626,1644,1678,1692,1720,1738,1752,2606,2620,2638,2652,2680,2714,2732,2764,2792,3132,3150,3164,3178,3192,3226,3244,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3128 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3128 3304 4
  · have he : independentCachedBranchMembers3128.erase 3304=independentCachedBranchMembers3126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3126
  · have he : independentCachedBranchMembers3128.filter (independentCachedEdge 3304)=independentCachedBranchMembers3127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3127
def independentCachedBranchMembers3129 : Finset ℕ := ([12,72,1626,1678,1692,1738,1752,2638,2652,2714,2764,3150,3164,3226,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3129 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3129 4 (fun x => (if x<2638 then (if x<1678 then (if x<72 then 0 else (if x<1626 then 1 else 1)) else (if x<1738 then (if x<1692 then 0 else 2) else (if x<1752 then 2 else 3))) else (if x<3150 then (if x<2714 then (if x<2652 then 0 else 1) else (if x<2764 then 2 else 2)) else (if x<3226 then (if x<3164 then 1 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3130 : Finset ℕ := ([12,40,72,252,1594,1626,1644,1678,1692,1720,1738,1752,2606,2620,2638,2652,2680,2714,2732,2764,2792,3132,3150,3164,3178,3192,3226,3244,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3130 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3130 40 4
  · have he : independentCachedBranchMembers3130.erase 40=independentCachedBranchMembers3128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3128
  · have he : independentCachedBranchMembers3130.filter (independentCachedEdge 40)=independentCachedBranchMembers3129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3129
def independentCachedBranchMembers3131 : Finset ℕ := ([252,1626,1692,1720,1738,2606,2652,2680,2714,2764,2792,3132,3150,3178,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3131 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3131 4 (fun x => (if x<2680 then (if x<1720 then (if x<1626 then 0 else (if x<1692 then 1 else 0)) else (if x<2606 then (if x<1738 then 1 else 2) else (if x<2652 then 3 else 0))) else (if x<3132 then (if x<2764 then (if x<2714 then 1 else 1) else (if x<2792 then 2 else 3)) else (if x<3178 then (if x<3150 then 0 else 2) else (if x<3244 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3132 : Finset ℕ := ([1692,1720,2606,2714,3132,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3132 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3132 3 (fun x => (if x<2714 then (if x<1720 then 0 else (if x<2606 then 1 else 2)) else (if x<3132 then 0 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3133 : Finset ℕ := ([72,252,1626,1692,1720,1738,2606,2652,2680,2714,2764,2792,3132,3150,3178,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3133 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3133 72 3
  · have he : independentCachedBranchMembers3133.erase 72=independentCachedBranchMembers3131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3131
  · have he : independentCachedBranchMembers3133.filter (independentCachedEdge 72)=independentCachedBranchMembers3132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3132
def independentCachedBranchMembers3134 : Finset ℕ := ([12,40,72,252,1594,1626,1644,1678,1692,1720,1738,1752,2606,2620,2638,2652,2680,2714,2732,2764,2792,3118,3132,3150,3164,3178,3192,3226,3244,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3134 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3134 3118 4
  · have he : independentCachedBranchMembers3134.erase 3118=independentCachedBranchMembers3130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3130
  · have he : independentCachedBranchMembers3134.filter (independentCachedEdge 3118)=independentCachedBranchMembers3133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3133
def independentCachedBranchMembers3135 : Finset ℕ := ([12,40,72,222,250,252,1594,1596,1614,1626,1628,1642,1644,1678,1690,1692,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3135 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3135 1690 5
  · have he : independentCachedBranchMembers3135.erase 1690=independentCachedBranchMembers3121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3121
  · have he : independentCachedBranchMembers3135.filter (independentCachedEdge 1690)=independentCachedBranchMembers3134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3134
def independentCachedBranchMembers3136 : Finset ℕ := ([72,222,252,1594,1596,1614,1642,1644,1678,1708,1752,2606,2650,2652,2680,2714,2716,2764,2792,3118,3162,3164,3192,3228,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3136 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3136 5 (fun x => (if x<2652 then (if x<1642 then (if x<1594 then (if x<222 then 0 else (if x<252 then 0 else 1)) else (if x<1596 then 2 else (if x<1614 then 1 else 0))) else (if x<1708 then (if x<1644 then 3 else (if x<1678 then 2 else 2)) else (if x<2606 then (if x<1752 then 3 else 0) else (if x<2650 then 2 else 0)))) else (if x<3162 then (if x<2716 then (if x<2680 then 1 else (if x<2714 then 2 else 2)) else (if x<2792 then (if x<2764 then 3 else 0) else (if x<3118 then 3 else 4))) else (if x<3228 then (if x<3164 then 4 else (if x<3192 then 0 else 1)) else (if x<3274 then (if x<3256 then 1 else 4) else (if x<3276 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3137 : Finset ℕ := ([252,1594,1644,1708,2650,2714,2764,2792,3118,3164,3192,3228,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3137 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3137 4 (fun x => (if x<2792 then (if x<1708 then (if x<1594 then 0 else (if x<1644 then 1 else 0)) else (if x<2714 then (if x<2650 then 1 else 1) else (if x<2764 then 2 else 0))) else (if x<3192 then (if x<3118 then 2 else (if x<3164 then 3 else 0)) else (if x<3256 then (if x<3228 then 3 else 3) else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3138 : Finset ℕ := ([72,222,252,1594,1596,1614,1642,1644,1678,1708,1752,2606,2650,2652,2680,2714,2716,2762,2764,2792,3118,3162,3164,3192,3228,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3138 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3138 2762 4
  · have he : independentCachedBranchMembers3138.erase 2762=independentCachedBranchMembers3136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3136
  · have he : independentCachedBranchMembers3138.filter (independentCachedEdge 2762)=independentCachedBranchMembers3137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3137
def independentCachedBranchMembers3139 : Finset ℕ := ([222,1594,1596,1614,1678,2606,2650,2652,2714,2716,2792,3192,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3139 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3139 4 (fun x => (if x<2652 then (if x<1614 then (if x<1594 then 0 else (if x<1596 then 1 else 2)) else (if x<2606 then (if x<1678 then 0 else 1) else (if x<2650 then 1 else 0))) else (if x<3192 then (if x<2716 then (if x<2714 then 2 else 1) else (if x<2792 then 3 else 3)) else (if x<3274 then (if x<3256 then 2 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3140 : Finset ℕ := ([72,222,252,1594,1596,1614,1642,1644,1678,1708,1752,2606,2650,2652,2680,2714,2716,2762,2764,2792,3118,3162,3164,3192,3228,3256,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3140 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3140 3304 4
  · have he : independentCachedBranchMembers3140.erase 3304=independentCachedBranchMembers3138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3138
  · have he : independentCachedBranchMembers3140.filter (independentCachedEdge 3304)=independentCachedBranchMembers3139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3139
def independentCachedBranchMembers3141 : Finset ℕ := ([222,252,1596,1614,1644,1678,1708,2606,2652,2716,2764,3118,3164,3228,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3141 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3141 4 (fun x => (if x<2606 then (if x<1614 then (if x<252 then 0 else (if x<1596 then 1 else 1)) else (if x<1678 then (if x<1644 then 0 else 2) else (if x<1708 then 2 else 3))) else (if x<3118 then (if x<2716 then (if x<2652 then 2 else 0) else (if x<2764 then 1 else 2)) else (if x<3228 then (if x<3164 then 3 else 1) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3142 : Finset ℕ := ([72,222,250,252,1594,1596,1614,1642,1644,1678,1708,1752,2606,2650,2652,2680,2714,2716,2762,2764,2792,3118,3162,3164,3192,3228,3256,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3142 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3142 250 4
  · have he : independentCachedBranchMembers3142.erase 250=independentCachedBranchMembers3140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3140
  · have he : independentCachedBranchMembers3142.filter (independentCachedEdge 250)=independentCachedBranchMembers3141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3141
def independentCachedBranchMembers3143 : Finset ℕ := ([252,1596,1614,1642,1708,2606,2652,2680,2714,2764,2792,3162,3228,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3143 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3143 4 (fun x => (if x<2680 then (if x<1642 then (if x<1596 then 0 else (if x<1614 then 0 else 1)) else (if x<2606 then (if x<1708 then 2 else 1) else (if x<2652 then 1 else 0))) else (if x<3162 then (if x<2764 then (if x<2714 then 2 else 3) else (if x<2792 then 1 else 3)) else (if x<3256 then (if x<3228 then 2 else 0) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3144 : Finset ℕ := ([1596,1708,2606,2714,3228,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3144 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3144 3 (fun x => (if x<2714 then (if x<1708 then 0 else (if x<2606 then 1 else 0)) else (if x<3228 then 2 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3145 : Finset ℕ := ([72,252,1596,1614,1642,1708,2606,2652,2680,2714,2764,2792,3162,3228,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3145 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3145 72 3
  · have he : independentCachedBranchMembers3145.erase 72=independentCachedBranchMembers3143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3143
  · have he : independentCachedBranchMembers3145.filter (independentCachedEdge 72)=independentCachedBranchMembers3144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3144
def independentCachedBranchMembers3146 : Finset ℕ := ([72,222,250,252,1594,1596,1614,1642,1644,1678,1708,1752,2606,2650,2652,2680,2714,2716,2762,2764,2792,3118,3162,3164,3192,3226,3228,3256,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3146 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3146 3226 4
  · have he : independentCachedBranchMembers3146.erase 3226=independentCachedBranchMembers3142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3142
  · have he : independentCachedBranchMembers3146.filter (independentCachedEdge 3226)=independentCachedBranchMembers3145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3145
def independentCachedBranchMembers3147 : Finset ℕ := ([12,40,72,222,250,252,1582,1594,1596,1614,1626,1628,1642,1644,1678,1690,1692,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3147 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3147 1582 5
  · have he : independentCachedBranchMembers3147.erase 1582=independentCachedBranchMembers3135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3135
  · have he : independentCachedBranchMembers3147.filter (independentCachedEdge 1582)=independentCachedBranchMembers3146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3146
def independentCachedBranchMembers3148 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1720,1752,1768,2606,2638,2680,2714,2716,2730,2732,2762,2764,3132,3162,3178,3180,3214,3256,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3148 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3148 5 (fun x => (if x<2680 then (if x<1644 then (if x<252 then (if x<72 then 0 else (if x<250 then 1 else 0)) else (if x<1628 then (if x<1594 then 1 else 0) else (if x<1642 then 1 else 2))) else (if x<1752 then (if x<1678 then 3 else (if x<1720 then 2 else 2)) else (if x<2606 then (if x<1768 then 3 else 0) else (if x<2638 then 3 else 2)))) else (if x<3132 then (if x<2730 then (if x<2714 then 0 else (if x<2716 then 3 else 2)) else (if x<2762 then (if x<2732 then 0 else 4) else (if x<2764 then 4 else 1))) else (if x<3214 then (if x<3178 then (if x<3162 then 4 else 4) else (if x<3180 then 0 else 1)) else (if x<3288 then (if x<3256 then 4 else 0) else (if x<3304 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3149 : Finset ℕ := ([40,250,1594,1628,1642,1678,1720,1768,2606,2714,2732,2762,3132,3162,3180,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3149 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3149 4 (fun x => (if x<2606 then (if x<1642 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 0 else 1)) else (if x<1720 then (if x<1678 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3132 then (if x<2732 then (if x<2714 then 2 else 2) else (if x<2762 then 3 else 3)) else (if x<3180 then (if x<3162 then 3 else 3) else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3150 : Finset ℕ := ([40,72,250,252,1594,1628,1642,1644,1678,1720,1752,1768,2606,2638,2680,2714,2716,2730,2732,2762,2764,3132,3162,3164,3178,3180,3214,3256,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3150 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3150 3164 4
  · have he : independentCachedBranchMembers3150.erase 3164=independentCachedBranchMembers3148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3148
  · have he : independentCachedBranchMembers3150.filter (independentCachedEdge 3164)=independentCachedBranchMembers3149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3149
def independentCachedBranchMembers3151 : Finset ℕ := ([40,252,1594,1628,1642,1752,2606,2716,2730,2764,3132,3162,3180,3214,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3151 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3151 4 (fun x => (if x<2730 then (if x<1642 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1628 then 1 else 1)) else (if x<2606 then (if x<1752 then 2 else 2) else (if x<2716 then 2 else 2))) else (if x<3180 then (if x<3132 then (if x<2764 then 1 else 1) else (if x<3162 then 0 else 3)) else (if x<3256 then (if x<3214 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3152 : Finset ℕ := ([40,72,250,252,1594,1626,1628,1642,1644,1678,1720,1752,1768,2606,2638,2680,2714,2716,2730,2732,2762,2764,3132,3162,3164,3178,3180,3214,3256,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3152 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3152 1626 4
  · have he : independentCachedBranchMembers3152.erase 1626=independentCachedBranchMembers3150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3150
  · have he : independentCachedBranchMembers3152.filter (independentCachedEdge 1626)=independentCachedBranchMembers3151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3151
def independentCachedBranchMembers3153 : Finset ℕ := ([72,250,1594,1628,1644,1720,2638,2714,2730,2764,3132,3162,3178,3214,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3153 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3153 4 (fun x => (if x<2730 then (if x<1644 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 1 else 1)) else (if x<2638 then (if x<1720 then 2 else 2) else (if x<2714 then 2 else 2))) else (if x<3178 then (if x<3132 then (if x<2764 then 1 else 1) else (if x<3162 then 3 else 0)) else (if x<3288 then (if x<3214 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3154 : Finset ℕ := ([40,72,250,252,1594,1596,1626,1628,1642,1644,1678,1720,1752,1768,2606,2638,2680,2714,2716,2730,2732,2762,2764,3132,3162,3164,3178,3180,3214,3256,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3154 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3154 1596 4
  · have he : independentCachedBranchMembers3154.erase 1596=independentCachedBranchMembers3152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3152
  · have he : independentCachedBranchMembers3154.filter (independentCachedEdge 1596)=independentCachedBranchMembers3153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3153
def independentCachedBranchMembers3155 : Finset ℕ := ([12,40,72,222,250,252,1582,1594,1596,1614,1626,1628,1642,1644,1678,1690,1692,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2702,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3132,3150,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3155 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3155 2702 5
  · have he : independentCachedBranchMembers3155.erase 2702=independentCachedBranchMembers3147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3147
  · have he : independentCachedBranchMembers3155.filter (independentCachedEdge 2702)=independentCachedBranchMembers3154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3154
def independentCachedBranchMembers3156 : Finset ℕ := ([12,72,222,252,1594,1614,1628,1644,1692,1708,1738,1752,2618,2638,2652,2668,2702,2716,2776,2792,3102,3118,3132,3162,3178,3192,3226,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3156 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3156 5 (fun x => (if x<2652 then (if x<1644 then (if x<252 then (if x<72 then 0 else (if x<222 then 1 else 0)) else (if x<1614 then (if x<1594 then 1 else 2) else (if x<1628 then 0 else 1))) else (if x<1738 then (if x<1692 then 2 else (if x<1708 then 0 else 3)) else (if x<2618 then (if x<1752 then 2 else 3) else (if x<2638 then 4 else 4)))) else (if x<3118 then (if x<2716 then (if x<2668 then 0 else (if x<2702 then 1 else 0)) else (if x<2792 then (if x<2776 then 3 else 1) else (if x<3102 then 3 else 0))) else (if x<3192 then (if x<3162 then (if x<3132 then 4 else 2) else (if x<3178 then 4 else 2)) else (if x<3256 then (if x<3226 then 1 else 2) else (if x<3276 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3157 : Finset ℕ := ([12,72,222,252,1614,1644,1692,1752,2638,2668,2716,2776,3118,3178,3226,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3157 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3157 4 (fun x => (if x<2638 then (if x<1614 then (if x<222 then (if x<72 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1692 then (if x<1644 then 0 else 1) else (if x<1752 then 0 else 1))) else (if x<3118 then (if x<2716 then (if x<2668 then 2 else 3) else (if x<2776 then 2 else 3)) else (if x<3226 then (if x<3178 then 3 else 2) else (if x<3256 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3158 : Finset ℕ := ([12,72,222,252,1594,1614,1628,1644,1692,1708,1738,1752,2618,2638,2652,2668,2702,2716,2776,2792,3102,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3158 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3158 3242 4
  · have he : independentCachedBranchMembers3158.erase 3242=independentCachedBranchMembers3156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3156
  · have he : independentCachedBranchMembers3158.filter (independentCachedEdge 3242)=independentCachedBranchMembers3157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3157
def independentCachedBranchMembers3159 : Finset ℕ := ([12,252,1594,1628,1644,1692,1708,1738,2638,2702,2776,2792,3102,3118,3192,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3159 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3159 4 (fun x => (if x<2638 then (if x<1644 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1628 then 1 else 0)) else (if x<1708 then (if x<1692 then 1 else 1) else (if x<1738 then 0 else 1))) else (if x<3102 then (if x<2776 then (if x<2702 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3192 then (if x<3118 then 3 else 2) else (if x<3256 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3160 : Finset ℕ := ([12,72,222,252,1594,1614,1628,1644,1692,1708,1738,1752,2618,2638,2652,2668,2702,2716,2762,2776,2792,3102,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3160 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3160 2762 4
  · have he : independentCachedBranchMembers3160.erase 2762=independentCachedBranchMembers3158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3158
  · have he : independentCachedBranchMembers3160.filter (independentCachedEdge 2762)=independentCachedBranchMembers3159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3159
def independentCachedBranchMembers3161 : Finset ℕ := ([72,222,1594,1614,1628,1708,1738,1752,2668,2702,2716,2792,3102,3178,3192,3226] : List ℕ).toFinset
theorem independentCachedBranchBound3161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3161 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3161 4 (fun x => (if x<2668 then (if x<1628 then (if x<1594 then (if x<222 then 0 else 0) else (if x<1614 then 1 else 0)) else (if x<1738 then (if x<1708 then 1 else 1) else (if x<1752 then 1 else 0))) else (if x<3102 then (if x<2716 then (if x<2702 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3192 then (if x<3178 then 3 else 3) else (if x<3226 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3162 : Finset ℕ := ([12,72,222,252,1594,1614,1628,1644,1692,1708,1738,1752,2618,2638,2652,2668,2702,2716,2732,2762,2776,2792,3102,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3162 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3162 2732 4
  · have he : independentCachedBranchMembers3162.erase 2732=independentCachedBranchMembers3160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3160
  · have he : independentCachedBranchMembers3162.filter (independentCachedEdge 2732)=independentCachedBranchMembers3161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3161
def independentCachedBranchMembers3163 : Finset ℕ := ([222,1644,1708,1738,1752,2618,2638,2652,2702,2716,2792,3118,3132,3162,3226] : List ℕ).toFinset
theorem independentCachedBranchBound3163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3163 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3163 4 (fun x => (if x<2652 then (if x<1738 then (if x<1644 then 0 else (if x<1708 then 1 else 2)) else (if x<2618 then (if x<1752 then 0 else 1) else (if x<2638 then 3 else 0))) else (if x<3118 then (if x<2716 then (if x<2702 then 1 else 2) else (if x<2792 then 3 else 1)) else (if x<3162 then (if x<3132 then 2 else 3) else (if x<3226 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3164 : Finset ℕ := ([1738,1752,2618,2792,3162,3226] : List ℕ).toFinset
theorem independentCachedBranchBound3164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3164 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3164 3 (fun x => (if x<2792 then (if x<1752 then 0 else (if x<2618 then 1 else 2)) else (if x<3162 then 0 else (if x<3226 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3165 : Finset ℕ := ([12,222,1644,1708,1738,1752,2618,2638,2652,2702,2716,2792,3118,3132,3162,3226] : List ℕ).toFinset
theorem independentCachedBranchBound3165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3165 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3165 12 3
  · have he : independentCachedBranchMembers3165.erase 12=independentCachedBranchMembers3163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3163
  · have he : independentCachedBranchMembers3165.filter (independentCachedEdge 12)=independentCachedBranchMembers3164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3164
def independentCachedBranchMembers3166 : Finset ℕ := ([12,72,222,252,1594,1614,1628,1644,1692,1708,1738,1752,1768,2618,2638,2652,2668,2702,2716,2732,2762,2776,2792,3102,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3166 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3166 1768 4
  · have he : independentCachedBranchMembers3166.erase 1768=independentCachedBranchMembers3162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3162
  · have he : independentCachedBranchMembers3166.filter (independentCachedEdge 1768)=independentCachedBranchMembers3165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3165
def independentCachedBranchMembers3167 : Finset ℕ := ([252,1614,1692,1708,1738,2618,2652,2668,2702,2776,2792,3132,3162,3178,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3167 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3167 4 (fun x => (if x<2668 then (if x<1708 then (if x<1614 then 0 else (if x<1692 then 1 else 0)) else (if x<2618 then (if x<1738 then 1 else 2) else (if x<2652 then 3 else 0))) else (if x<3132 then (if x<2776 then (if x<2702 then 1 else 1) else (if x<2792 then 2 else 3)) else (if x<3178 then (if x<3162 then 0 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3168 : Finset ℕ := ([1692,1708,2618,2702,3132,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3168 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3168 3 (fun x => (if x<2702 then (if x<1708 then 0 else (if x<2618 then 1 else 2)) else (if x<3132 then 0 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3169 : Finset ℕ := ([72,252,1614,1692,1708,1738,2618,2652,2668,2702,2776,2792,3132,3162,3178,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3169 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3169 72 3
  · have he : independentCachedBranchMembers3169.erase 72=independentCachedBranchMembers3167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3167
  · have he : independentCachedBranchMembers3169.filter (independentCachedEdge 72)=independentCachedBranchMembers3168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3168
def independentCachedBranchMembers3170 : Finset ℕ := ([12,72,222,252,1594,1614,1628,1644,1678,1692,1708,1738,1752,1768,2618,2638,2652,2668,2702,2716,2732,2762,2776,2792,3102,3118,3132,3162,3178,3192,3226,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3170 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3170 1678 4
  · have he : independentCachedBranchMembers3170.erase 1678=independentCachedBranchMembers3166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3166
  · have he : independentCachedBranchMembers3170.filter (independentCachedEdge 1678)=independentCachedBranchMembers3169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3169
def independentCachedBranchMembers3171 : Finset ℕ := ([12,40,72,222,250,252,1582,1594,1596,1614,1626,1628,1642,1644,1678,1690,1692,1708,1720,1738,1740,1752,1768,2606,2618,2620,2638,2650,2652,2668,2680,2702,2714,2716,2730,2732,2762,2764,2776,2792,3102,3118,3130,3132,3150,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3171 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3171 3130 5
  · have he : independentCachedBranchMembers3171.erase 3130=independentCachedBranchMembers3155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3155
  · have he : independentCachedBranchMembers3171.filter (independentCachedEdge 3130)=independentCachedBranchMembers3170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3170
def independentCachedBranchMembers3172 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3172 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3172 246 6
  · have he : independentCachedBranchMembers3172.erase 246=independentCachedBranchMembers3002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3002
  · have he : independentCachedBranchMembers3172.filter (independentCachedEdge 246)=independentCachedBranchMembers3171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3171
def independentCachedBranchMembers3173 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2680,2702,2730,2764,2786,2788,3102,3186,3188,3192,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3173 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3173 6 (fun x => (if x<2650 then (if x<1678 then (if x<1594 then (if x<130 then (if x<80 then 0 else 1) else (if x<132 then 0 else 1)) else (if x<1650 then (if x<1628 then 2 else 2) else (if x<1652 then 1 else 0))) else (if x<1738 then (if x<1708 then (if x<1702 then 2 else 1) else (if x<1734 then 3 else 0)) else (if x<2614 then (if x<1768 then 3 else 2) else (if x<2620 then 4 else (if x<2646 then 0 else 5))))) else (if x<3186 then (if x<2764 then (if x<2702 then (if x<2680 then 1 else 2) else (if x<2730 then 0 else 2)) else (if x<2788 then (if x<2786 then 2 else 4) else (if x<3102 then 5 else 4))) else (if x<3242 then (if x<3192 then (if x<3188 then 4 else 5) else (if x<3238 then 0 else 4)) else (if x<3270 then (if x<3244 then 3 else 1) else (if x<3274 then 5 else (if x<3276 then 0 else 3)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3174 : Finset ℕ := ([80,130,1594,1628,1652,1678,1702,1708,1738,1768,2646,2702,2786,3102,3186,3192,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3174 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3174 5 (fun x => (if x<1768 then (if x<1652 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else 0)) else (if x<1702 then (if x<1678 then 1 else 0) else (if x<1708 then 1 else (if x<1738 then 2 else 2)))) else (if x<3186 then (if x<2702 then (if x<2646 then 1 else 3) else (if x<2786 then 2 else (if x<3102 then 3 else 3))) else (if x<3242 then (if x<3192 then 3 else 0) else (if x<3270 then 0 else (if x<3276 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3175 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2680,2702,2730,2764,2786,2788,3102,3130,3186,3188,3192,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3175 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3175 3130 5
  · have he : independentCachedBranchMembers3175.erase 3130=independentCachedBranchMembers3173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3173
  · have he : independentCachedBranchMembers3175.filter (independentCachedEdge 3130)=independentCachedBranchMembers3174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3174
def independentCachedBranchMembers3176 : Finset ℕ := ([48,80,132,1594,1652,1678,1708,2614,2646,2650,2680,2702,2764,2786,3102,3186,3238,3242,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3176 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3176 5 (fun x => (if x<2680 then (if x<1678 then (if x<132 then (if x<80 then 0 else 1) else (if x<1594 then 0 else (if x<1652 then 0 else 1))) else (if x<2614 then (if x<1708 then 0 else 1) else (if x<2646 then 2 else (if x<2650 then 1 else 2)))) else (if x<3186 then (if x<2764 then (if x<2702 then 0 else 1) else (if x<2786 then 0 else (if x<3102 then 2 else 2))) else (if x<3242 then (if x<3238 then 0 else 2) else (if x<3270 then 1 else (if x<3274 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3177 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2680,2702,2730,2764,2786,2788,3102,3130,3186,3188,3192,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3177 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3177 3298 5
  · have he : independentCachedBranchMembers3177.erase 3298=independentCachedBranchMembers3175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3175
  · have he : independentCachedBranchMembers3177.filter (independentCachedEdge 3298)=independentCachedBranchMembers3176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3176
def independentCachedBranchMembers3178 : Finset ℕ := ([48,132,1594,1678,1702,1738,2620,2646,2680,2702,2764,2786,2788,3102,3186,3188,3242,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3178 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3178 5 (fun x => (if x<2702 then (if x<1702 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1678 then 0 else 0)) else (if x<2620 then (if x<1738 then 1 else 1) else (if x<2646 then 2 else (if x<2680 then 2 else 0)))) else (if x<3186 then (if x<2786 then (if x<2764 then 1 else 0) else (if x<2788 then 1 else (if x<3102 then 2 else 2))) else (if x<3242 then (if x<3188 then 0 else 2) else (if x<3244 then 1 else (if x<3270 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3179 : Finset ℕ := ([132,1594,2646,2764,2788,3102,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3179 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3179 4 (fun x => (if x<2788 then (if x<2646 then (if x<1594 then 0 else 0) else (if x<2764 then 1 else 0)) else (if x<3186 then (if x<3102 then 1 else 1) else (if x<3244 then 0 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3180 : Finset ℕ := ([48,130,132,1594,1678,1702,1738,2620,2646,2680,2702,2764,2786,2788,3102,3186,3188,3242,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3180 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3180 130 4
  · have he : independentCachedBranchMembers3180.erase 130=independentCachedBranchMembers3178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3178
  · have he : independentCachedBranchMembers3180.filter (independentCachedEdge 130)=independentCachedBranchMembers3179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3179
def independentCachedBranchMembers3181 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2680,2702,2730,2764,2786,2788,3102,3130,3158,3186,3188,3192,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3181 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3181 3158 5
  · have he : independentCachedBranchMembers3181.erase 3158=independentCachedBranchMembers3177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3177
  · have he : independentCachedBranchMembers3181.filter (independentCachedEdge 3158)=independentCachedBranchMembers3180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3180
def independentCachedBranchMembers3182 : Finset ℕ := ([80,1628,1650,1652,1708,1734,1768,2620,2646,2680,2702,2764,2786,2788,3102,3186,3188,3242,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3182 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3182 5 (fun x => (if x<2702 then (if x<1734 then (if x<1650 then (if x<1628 then 0 else 0) else (if x<1652 then 0 else (if x<1708 then 1 else 1))) else (if x<2620 then (if x<1768 then 1 else 2) else (if x<2646 then 1 else (if x<2680 then 0 else 0)))) else (if x<3186 then (if x<2786 then (if x<2764 then 1 else 2) else (if x<2788 then 2 else (if x<3102 then 1 else 3))) else (if x<3242 then (if x<3188 then 3 else 0) else (if x<3244 then 3 else (if x<3270 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3183 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2680,2702,2730,2758,2764,2786,2788,3102,3130,3158,3186,3188,3192,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3183 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3183 2758 5
  · have he : independentCachedBranchMembers3183.erase 2758=independentCachedBranchMembers3181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3181
  · have he : independentCachedBranchMembers3183.filter (independentCachedEdge 2758)=independentCachedBranchMembers3182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3182
def independentCachedBranchMembers3184 : Finset ℕ := ([130,1628,1650,1702,1734,1738,1768,2614,2646,2650,2680,2702,2764,2786,3102,3186,3238,3242,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3184 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3184 5 (fun x => (if x<2680 then (if x<1738 then (if x<1650 then (if x<1628 then 0 else 0) else (if x<1702 then 1 else (if x<1734 then 1 else 0))) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2646 then 1 else (if x<2650 then 2 else 1)))) else (if x<3186 then (if x<2764 then (if x<2702 then 0 else 1) else (if x<2786 then 2 else (if x<3102 then 0 else 3))) else (if x<3242 then (if x<3238 then 3 else 0) else (if x<3270 then 3 else (if x<3274 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3185 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2674,2680,2702,2730,2758,2764,2786,2788,3102,3130,3158,3186,3188,3192,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3185 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3185 2674 5
  · have he : independentCachedBranchMembers3185.erase 2674=independentCachedBranchMembers3183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3183
  · have he : independentCachedBranchMembers3185.filter (independentCachedEdge 2674)=independentCachedBranchMembers3184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3184
def independentCachedBranchMembers3186 : Finset ℕ := ([1594,1628,1678,1768,2614,2620,2646,2650,2702,2786,2788,3102,3186,3188,3192,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3186 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3186 5 (fun x => (if x<2788 then (if x<2620 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1768 then 0 else (if x<2614 then 0 else 1))) else (if x<2650 then (if x<2646 then 2 else 2) else (if x<2702 then 1 else (if x<2786 then 1 else 1)))) else (if x<3238 then (if x<3186 then (if x<3102 then 2 else 0) else (if x<3188 then 1 else (if x<3192 then 2 else 0))) else (if x<3270 then (if x<3242 then 1 else (if x<3244 then 0 else 2)) else (if x<3274 then 2 else (if x<3276 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3187 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2674,2680,2702,2730,2758,2764,2786,2788,3102,3130,3158,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3187 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3187 3214 5
  · have he : independentCachedBranchMembers3187.erase 3214=independentCachedBranchMembers3185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3185
  · have he : independentCachedBranchMembers3187.filter (independentCachedEdge 3214)=independentCachedBranchMembers3186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3186
def independentCachedBranchMembers3188 : Finset ℕ := ([48,130,1652,1678,1734,1768,2614,2620,2650,2702,2730,2758,2764,2786,3102,3130,3158,3186,3192,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3188 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3188 5 (fun x => (if x<2758 then (if x<1768 then (if x<1652 then (if x<130 then 0 else 0) else (if x<1678 then 0 else (if x<1734 then 1 else 0))) else (if x<2650 then (if x<2614 then 1 else (if x<2620 then 2 else 0)) else (if x<2702 then 2 else (if x<2730 then 0 else 1)))) else (if x<3158 then (if x<2786 then (if x<2764 then 2 else 1) else (if x<3102 then 3 else (if x<3130 then 3 else 2))) else (if x<3238 then (if x<3186 then 2 else (if x<3192 then 3 else 0)) else (if x<3244 then 2 else (if x<3274 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3189 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2674,2680,2702,2730,2758,2764,2786,2788,3102,3130,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3189 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3189 3162 5
  · have he : independentCachedBranchMembers3189.erase 3162=independentCachedBranchMembers3187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3187
  · have he : independentCachedBranchMembers3189.filter (independentCachedEdge 3162)=independentCachedBranchMembers3188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3188
def independentCachedBranchMembers3190 : Finset ℕ := ([80,132,1650,1678,1702,1768,2620,2646,2650,2674,2702,2730,2764,2788,3102,3130,3188,3192,3244,3270,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3190 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3190 5 (fun x => (if x<2730 then (if x<1768 then (if x<1650 then (if x<132 then 0 else 0) else (if x<1678 then 0 else (if x<1702 then 1 else 0))) else (if x<2650 then (if x<2620 then 1 else (if x<2646 then 2 else 2)) else (if x<2674 then 0 else (if x<2702 then 3 else 0)))) else (if x<3188 then (if x<2788 then (if x<2764 then 1 else 1) else (if x<3102 then 2 else (if x<3130 then 2 else 3))) else (if x<3270 then (if x<3192 then 2 else (if x<3244 then 0 else 0)) else (if x<3274 then 2 else (if x<3298 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3191 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2674,2680,2702,2730,2758,2764,2786,2788,3102,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3191 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3191 3132 5
  · have he : independentCachedBranchMembers3191.erase 3132=independentCachedBranchMembers3189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3189
  · have he : independentCachedBranchMembers3191.filter (independentCachedEdge 3132)=independentCachedBranchMembers3190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3190
def independentCachedBranchMembers3192 : Finset ℕ := ([48,132,1594,1628,1650,1678,1708,1734,1738,1768,2620,2646,2650,2680,2730,2764,2786,3130,3186,3214,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3192 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3192 5 (fun x => (if x<2646 then (if x<1678 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1628 then 0 else (if x<1650 then 1 else 1))) else (if x<1738 then (if x<1708 then 0 else (if x<1734 then 2 else 1)) else (if x<1768 then 2 else (if x<2620 then 1 else 2)))) else (if x<3130 then (if x<2730 then (if x<2650 then 1 else (if x<2680 then 2 else 0)) else (if x<2764 then 2 else (if x<2786 then 0 else 1))) else (if x<3244 then (if x<3186 then 3 else (if x<3214 then 0 else 3)) else (if x<3270 then 4 else (if x<3274 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3193 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2652,2674,2680,2702,2730,2758,2764,2786,2788,3102,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3193 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3193 2652 5
  · have he : independentCachedBranchMembers3193.erase 2652=independentCachedBranchMembers3191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3191
  · have he : independentCachedBranchMembers3193.filter (independentCachedEdge 2652)=independentCachedBranchMembers3192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3192
def independentCachedBranchMembers3194 : Finset ℕ := ([80,132,1594,1628,1650,1702,1708,1738,2614,2620,2650,2702,2730,2758,2764,2786,3102,3130,3158,3186,3192,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3194 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3194 5 (fun x => (if x<2730 then (if x<1708 then (if x<1628 then (if x<132 then 0 else (if x<1594 then 0 else 1)) else (if x<1650 then 1 else (if x<1702 then 0 else 0))) else (if x<2620 then (if x<1738 then 1 else (if x<2614 then 1 else 2)) else (if x<2650 then 1 else (if x<2702 then 0 else 0)))) else (if x<3158 then (if x<2786 then (if x<2758 then 1 else (if x<2764 then 2 else 1)) else (if x<3102 then 3 else (if x<3130 then 3 else 2))) else (if x<3238 then (if x<3186 then 2 else (if x<3192 then 3 else 0)) else (if x<3244 then 2 else (if x<3274 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3195 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2652,2674,2680,2702,2730,2758,2762,2764,2786,2788,3102,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3195 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3195 2762 5
  · have he : independentCachedBranchMembers3195.erase 2762=independentCachedBranchMembers3193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3193
  · have he : independentCachedBranchMembers3195.filter (independentCachedEdge 2762)=independentCachedBranchMembers3194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3194
def independentCachedBranchMembers3196 : Finset ℕ := ([48,130,1594,1628,1652,1708,1734,1738,2620,2646,2650,2674,2702,2730,2764,2788,3102,3130,3188,3192,3244,3270,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3196 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3196 5 (fun x => (if x<2702 then (if x<1734 then (if x<1628 then (if x<130 then 0 else (if x<1594 then 0 else 1)) else (if x<1652 then 1 else (if x<1708 then 0 else 1))) else (if x<2646 then (if x<1738 then 0 else (if x<2620 then 1 else 0)) else (if x<2650 then 2 else (if x<2674 then 1 else 3)))) else (if x<3188 then (if x<2788 then (if x<2730 then 0 else (if x<2764 then 1 else 1)) else (if x<3102 then 2 else (if x<3130 then 2 else 3))) else (if x<3270 then (if x<3192 then 2 else (if x<3244 then 0 else 2)) else (if x<3274 then 2 else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3197 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3197 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3197 2732 5
  · have he : independentCachedBranchMembers3197.erase 2732=independentCachedBranchMembers3195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3195
  · have he : independentCachedBranchMembers3197.filter (independentCachedEdge 2732)=independentCachedBranchMembers3196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3196
def independentCachedBranchMembers3198 : Finset ℕ := ([48,130,1594,1628,1650,1702,1708,1738,2614,2620,2650,2702,2730,2764,2786,3132,3162,3188,3242,3270,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3198 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3198 5 (fun x => (if x<2702 then (if x<1702 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else (if x<1650 then 1 else 2))) else (if x<2614 then (if x<1708 then 2 else (if x<1738 then 1 else 0)) else (if x<2620 then 2 else (if x<2650 then 0 else 1)))) else (if x<3162 then (if x<2764 then (if x<2730 then 0 else 1) else (if x<2786 then 1 else (if x<3132 then 2 else 3))) else (if x<3270 then (if x<3188 then 3 else (if x<3242 then 0 else 3)) else (if x<3276 then 0 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3199 : Finset ℕ := ([1594,1628,2614,2620,2650,2702,2786,3188,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3199 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3199 4 (fun x => (if x<2702 then (if x<2614 then (if x<1628 then 0 else 0) else (if x<2620 then 1 else (if x<2650 then 0 else 0))) else (if x<3242 then (if x<2786 then 1 else (if x<3188 then 1 else 2)) else (if x<3270 then 3 else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
