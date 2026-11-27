/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch0
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers128 : Finset ℕ := ([1596,1614,1652,1746,1768,2620,2652,2662,2738,2792,3102,3158,3180,3256,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers128 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers128 5 (fun x => (if x<2738 then (if x<1768 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2652 then (if x<2620 then 0 else 1) else (if x<2662 then 2 else 2))) else (if x<3180 then (if x<3102 then (if x<2792 then 3 else 2) else (if x<3158 then 0 else 2)) else (if x<3274 then (if x<3256 then 0 else 0) else (if x<3288 then 0 else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers129 : Finset ℕ := ([132,1594,1596,1614,1626,1652,1692,1702,1746,1768,2620,2650,2652,2662,2674,2702,2738,2740,2758,2772,2792,3102,3158,3178,3180,3192,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers129 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers129 132 5
  · have he : independentCachedBranchMembers129.erase 132=independentCachedBranchMembers127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound127
  · have he : independentCachedBranchMembers129.filter (independentCachedEdge 132)=independentCachedBranchMembers128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound128
def independentCachedBranchMembers130 : Finset ℕ := ([1626,1692,1702,1746,1768,2650,2652,2662,2772,2792,3102,3158,3178,3180,3244,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers130 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers130 5 (fun x => (if x<2772 then (if x<1768 then (if x<1702 then (if x<1692 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2652 then (if x<2650 then 0 else 1) else (if x<2662 then 2 else 2))) else (if x<3178 then (if x<3102 then (if x<2792 then 3 else 2) else (if x<3158 then 0 else 2)) else (if x<3244 then (if x<3180 then 0 else 2) else (if x<3288 then 0 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers131 : Finset ℕ := ([48,132,1594,1596,1614,1626,1652,1692,1702,1746,1768,2620,2650,2652,2662,2674,2702,2738,2740,2758,2772,2792,3102,3158,3178,3180,3192,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers131 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers131 48 5
  · have he : independentCachedBranchMembers131.erase 48=independentCachedBranchMembers129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound129
  · have he : independentCachedBranchMembers131.filter (independentCachedEdge 48)=independentCachedBranchMembers130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound130
def independentCachedBranchMembers132 : Finset ℕ := ([1614,1652,1692,1702,2620,2650,2652,2662,2702,2738,2740,2772,2792,3158,3178,3180,3256,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers132 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers132 5 (fun x => (if x<2738 then (if x<2620 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1702 then 0 else 0)) else (if x<2652 then (if x<2650 then 1 else 1) else (if x<2662 then 0 else (if x<2702 then 0 else 0)))) else (if x<3178 then (if x<2772 then (if x<2740 then 1 else 0) else (if x<2792 then 1 else (if x<3158 then 1 else 2))) else (if x<3256 then (if x<3180 then 2 else 3) else (if x<3288 then 3 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers133 : Finset ℕ := ([48,132,1594,1596,1614,1626,1652,1678,1692,1702,1746,1768,2620,2650,2652,2662,2674,2702,2738,2740,2758,2772,2792,3102,3158,3178,3180,3192,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers133 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers133 1678 5
  · have he : independentCachedBranchMembers133.erase 1678=independentCachedBranchMembers131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound131
  · have he : independentCachedBranchMembers133.filter (independentCachedEdge 1678)=independentCachedBranchMembers132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound132
def independentCachedBranchMembers134 : Finset ℕ := ([132,1596,1614,1626,1652,1692,1702,2652,2662,2674,2702,2740,2758,2792,3178,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers134 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers134 5 (fun x => (if x<2674 then (if x<1652 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1626 then 1 else 0)) else (if x<1702 then (if x<1692 then 2 else 0) else (if x<2652 then 1 else (if x<2662 then 1 else 2)))) else (if x<2792 then (if x<2740 then (if x<2702 then 0 else 2) else (if x<2758 then 0 else 1)) else (if x<3244 then (if x<3178 then 3 else 0) else (if x<3256 then 0 else (if x<3274 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers135 : Finset ℕ := ([1626,1692,1702,2652,2662,2792,3178,3244] : List ℕ).toFinset
theorem independentCachedBranchBound135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers135 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers135 4 (fun x => (if x<2662 then (if x<1702 then (if x<1692 then 0 else 0) else (if x<2652 then 1 else 0)) else (if x<3178 then (if x<2792 then 1 else 2) else (if x<3244 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers136 : Finset ℕ := ([48,132,1596,1614,1626,1652,1692,1702,2652,2662,2674,2702,2740,2758,2792,3178,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers136 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers136 48 4
  · have he : independentCachedBranchMembers136.erase 48=independentCachedBranchMembers134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound134
  · have he : independentCachedBranchMembers136.filter (independentCachedEdge 48)=independentCachedBranchMembers135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound135
def independentCachedBranchMembers137 : Finset ℕ := ([48,132,1594,1596,1614,1626,1628,1652,1678,1692,1702,1746,1768,2620,2650,2652,2662,2674,2702,2738,2740,2758,2772,2792,3102,3158,3178,3180,3192,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers137 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers137 1628 5
  · have he : independentCachedBranchMembers137.erase 1628=independentCachedBranchMembers133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound133
  · have he : independentCachedBranchMembers137.filter (independentCachedEdge 1628)=independentCachedBranchMembers136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound136
def independentCachedBranchMembers138 : Finset ℕ := ([1594,1614,1626,1652,1692,1702,1746,1768,2620,2652,2662,2674,2702,2740,2772,3158,3180,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers138 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers138 5 (fun x => (if x<2652 then (if x<1692 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 0)) else (if x<1746 then (if x<1702 then 0 else 0) else (if x<1768 then 0 else (if x<2620 then 0 else 2)))) else (if x<2772 then (if x<2674 then (if x<2662 then 1 else 2) else (if x<2702 then 1 else (if x<2740 then 2 else 1))) else (if x<3180 then (if x<3158 then 2 else 3) else (if x<3192 then 3 else (if x<3274 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers139 : Finset ℕ := ([1626,1692,1702,1746,1768,2652,2662,2772,3158,3180] : List ℕ).toFinset
theorem independentCachedBranchBound139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers139 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers139 4 (fun x => (if x<2652 then (if x<1702 then (if x<1692 then 0 else 0) else (if x<1746 then 1 else (if x<1768 then 1 else 0))) else (if x<2772 then (if x<2662 then 2 else 2) else (if x<3158 then 3 else (if x<3180 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers140 : Finset ℕ := ([48,1594,1614,1626,1652,1692,1702,1746,1768,2620,2652,2662,2674,2702,2740,2772,3158,3180,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers140 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers140 48 4
  · have he : independentCachedBranchMembers140.erase 48=independentCachedBranchMembers138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound138
  · have he : independentCachedBranchMembers140.filter (independentCachedEdge 48)=independentCachedBranchMembers139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound139
def independentCachedBranchMembers141 : Finset ℕ := ([48,132,1594,1596,1614,1626,1628,1652,1678,1692,1702,1746,1768,2620,2650,2652,2662,2674,2702,2716,2738,2740,2758,2772,2792,3102,3158,3178,3180,3192,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers141 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers141 2716 5
  · have he : independentCachedBranchMembers141.erase 2716=independentCachedBranchMembers137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound137
  · have he : independentCachedBranchMembers141.filter (independentCachedEdge 2716)=independentCachedBranchMembers140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound140
def independentCachedBranchMembers142 : Finset ℕ := ([1594,1596,1614,1652,1692,1702,1746,1768,2650,2652,2662,2702,2738,2740,2758,3192,3244,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers142 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers142 5 (fun x => (if x<2652 then (if x<1692 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1652 then 0 else 0)) else (if x<1746 then (if x<1702 then 0 else 0) else (if x<1768 then 0 else (if x<2650 then 0 else 2)))) else (if x<2758 then (if x<2702 then (if x<2662 then 1 else 2) else (if x<2738 then 2 else (if x<2740 then 2 else 1))) else (if x<3244 then (if x<3192 then 1 else 3) else (if x<3288 then 3 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers143 : Finset ℕ := ([1596,1614,1652,1746,1768,2652,2662,2738,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers143 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers143 4 (fun x => (if x<2652 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1746 then 1 else (if x<1768 then 1 else 0))) else (if x<2738 then (if x<2662 then 2 else 2) else (if x<3288 then 3 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers144 : Finset ℕ := ([132,1594,1596,1614,1652,1692,1702,1746,1768,2650,2652,2662,2702,2738,2740,2758,3192,3244,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers144 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers144 132 4
  · have he : independentCachedBranchMembers144.erase 132=independentCachedBranchMembers142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound142
  · have he : independentCachedBranchMembers144.filter (independentCachedEdge 132)=independentCachedBranchMembers143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound143
def independentCachedBranchMembers145 : Finset ℕ := ([48,132,1594,1596,1614,1626,1628,1652,1678,1692,1702,1746,1768,2620,2638,2650,2652,2662,2674,2702,2716,2738,2740,2758,2772,2792,3102,3158,3178,3180,3192,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers145 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers145 2638 5
  · have he : independentCachedBranchMembers145.erase 2638=independentCachedBranchMembers141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound141
  · have he : independentCachedBranchMembers145.filter (independentCachedEdge 2638)=independentCachedBranchMembers144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound144
def independentCachedBranchMembers146 : Finset ℕ := ([1594,1614,1628,1652,1692,1702,1746,1768,2620,2650,2674,2738,2758,2772,3158,3180,3244,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers146 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers146 5 (fun x => (if x<2674 then (if x<1702 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else (if x<1692 then 0 else 0))) else (if x<1768 then (if x<1746 then 0 else 0) else (if x<2620 then 0 else (if x<2650 then 1 else 1)))) else (if x<3180 then (if x<2758 then (if x<2738 then 2 else 1) else (if x<2772 then 2 else (if x<3158 then 1 else 2))) else (if x<3274 then (if x<3244 then 3 else 4) else (if x<3288 then 3 else (if x<3298 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers147 : Finset ℕ := ([1614,1652,1692,1702,2620,2650,2738,2772,3158,3180,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers147 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers147 4 (fun x => (if x<2738 then (if x<1702 then (if x<1652 then 0 else (if x<1692 then 0 else 0)) else (if x<2620 then 0 else (if x<2650 then 1 else 1))) else (if x<3180 then (if x<2772 then 1 else (if x<3158 then 1 else 2)) else (if x<3288 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers148 : Finset ℕ := ([1594,1614,1628,1652,1678,1692,1702,1746,1768,2620,2650,2674,2738,2758,2772,3158,3180,3244,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers148 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers148 1678 4
  · have he : independentCachedBranchMembers148.erase 1678=independentCachedBranchMembers146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound146
  · have he : independentCachedBranchMembers148.filter (independentCachedEdge 1678)=independentCachedBranchMembers147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound147
def independentCachedBranchMembers149 : Finset ℕ := ([48,132,1594,1596,1614,1626,1628,1652,1678,1692,1702,1746,1768,2618,2620,2638,2650,2652,2662,2674,2702,2716,2738,2740,2758,2772,2792,3102,3158,3178,3180,3192,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers149 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers149 2618 5
  · have he : independentCachedBranchMembers149.erase 2618=independentCachedBranchMembers145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound145
  · have he : independentCachedBranchMembers149.filter (independentCachedEdge 2618)=independentCachedBranchMembers148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound148
def independentCachedBranchMembers150 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers150 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers150 3304 6
  · have he : independentCachedBranchMembers150.erase 3304=independentCachedBranchMembers126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound126
  · have he : independentCachedBranchMembers150.filter (independentCachedEdge 3304)=independentCachedBranchMembers149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound149
def independentCachedBranchMembers151 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2618,2620,2650,2662,2668,2702,2738,2740,2772,2776,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers151 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers151 6 (fun x => (if x<2740 then (if x<2618 then (if x<1678 then (if x<1628 then 0 else (if x<1642 then 0 else 0)) else (if x<1746 then (if x<1720 then 0 else 0) else (if x<1764 then 0 else 0))) else (if x<2662 then (if x<2620 then 1 else (if x<2650 then 2 else 2)) else (if x<2702 then (if x<2668 then 1 else 3) else (if x<2738 then 1 else 2)))) else (if x<3188 then (if x<2792 then (if x<2772 then 1 else (if x<2776 then 2 else 3)) else (if x<3118 then (if x<3102 then 1 else 4) else (if x<3186 then 3 else 4))) else (if x<3244 then (if x<3226 then (if x<3192 then 5 else 3) else (if x<3238 then 3 else 4)) else (if x<3274 then (if x<3270 then 5 else 5) else (if x<3276 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers152 : Finset ℕ := ([1628,1642,1746,1764,2620,2650,2662,2668,2702,2738,2772,2792,3118,3188,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers152 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers152 5 (fun x => (if x<2702 then (if x<2620 then (if x<1746 then (if x<1642 then 0 else 0) else (if x<1764 then 0 else 0)) else (if x<2662 then (if x<2650 then 1 else 0) else (if x<2668 then 1 else 0))) else (if x<3118 then (if x<2772 then (if x<2738 then 1 else 1) else (if x<2792 then 0 else 1)) else (if x<3270 then (if x<3188 then 2 else 2) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers153 : Finset ℕ := ([1590,1626,1628,1642,1678,1720,1746,1764,2618,2620,2650,2662,2668,2702,2738,2740,2772,2776,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers153 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers153 1626 5
  · have he : independentCachedBranchMembers153.erase 1626=independentCachedBranchMembers151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound151
  · have he : independentCachedBranchMembers153.filter (independentCachedEdge 1626)=independentCachedBranchMembers152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound152
def independentCachedBranchMembers154 : Finset ℕ := ([1590,1628,1720,1746,2620,2650,2662,2702,2738,2772,2776,2792,3186,3226,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers154 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers154 5 (fun x => (if x<2738 then (if x<2620 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2662 then (if x<2650 then 0 else 1) else (if x<2702 then 1 else 1))) else (if x<3186 then (if x<2776 then (if x<2772 then 0 else 1) else (if x<2792 then 0 else 1)) else (if x<3238 then (if x<3226 then 2 else 2) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers155 : Finset ℕ := ([1590,1596,1626,1628,1642,1678,1720,1746,1764,2618,2620,2650,2662,2668,2702,2738,2740,2772,2776,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers155 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers155 1596 5
  · have he : independentCachedBranchMembers155.erase 1596=independentCachedBranchMembers153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound153
  · have he : independentCachedBranchMembers155.filter (independentCachedEdge 1596)=independentCachedBranchMembers154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound154
def independentCachedBranchMembers156 : Finset ℕ := ([1590,1626,1642,1678,1746,2618,2650,2662,2702,2738,3102,3118,3186,3226,3238,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers156 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers156 5 (fun x => (if x<2702 then (if x<1746 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1678 then 1 else 0)) else (if x<2650 then (if x<2618 then 1 else 2) else (if x<2662 then 1 else 2))) else (if x<3186 then (if x<3102 then (if x<2738 then 2 else 3) else (if x<3118 then 0 else 2)) else (if x<3238 then (if x<3226 then 0 else 2) else (if x<3270 then 0 else (if x<3274 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers157 : Finset ℕ := ([252,1590,1596,1626,1628,1642,1678,1720,1746,1764,2618,2620,2650,2662,2668,2702,2738,2740,2772,2776,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers157 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers157 252 5
  · have he : independentCachedBranchMembers157.erase 252=independentCachedBranchMembers155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound155
  · have he : independentCachedBranchMembers157.filter (independentCachedEdge 252)=independentCachedBranchMembers156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound156
def independentCachedBranchMembers158 : Finset ℕ := ([1596,1678,1720,1746,1764,2618,2620,2662,2702,2772,3102,3118,3186,3188,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers158 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers158 5 (fun x => (if x<2702 then (if x<1764 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2620 then (if x<2618 then 0 else 2) else (if x<2662 then 1 else 2))) else (if x<3186 then (if x<3102 then (if x<2772 then 2 else 3) else (if x<3118 then 0 else 2)) else (if x<3226 then (if x<3188 then 2 else 0) else (if x<3244 then 2 else (if x<3270 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers159 : Finset ℕ := ([72,252,1590,1596,1626,1628,1642,1678,1720,1746,1764,2618,2620,2650,2662,2668,2702,2738,2740,2772,2776,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers159 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers159 72 5
  · have he : independentCachedBranchMembers159.erase 72=independentCachedBranchMembers157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound157
  · have he : independentCachedBranchMembers159.filter (independentCachedEdge 72)=independentCachedBranchMembers158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound158
def independentCachedBranchMembers160 : Finset ℕ := ([1590,1642,1720,1764,2618,2620,2650,2662,2702,2738,2740,2772,2792,3118,3186,3188,3226,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers160 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers160 5 (fun x => (if x<2738 then (if x<2618 then (if x<1720 then (if x<1642 then 0 else 0) else (if x<1764 then 0 else 0)) else (if x<2650 then (if x<2620 then 0 else 1) else (if x<2662 then 1 else (if x<2702 then 0 else 1)))) else (if x<3186 then (if x<2772 then (if x<2740 then 1 else 0) else (if x<2792 then 1 else (if x<3118 then 0 else 2))) else (if x<3226 then (if x<3188 then 2 else 3) else (if x<3238 then 2 else (if x<3270 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers161 : Finset ℕ := ([72,252,1590,1596,1626,1628,1642,1678,1720,1746,1764,1768,2618,2620,2650,2662,2668,2702,2738,2740,2772,2776,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers161 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers161 1768 5
  · have he : independentCachedBranchMembers161.erase 1768=independentCachedBranchMembers159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound159
  · have he : independentCachedBranchMembers161.filter (independentCachedEdge 1768)=independentCachedBranchMembers160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound160
def independentCachedBranchMembers162 : Finset ℕ := ([252,1590,1596,1626,1642,1720,1764,2618,2662,2668,2702,2740,2776,2792,3188,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers162 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers162 5 (fun x => (if x<2668 then (if x<1642 then (if x<1596 then (if x<1590 then 0 else 1) else (if x<1626 then 0 else 1)) else (if x<1764 then (if x<1720 then 2 else 1) else (if x<2618 then 0 else (if x<2662 then 1 else 2)))) else (if x<2792 then (if x<2740 then (if x<2702 then 0 else 3) else (if x<2776 then 0 else 1)) else (if x<3238 then (if x<3188 then 2 else 0) else (if x<3244 then 3 else (if x<3274 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers163 : Finset ℕ := ([1596,1720,1764,2618,2662,2702,3188,3244] : List ℕ).toFinset
theorem independentCachedBranchBound163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers163 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers163 4 (fun x => (if x<2662 then (if x<1764 then (if x<1720 then 0 else 1) else (if x<2618 then 0 else 0)) else (if x<3188 then (if x<2702 then 1 else 2) else (if x<3244 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers164 : Finset ℕ := ([72,252,1590,1596,1626,1642,1720,1764,2618,2662,2668,2702,2740,2776,2792,3188,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers164 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers164 72 4
  · have he : independentCachedBranchMembers164.erase 72=independentCachedBranchMembers162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound162
  · have he : independentCachedBranchMembers164.filter (independentCachedEdge 72)=independentCachedBranchMembers163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound163
def independentCachedBranchMembers165 : Finset ℕ := ([72,252,1590,1594,1596,1626,1628,1642,1678,1720,1746,1764,1768,2618,2620,2650,2662,2668,2702,2738,2740,2772,2776,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers165 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers165 1594 5
  · have he : independentCachedBranchMembers165.erase 1594=independentCachedBranchMembers161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound161
  · have he : independentCachedBranchMembers165.filter (independentCachedEdge 1594)=independentCachedBranchMembers164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound164
def independentCachedBranchMembers166 : Finset ℕ := ([1590,1596,1628,1642,1678,1720,1746,1764,2618,2650,2662,2668,2740,2772,2792,3118,3186,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers166 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers166 5 (fun x => (if x<2650 then (if x<1678 then (if x<1628 then (if x<1596 then 0 else 1) else (if x<1642 then 0 else 0)) else (if x<1746 then (if x<1720 then 0 else 0) else (if x<1764 then 0 else (if x<2618 then 0 else 1)))) else (if x<2792 then (if x<2668 then (if x<2662 then 2 else 2) else (if x<2740 then 1 else (if x<2772 then 1 else 2))) else (if x<3186 then (if x<3118 then 2 else 3) else (if x<3192 then 3 else (if x<3274 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers167 : Finset ℕ := ([1596,1678,1720,1746,1764,2618,2662,2772,3118,3186] : List ℕ).toFinset
theorem independentCachedBranchBound167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers167 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers167 4 (fun x => (if x<2618 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<1746 then 1 else (if x<1764 then 1 else 0))) else (if x<2772 then (if x<2662 then 2 else 2) else (if x<3118 then 3 else (if x<3186 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers168 : Finset ℕ := ([72,1590,1596,1628,1642,1678,1720,1746,1764,2618,2650,2662,2668,2740,2772,2792,3118,3186,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers168 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers168 72 4
  · have he : independentCachedBranchMembers168.erase 72=independentCachedBranchMembers166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound166
  · have he : independentCachedBranchMembers168.filter (independentCachedEdge 72)=independentCachedBranchMembers167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound167
def independentCachedBranchMembers169 : Finset ℕ := ([72,252,1590,1594,1596,1626,1628,1642,1678,1720,1746,1764,1768,2618,2620,2650,2662,2668,2702,2738,2740,2772,2776,2788,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers169 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers169 2788 5
  · have he : independentCachedBranchMembers169.erase 2788=independentCachedBranchMembers165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound165
  · have he : independentCachedBranchMembers169.filter (independentCachedEdge 2788)=independentCachedBranchMembers168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound168
def independentCachedBranchMembers170 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2618,2620,2662,2738,2740,2776,2792,3192,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers170 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers170 5 (fun x => (if x<2662 then (if x<1720 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 0 else 0)) else (if x<1764 then (if x<1746 then 0 else 0) else (if x<2618 then 0 else (if x<2620 then 1 else 2)))) else (if x<2792 then (if x<2740 then (if x<2738 then 1 else 2) else (if x<2776 then 1 else 2)) else (if x<3226 then (if x<3192 then 1 else 3) else (if x<3244 then 3 else (if x<3270 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers171 : Finset ℕ := ([1628,1642,1746,1764,2620,2662,2738,2792,3270] : List ℕ).toFinset
theorem independentCachedBranchBound171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers171 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers171 4 (fun x => (if x<2620 then (if x<1746 then (if x<1642 then 0 else 0) else (if x<1764 then 0 else 0)) else (if x<2738 then (if x<2662 then 1 else 1) else (if x<2792 then 1 else (if x<3270 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers172 : Finset ℕ := ([1590,1626,1628,1642,1678,1720,1746,1764,2618,2620,2662,2738,2740,2776,2792,3192,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers172 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers172 1626 4
  · have he : independentCachedBranchMembers172.erase 1626=independentCachedBranchMembers170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound170
  · have he : independentCachedBranchMembers172.filter (independentCachedEdge 1626)=independentCachedBranchMembers171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound171
def independentCachedBranchMembers173 : Finset ℕ := ([1590,1626,1642,1678,1746,2618,2662,2738,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers173 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers173 4 (fun x => (if x<2618 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1678 then 1 else (if x<1746 then 0 else 1))) else (if x<2738 then (if x<2662 then 2 else 2) else (if x<3226 then 3 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers174 : Finset ℕ := ([252,1590,1626,1628,1642,1678,1720,1746,1764,2618,2620,2662,2738,2740,2776,2792,3192,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers174 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers174 252 4
  · have he : independentCachedBranchMembers174.erase 252=independentCachedBranchMembers172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound172
  · have he : independentCachedBranchMembers174.filter (independentCachedEdge 252)=independentCachedBranchMembers173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound173
def independentCachedBranchMembers175 : Finset ℕ := ([72,252,1590,1594,1596,1626,1628,1642,1678,1720,1746,1764,1768,2614,2618,2620,2650,2662,2668,2702,2738,2740,2772,2776,2788,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers175 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers175 2614 5
  · have he : independentCachedBranchMembers175.erase 2614=independentCachedBranchMembers169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound169
  · have he : independentCachedBranchMembers175.filter (independentCachedEdge 2614)=independentCachedBranchMembers174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound174
def independentCachedBranchMembers176 : Finset ℕ := ([1590,1594,1628,1642,1678,1720,1746,1764,2620,2650,2668,2738,2772,2776,3118,3186,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers176 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers176 5 (fun x => (if x<2668 then (if x<1720 then (if x<1628 then (if x<1594 then 0 else 1) else (if x<1642 then 0 else (if x<1678 then 0 else 0))) else (if x<1764 then (if x<1746 then 0 else 0) else (if x<2620 then 0 else (if x<2650 then 1 else 1)))) else (if x<3186 then (if x<2772 then (if x<2738 then 2 else 1) else (if x<2776 then 1 else (if x<3118 then 2 else 2))) else (if x<3244 then (if x<3226 then 3 else 2) else (if x<3270 then 4 else (if x<3274 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers177 : Finset ℕ := ([1590,1642,1720,1764,2620,2650,2738,2772,3118,3186,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers177 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers177 4 (fun x => (if x<2738 then (if x<1764 then (if x<1642 then 0 else (if x<1720 then 0 else 0)) else (if x<2620 then 0 else (if x<2650 then 1 else 1))) else (if x<3186 then (if x<2772 then 1 else (if x<3118 then 1 else 2)) else (if x<3226 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers178 : Finset ℕ := ([1590,1594,1628,1642,1678,1720,1746,1764,1768,2620,2650,2668,2738,2772,2776,3118,3186,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers178 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers178 1768 4
  · have he : independentCachedBranchMembers178.erase 1768=independentCachedBranchMembers176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound176
  · have he : independentCachedBranchMembers178.filter (independentCachedEdge 1768)=independentCachedBranchMembers177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound177
def independentCachedBranchMembers179 : Finset ℕ := ([72,252,1590,1594,1596,1626,1628,1642,1678,1720,1746,1764,1768,2614,2618,2620,2650,2652,2662,2668,2702,2738,2740,2772,2776,2788,2792,3102,3118,3186,3188,3192,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers179 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers179 2652 5
  · have he : independentCachedBranchMembers179.erase 2652=independentCachedBranchMembers175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound175
  · have he : independentCachedBranchMembers179.filter (independentCachedEdge 2652)=independentCachedBranchMembers178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound178
def independentCachedBranchMembers180 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3214,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers180 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers180 3214 6
  · have he : independentCachedBranchMembers180.erase 3214=independentCachedBranchMembers150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound150
  · have he : independentCachedBranchMembers180.filter (independentCachedEdge 3214)=independentCachedBranchMembers179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound179
def independentCachedBranchMembers181 : Finset ℕ := ([1590,1628,1642,1678,1686,1720,1746,1764,1776,2618,2652,2662,2674,2710,2732,2740,2758,2762,2792,2800,3102,3158,3180,3188,3192,3238,3250,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers181 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers181 6 (fun x => (if x<2740 then (if x<1764 then (if x<1678 then (if x<1628 then 0 else (if x<1642 then 0 else 0)) else (if x<1720 then (if x<1686 then 0 else 1) else (if x<1746 then 0 else 0))) else (if x<2662 then (if x<2618 then (if x<1776 then 0 else 1) else (if x<2652 then 2 else 2)) else (if x<2710 then (if x<2674 then 2 else 3) else (if x<2732 then 2 else 2)))) else (if x<3188 then (if x<2800 then (if x<2762 then (if x<2758 then 1 else 3) else (if x<2792 then 2 else 1)) else (if x<3158 then (if x<3102 then 2 else 4) else (if x<3180 then 3 else 4))) else (if x<3276 then (if x<3238 then (if x<3192 then 5 else 3) else (if x<3250 then 4 else 5)) else (if x<3288 then (if x<3284 then 3 else 4) else (if x<3298 then 5 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers182 : Finset ℕ := ([1590,1628,1720,1746,1776,2652,2662,2762,2792,2800,3102,3158,3180,3188,3250,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers182 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers182 5 (fun x => (if x<2792 then (if x<1776 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2662 then (if x<2652 then 1 else 2) else (if x<2762 then 2 else 2))) else (if x<3180 then (if x<3102 then (if x<2800 then 1 else 2) else (if x<3158 then 1 else 0)) else (if x<3250 then (if x<3188 then 3 else 2) else (if x<3288 then 0 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers183 : Finset ℕ := ([132,1590,1628,1642,1678,1686,1720,1746,1764,1776,2618,2652,2662,2674,2710,2732,2740,2758,2762,2792,2800,3102,3158,3180,3188,3192,3238,3250,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers183 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers183 132 5
  · have he : independentCachedBranchMembers183.erase 132=independentCachedBranchMembers181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound181
  · have he : independentCachedBranchMembers183.filter (independentCachedEdge 132)=independentCachedBranchMembers182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound182
def independentCachedBranchMembers184 : Finset ℕ := ([1628,1642,1686,1746,1764,2652,2662,2710,2732,2792,3102,3158,3180,3238,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers184 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers184 5 (fun x => (if x<2732 then (if x<1764 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1746 then 1 else 0)) else (if x<2662 then (if x<2652 then 0 else 2) else (if x<2710 then 2 else 2))) else (if x<3180 then (if x<3102 then (if x<2792 then 2 else 1) else (if x<3158 then 1 else 2)) else (if x<3284 then (if x<3238 then 0 else 2) else (if x<3288 then 0 else (if x<3298 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers185 : Finset ℕ := ([48,132,1590,1628,1642,1678,1686,1720,1746,1764,1776,2618,2652,2662,2674,2710,2732,2740,2758,2762,2792,2800,3102,3158,3180,3188,3192,3238,3250,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers185 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers185 48 5
  · have he : independentCachedBranchMembers185.erase 48=independentCachedBranchMembers183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound183
  · have he : independentCachedBranchMembers185.filter (independentCachedEdge 48)=independentCachedBranchMembers184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound184
def independentCachedBranchMembers186 : Finset ℕ := ([48,132,1590,1642,1686,1720,1764,1776,2618,2652,2662,2674,2740,2758,2792,3188,3238,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers186 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers186 5 (fun x => (if x<2652 then (if x<1686 then (if x<1590 then (if x<132 then 0 else 0) else (if x<1642 then 1 else 1)) else (if x<1764 then (if x<1720 then 2 else 1) else (if x<1776 then 1 else (if x<2618 then 2 else 0)))) else (if x<2792 then (if x<2674 then (if x<2662 then 3 else 1) else (if x<2740 then 3 else (if x<2758 then 0 else 3))) else (if x<3238 then (if x<3188 then 1 else 4) else (if x<3250 then 4 else (if x<3284 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers187 : Finset ℕ := ([48,132,1590,1628,1642,1678,1686,1720,1746,1764,1768,1776,2618,2652,2662,2674,2710,2732,2740,2758,2762,2792,2800,3102,3158,3180,3188,3192,3238,3250,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers187 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers187 1768 5
  · have he : independentCachedBranchMembers187.erase 1768=independentCachedBranchMembers185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound185
  · have he : independentCachedBranchMembers187.filter (independentCachedEdge 1768)=independentCachedBranchMembers186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound186
def independentCachedBranchMembers188 : Finset ℕ := ([1590,1642,1720,1764,2618,2652,2662,2710,2732,2740,2762,2792,2800,3158,3180,3188,3238,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers188 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers188 5 (fun x => (if x<2740 then (if x<2618 then (if x<1720 then (if x<1642 then 0 else 0) else (if x<1764 then 0 else 0)) else (if x<2662 then (if x<2652 then 0 else 1) else (if x<2710 then 0 else (if x<2732 then 1 else 1)))) else (if x<3180 then (if x<2792 then (if x<2762 then 0 else 1) else (if x<2800 then 0 else (if x<3158 then 1 else 2))) else (if x<3238 then (if x<3188 then 2 else 3) else (if x<3288 then 2 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers189 : Finset ℕ := ([48,132,1590,1594,1628,1642,1678,1686,1720,1746,1764,1768,1776,2618,2652,2662,2674,2710,2732,2740,2758,2762,2792,2800,3102,3158,3180,3188,3192,3238,3250,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers189 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers189 1594 5
  · have he : independentCachedBranchMembers189.erase 1594=independentCachedBranchMembers187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound187
  · have he : independentCachedBranchMembers189.filter (independentCachedEdge 1594)=independentCachedBranchMembers188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound188
def independentCachedBranchMembers190 : Finset ℕ := ([1590,1628,1642,1678,1686,1720,1746,1764,2618,2662,2732,2740,2758,2792,2800,3158,3192,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers190 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers190 5 (fun x => (if x<2662 then (if x<1686 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 0 else 0)) else (if x<1746 then (if x<1720 then 1 else 0) else (if x<1764 then 0 else (if x<2618 then 0 else 2)))) else (if x<2800 then (if x<2740 then (if x<2732 then 2 else 2) else (if x<2758 then 1 else (if x<2792 then 1 else 1))) else (if x<3192 then (if x<3158 then 2 else 3) else (if x<3250 then 3 else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers191 : Finset ℕ := ([1628,1642,1686,1746,1764,2662,2732,2792,3158,3288] : List ℕ).toFinset
theorem independentCachedBranchBound191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers191 4 (fun x => (if x<2662 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1746 then 1 else (if x<1764 then 0 else 0))) else (if x<2792 then (if x<2732 then 2 else 2) else (if x<3158 then 1 else (if x<3288 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers192 : Finset ℕ := ([48,1590,1628,1642,1678,1686,1720,1746,1764,2618,2662,2732,2740,2758,2792,2800,3158,3192,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers192 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers192 48 4
  · have he : independentCachedBranchMembers192.erase 48=independentCachedBranchMembers190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound190
  · have he : independentCachedBranchMembers192.filter (independentCachedEdge 48)=independentCachedBranchMembers191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound191
def independentCachedBranchMembers193 : Finset ℕ := ([48,132,1590,1594,1628,1642,1678,1686,1720,1746,1764,1768,1776,2618,2652,2662,2674,2710,2732,2740,2758,2762,2788,2792,2800,3102,3158,3180,3188,3192,3238,3250,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers193 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers193 2788 5
  · have he : independentCachedBranchMembers193.erase 2788=independentCachedBranchMembers189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound189
  · have he : independentCachedBranchMembers193.filter (independentCachedEdge 2788)=independentCachedBranchMembers192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound192
def independentCachedBranchMembers194 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,1776,2618,2662,2674,2710,2740,2762,2792,3180,3192,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers194 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers194 5 (fun x => (if x<2662 then (if x<1720 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 0 else 0)) else (if x<1764 then (if x<1746 then 0 else 0) else (if x<1776 then 0 else (if x<2618 then 1 else 2)))) else (if x<2792 then (if x<2710 then (if x<2674 then 2 else 1) else (if x<2740 then 2 else (if x<2762 then 1 else 2))) else (if x<3192 then (if x<3180 then 1 else 3) else (if x<3284 then 4 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers195 : Finset ℕ := ([1590,1628,1720,1746,1776,2662,2762,2792,3180,3298] : List ℕ).toFinset
theorem independentCachedBranchBound195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers195 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers195 4 (fun x => (if x<2662 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<1746 then 0 else (if x<1776 then 0 else 1))) else (if x<2792 then (if x<2762 then 2 else 2) else (if x<3180 then 1 else (if x<3298 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers196 : Finset ℕ := ([132,1590,1628,1642,1678,1720,1746,1764,1776,2618,2662,2674,2710,2740,2762,2792,3180,3192,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers196 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers196 132 4
  · have he : independentCachedBranchMembers196.erase 132=independentCachedBranchMembers194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound194
  · have he : independentCachedBranchMembers196.filter (independentCachedEdge 132)=independentCachedBranchMembers195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound195
def independentCachedBranchMembers197 : Finset ℕ := ([48,132,1590,1594,1628,1642,1678,1686,1720,1746,1764,1768,1776,2614,2618,2652,2662,2674,2710,2732,2740,2758,2762,2788,2792,2800,3102,3158,3180,3188,3192,3238,3250,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers197 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers197 2614 5
  · have he : independentCachedBranchMembers197.erase 2614=independentCachedBranchMembers193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound193
  · have he : independentCachedBranchMembers197.filter (independentCachedEdge 2614)=independentCachedBranchMembers196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound196
def independentCachedBranchMembers198 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,1768,2674,2710,2732,2758,2762,2800,3158,3180,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers198 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers198 5 (fun x => (if x<2732 then (if x<1746 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 0 else (if x<1720 then 0 else 0))) else (if x<1768 then (if x<1764 then 0 else 0) else (if x<2674 then 1 else (if x<2710 then 2 else 1)))) else (if x<3180 then (if x<2762 then (if x<2758 then 1 else 2) else (if x<2800 then 1 else (if x<3158 then 1 else 2))) else (if x<3284 then (if x<3250 then 3 else 4) else (if x<3288 then 3 else (if x<3298 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers199 : Finset ℕ := ([1590,1642,1720,1764,2710,2732,2762,2800,3158,3180,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers199 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers199 4 (fun x => (if x<2762 then (if x<1764 then (if x<1642 then 0 else (if x<1720 then 0 else 0)) else (if x<2710 then 0 else (if x<2732 then 1 else 1))) else (if x<3180 then (if x<2800 then 1 else (if x<3158 then 1 else 2)) else (if x<3288 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers200 : Finset ℕ := ([1590,1594,1628,1642,1678,1720,1746,1764,1768,2674,2710,2732,2758,2762,2800,3158,3180,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers200 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers200 1594 4
  · have he : independentCachedBranchMembers200.erase 1594=independentCachedBranchMembers198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound198
  · have he : independentCachedBranchMembers200.filter (independentCachedEdge 1594)=independentCachedBranchMembers199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound199
def independentCachedBranchMembers201 : Finset ℕ := ([48,132,1590,1594,1628,1642,1678,1686,1720,1746,1764,1768,1776,2614,2618,2652,2662,2674,2702,2710,2732,2740,2758,2762,2788,2792,2800,3102,3158,3180,3188,3192,3238,3250,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers201 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers201 2702 5
  · have he : independentCachedBranchMembers201.erase 2702=independentCachedBranchMembers197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound197
  · have he : independentCachedBranchMembers201.filter (independentCachedEdge 2702)=independentCachedBranchMembers200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound200
def independentCachedBranchMembers202 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3164,3178,3180,3186,3188,3192,3214,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers202 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers202 3164 6
  · have he : independentCachedBranchMembers202.erase 3164=independentCachedBranchMembers180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound180
  · have he : independentCachedBranchMembers202.filter (independentCachedEdge 3164)=independentCachedBranchMembers201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound201
def independentCachedBranchMembers203 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,1776,2618,2652,2662,2668,2702,2710,2732,2740,2762,2776,2800,3102,3118,3178,3186,3192,3226,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers203 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers203 6 (fun x => (if x<2740 then (if x<1776 then (if x<1692 then (if x<1614 then 0 else (if x<1652 then 0 else 0)) else (if x<1746 then (if x<1702 then 0 else 0) else (if x<1768 then 0 else 0))) else (if x<2668 then (if x<2652 then (if x<2618 then 1 else 2) else (if x<2662 then 2 else 2)) else (if x<2710 then (if x<2702 then 3 else 1) else (if x<2732 then 2 else 2)))) else (if x<3186 then (if x<2800 then (if x<2762 then 1 else (if x<2776 then 2 else 1)) else (if x<3118 then (if x<3102 then 2 else 4) else (if x<3178 then 3 else 4))) else (if x<3256 then (if x<3226 then (if x<3192 then 5 else 3) else (if x<3250 then 3 else 4)) else (if x<3276 then (if x<3270 then 5 else 4) else (if x<3284 then 3 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers204 : Finset ℕ := ([1692,1702,1746,1768,2618,2652,2662,2710,2732,2762,2776,2800,3118,3186,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers204 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers204 5 (fun x => (if x<2732 then (if x<2618 then (if x<1746 then (if x<1702 then 0 else 0) else (if x<1768 then 0 else 0)) else (if x<2662 then (if x<2652 then 1 else 1) else (if x<2710 then 1 else 0))) else (if x<3118 then (if x<2776 then (if x<2762 then 0 else 1) else (if x<2800 then 0 else 1)) else (if x<3256 then (if x<3186 then 2 else 2) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers205 : Finset ℕ := ([1594,1614,1652,1686,1692,1702,1746,1768,1776,2618,2652,2662,2668,2702,2710,2732,2740,2762,2776,2800,3102,3118,3178,3186,3192,3226,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers205 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers205 1686 5
  · have he : independentCachedBranchMembers205.erase 1686=independentCachedBranchMembers203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound203
  · have he : independentCachedBranchMembers205.filter (independentCachedEdge 1686)=independentCachedBranchMembers204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound204
def independentCachedBranchMembers206 : Finset ℕ := ([1594,1614,1686,1702,1746,2618,2662,2702,2710,2762,3102,3118,3178,3186,3226,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers206 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers206 5 (fun x => (if x<2710 then (if x<1746 then (if x<1686 then (if x<1614 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<2662 then (if x<2618 then 1 else 2) else (if x<2702 then 2 else 2))) else (if x<3178 then (if x<3102 then (if x<2762 then 1 else 3) else (if x<3118 then 0 else 2)) else (if x<3226 then (if x<3186 then 0 else 2) else (if x<3250 then 2 else (if x<3270 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers207 : Finset ℕ := ([252,1594,1614,1652,1686,1692,1702,1746,1768,1776,2618,2652,2662,2668,2702,2710,2732,2740,2762,2776,2800,3102,3118,3178,3186,3192,3226,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers207 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers207 252 5
  · have he : independentCachedBranchMembers207.erase 252=independentCachedBranchMembers205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound205
  · have he : independentCachedBranchMembers207.filter (independentCachedEdge 252)=independentCachedBranchMembers206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound206
def independentCachedBranchMembers208 : Finset ℕ := ([1594,1652,1692,1746,1776,2618,2662,2702,2732,2800,3102,3118,3186,3226,3256,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers208 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers208 5 (fun x => (if x<2732 then (if x<1776 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2662 then (if x<2618 then 1 else 2) else (if x<2702 then 2 else 1))) else (if x<3186 then (if x<3102 then (if x<2800 then 2 else 2) else (if x<3118 then 1 else 2)) else (if x<3256 then (if x<3226 then 0 else 0) else (if x<3270 then 2 else (if x<3284 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers209 : Finset ℕ := ([72,252,1594,1614,1652,1686,1692,1702,1746,1768,1776,2618,2652,2662,2668,2702,2710,2732,2740,2762,2776,2800,3102,3118,3178,3186,3192,3226,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers209 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers209 72 5
  · have he : independentCachedBranchMembers209.erase 72=independentCachedBranchMembers207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound207
  · have he : independentCachedBranchMembers209.filter (independentCachedEdge 72)=independentCachedBranchMembers208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound208
def independentCachedBranchMembers210 : Finset ℕ := ([72,252,1614,1652,1686,1692,1702,1776,2618,2652,2662,2668,2702,2740,2776,3178,3250,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers210 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers210 5 (fun x => (if x<2652 then (if x<1686 then (if x<1614 then (if x<252 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1702 then (if x<1692 then 1 else 2) else (if x<1776 then 2 else (if x<2618 then 2 else 3)))) else (if x<2776 then (if x<2668 then (if x<2662 then 0 else 3) else (if x<2702 then 1 else (if x<2740 then 1 else 0))) else (if x<3250 then (if x<3178 then 2 else 3) else (if x<3256 then 4 else (if x<3284 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers211 : Finset ℕ := ([72,252,1594,1614,1652,1678,1686,1692,1702,1746,1768,1776,2618,2652,2662,2668,2702,2710,2732,2740,2762,2776,2800,3102,3118,3178,3186,3192,3226,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers211 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers211 1678 5
  · have he : independentCachedBranchMembers211.erase 1678=independentCachedBranchMembers209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound209
  · have he : independentCachedBranchMembers211.filter (independentCachedEdge 1678)=independentCachedBranchMembers210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound210
def independentCachedBranchMembers212 : Finset ℕ := ([1614,1652,1692,1702,2618,2652,2662,2702,2710,2732,2740,2762,2800,3118,3178,3186,3226,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers212 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers212 5 (fun x => (if x<2732 then (if x<2618 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1702 then 0 else 0)) else (if x<2662 then (if x<2652 then 1 else 0) else (if x<2702 then 0 else (if x<2710 then 0 else 1)))) else (if x<3178 then (if x<2762 then (if x<2740 then 1 else 0) else (if x<2800 then 1 else (if x<3118 then 1 else 2))) else (if x<3226 then (if x<3186 then 3 else 2) else (if x<3256 then 2 else (if x<3270 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers213 : Finset ℕ := ([72,252,1594,1614,1628,1652,1678,1686,1692,1702,1746,1768,1776,2618,2652,2662,2668,2702,2710,2732,2740,2762,2776,2800,3102,3118,3178,3186,3192,3226,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers213 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers213 1628 5
  · have he : independentCachedBranchMembers213.erase 1628=independentCachedBranchMembers211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound211
  · have he : independentCachedBranchMembers213.filter (independentCachedEdge 1628)=independentCachedBranchMembers212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound212
def independentCachedBranchMembers214 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,1776,2652,2662,2702,2710,2732,2740,2776,3118,3192,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers214 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers214 5 (fun x => (if x<2662 then (if x<1702 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1692 then 0 else 0)) else (if x<1768 then (if x<1746 then 0 else 0) else (if x<1776 then 0 else (if x<2652 then 1 else 2)))) else (if x<2776 then (if x<2710 then (if x<2702 then 2 else 1) else (if x<2732 then 2 else (if x<2740 then 2 else 1))) else (if x<3192 then (if x<3118 then 1 else 3) else (if x<3250 then 3 else (if x<3270 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers215 : Finset ℕ := ([1594,1652,1692,1746,1776,2662,2702,2732,3118,3270] : List ℕ).toFinset
theorem independentCachedBranchBound215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers215 4 (fun x => (if x<2662 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1746 then 0 else (if x<1776 then 0 else 1))) else (if x<2732 then (if x<2702 then 2 else 1) else (if x<3118 then 2 else (if x<3270 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers216 : Finset ℕ := ([72,1594,1614,1652,1692,1702,1746,1768,1776,2652,2662,2702,2710,2732,2740,2776,3118,3192,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers216 72 4
  · have he : independentCachedBranchMembers216.erase 72=independentCachedBranchMembers214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound214
  · have he : independentCachedBranchMembers216.filter (independentCachedEdge 72)=independentCachedBranchMembers215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound215
def independentCachedBranchMembers217 : Finset ℕ := ([72,252,1594,1614,1628,1652,1678,1686,1692,1702,1746,1768,1776,2618,2652,2662,2668,2702,2710,2716,2732,2740,2762,2776,2800,3102,3118,3178,3186,3192,3226,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers217 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers217 2716 5
  · have he : independentCachedBranchMembers217.erase 2716=independentCachedBranchMembers213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound213
  · have he : independentCachedBranchMembers217.filter (independentCachedEdge 2716)=independentCachedBranchMembers216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound216
def independentCachedBranchMembers218 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2652,2662,2668,2702,2740,2762,2800,3186,3192,3226,3284] : List ℕ).toFinset
theorem independentCachedBranchBound218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers218 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers218 5 (fun x => (if x<2668 then (if x<1702 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1692 then 0 else 0)) else (if x<1768 then (if x<1746 then 0 else 0) else (if x<2652 then 0 else (if x<2662 then 1 else 1)))) else (if x<2800 then (if x<2740 then (if x<2702 then 2 else 1) else (if x<2762 then 1 else 2)) else (if x<3192 then (if x<3186 then 2 else 3) else (if x<3226 then 4 else (if x<3284 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers219 : Finset ℕ := ([1692,1702,1746,1768,2652,2662,2762,2800,3186] : List ℕ).toFinset
theorem independentCachedBranchBound219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers219 4 (fun x => (if x<2652 then (if x<1746 then (if x<1702 then 0 else 0) else (if x<1768 then 0 else 0)) else (if x<2762 then (if x<2662 then 1 else 1) else (if x<2800 then 1 else (if x<3186 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers220 : Finset ℕ := ([1594,1614,1652,1686,1692,1702,1746,1768,2652,2662,2668,2702,2740,2762,2800,3186,3192,3226,3284] : List ℕ).toFinset
theorem independentCachedBranchBound220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers220 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers220 1686 4
  · have he : independentCachedBranchMembers220.erase 1686=independentCachedBranchMembers218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound218
  · have he : independentCachedBranchMembers220.filter (independentCachedEdge 1686)=independentCachedBranchMembers219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound219
def independentCachedBranchMembers221 : Finset ℕ := ([1594,1614,1686,1702,1746,2662,2702,2762,3186,3226] : List ℕ).toFinset
theorem independentCachedBranchBound221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers221 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers221 4 (fun x => (if x<2662 then (if x<1686 then (if x<1614 then 0 else 0) else (if x<1702 then 0 else (if x<1746 then 1 else 1))) else (if x<2762 then (if x<2702 then 2 else 2) else (if x<3186 then 3 else (if x<3226 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers222 : Finset ℕ := ([252,1594,1614,1652,1686,1692,1702,1746,1768,2652,2662,2668,2702,2740,2762,2800,3186,3192,3226,3284] : List ℕ).toFinset
theorem independentCachedBranchBound222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers222 252 4
  · have he : independentCachedBranchMembers222.erase 252=independentCachedBranchMembers220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound220
  · have he : independentCachedBranchMembers222.filter (independentCachedEdge 252)=independentCachedBranchMembers221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound221
def independentCachedBranchMembers223 : Finset ℕ := ([72,252,1594,1614,1628,1652,1678,1686,1692,1702,1746,1768,1776,2618,2638,2652,2662,2668,2702,2710,2716,2732,2740,2762,2776,2800,3102,3118,3178,3186,3192,3226,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers223 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers223 2638 5
  · have he : independentCachedBranchMembers223.erase 2638=independentCachedBranchMembers217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound217
  · have he : independentCachedBranchMembers223.filter (independentCachedEdge 2638)=independentCachedBranchMembers222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound222
def independentCachedBranchMembers224 : Finset ℕ := ([1594,1614,1652,1678,1692,1702,1746,1768,2668,2710,2732,2762,2776,2800,3118,3186,3226,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers224 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers224 5 (fun x => (if x<2732 then (if x<1702 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1678 then 0 else (if x<1692 then 1 else 0))) else (if x<1768 then (if x<1746 then 0 else 0) else (if x<2668 then 0 else (if x<2710 then 2 else 1)))) else (if x<3186 then (if x<2776 then (if x<2762 then 1 else 1) else (if x<2800 then 2 else (if x<3118 then 1 else 2))) else (if x<3250 then (if x<3226 then 3 else 2) else (if x<3270 then 4 else (if x<3284 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers225 : Finset ℕ := ([1614,1652,1692,1702,2710,2732,2762,2800,3118,3186,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers225 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers225 4 (fun x => (if x<2762 then (if x<1702 then (if x<1652 then 0 else (if x<1692 then 0 else 0)) else (if x<2710 then 0 else (if x<2732 then 1 else 1))) else (if x<3186 then (if x<2800 then 1 else (if x<3118 then 1 else 2)) else (if x<3226 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers226 : Finset ℕ := ([1594,1614,1628,1652,1678,1692,1702,1746,1768,2668,2710,2732,2762,2776,2800,3118,3186,3226,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers226 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers226 1628 4
  · have he : independentCachedBranchMembers226.erase 1628=independentCachedBranchMembers224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound224
  · have he : independentCachedBranchMembers226.filter (independentCachedEdge 1628)=independentCachedBranchMembers225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound225
def independentCachedBranchMembers227 : Finset ℕ := ([72,252,1594,1614,1628,1652,1678,1686,1692,1702,1746,1768,1776,2618,2638,2652,2662,2668,2702,2710,2716,2732,2740,2762,2776,2792,2800,3102,3118,3178,3186,3192,3226,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers227 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers227 2792 5
  · have he : independentCachedBranchMembers227.erase 2792=independentCachedBranchMembers223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound223
  · have he : independentCachedBranchMembers227.filter (independentCachedEdge 2792)=independentCachedBranchMembers226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound226
def independentCachedBranchMembers228 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3130,3158,3164,3178,3180,3186,3188,3192,3214,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers228 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers228 3130 6
  · have he : independentCachedBranchMembers228.erase 3130=independentCachedBranchMembers202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound202
  · have he : independentCachedBranchMembers228.filter (independentCachedEdge 3130)=independentCachedBranchMembers227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound227
def independentCachedBranchMembers229 : Finset ℕ := ([1642,1652,1686,1702,1720,1740,1776,2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3118,3158,3192,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers229 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers229 6 (fun x => (if x<2732 then (if x<2614 then (if x<1702 then (if x<1652 then 0 else (if x<1686 then 0 else 1)) else (if x<1740 then (if x<1720 then 0 else 0) else (if x<1776 then 0 else 1))) else (if x<2668 then (if x<2638 then (if x<2618 then 2 else 3) else (if x<2652 then 2 else 3)) else (if x<2702 then (if x<2674 then 4 else 4) else (if x<2716 then 1 else 2)))) else (if x<2792 then (if x<2762 then (if x<2738 then 3 else (if x<2758 then 1 else 4)) else (if x<2776 then (if x<2772 then 3 else 1) else (if x<2788 then 4 else 2))) else (if x<3226 then (if x<3158 then (if x<3118 then 1 else 5) else (if x<3192 then 5 else 4)) else (if x<3276 then (if x<3252 then 5 else 2) else (if x<3298 then 2 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers230 : Finset ℕ := ([1642,1702,2614,2668,2702,2716,2738,2758,2772,2792,3118,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers230 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers230 5 (fun x => (if x<2738 then (if x<2668 then (if x<1702 then 0 else (if x<2614 then 0 else 1)) else (if x<2702 then 1 else (if x<2716 then 1 else 2))) else (if x<2792 then (if x<2758 then 2 else (if x<2772 then 2 else 1)) else (if x<3276 then (if x<3118 then 2 else 0) else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers231 : Finset ℕ := ([1626,1642,1652,1686,1702,1720,1740,1776,2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3118,3158,3192,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers231 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers231 1626 5
  · have he : independentCachedBranchMembers231.erase 1626=independentCachedBranchMembers229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound229
  · have he : independentCachedBranchMembers231.filter (independentCachedEdge 1626)=independentCachedBranchMembers230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound230
def independentCachedBranchMembers232 : Finset ℕ := ([1652,1720,2638,2674,2702,2738,2772,2776,2788,2792,3158,3226,3276] : List ℕ).toFinset
theorem independentCachedBranchBound232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers232 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers232 5 (fun x => (if x<2772 then (if x<2674 then (if x<1720 then 0 else (if x<2638 then 0 else 1)) else (if x<2702 then 1 else (if x<2738 then 2 else 2))) else (if x<2792 then (if x<2776 then 1 else (if x<2788 then 2 else 2)) else (if x<3226 then (if x<3158 then 1 else 0) else (if x<3276 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers233 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1740,1776,2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3118,3158,3192,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers233 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers233 1596 5
  · have he : independentCachedBranchMembers233.erase 1596=independentCachedBranchMembers231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound231
  · have he : independentCachedBranchMembers233.filter (independentCachedEdge 1596)=independentCachedBranchMembers232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound232
def independentCachedBranchMembers234 : Finset ℕ := ([1642,1652,1702,1720,1740,2668,2674,2732,2738,2758,2762,2772,2776,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers234 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers234 5 (fun x => (if x<2738 then (if x<1740 then (if x<1702 then (if x<1652 then 0 else 0) else (if x<1720 then 0 else 0)) else (if x<2674 then (if x<2668 then 0 else 1) else (if x<2732 then 1 else 2))) else (if x<2776 then (if x<2762 then (if x<2758 then 2 else 1) else (if x<2772 then 2 else 2)) else (if x<3158 then (if x<3118 then 1 else 3) else (if x<3226 then 3 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers235 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1740,1776,2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3102,3118,3158,3192,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers235 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers235 3102 5
  · have he : independentCachedBranchMembers235.erase 3102=independentCachedBranchMembers233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound233
  · have he : independentCachedBranchMembers235.filter (independentCachedEdge 3102)=independentCachedBranchMembers234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound234
def independentCachedBranchMembers236 : Finset ℕ := ([1626,1642,1652,1686,1702,1720,1740,2614,2652,2668,2674,2702,2762,2772,2788,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers236 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers236 5 (fun x => (if x<2668 then (if x<1702 then (if x<1652 then (if x<1642 then 0 else 1) else (if x<1686 then 0 else 0)) else (if x<1740 then (if x<1720 then 1 else 0) else (if x<2614 then 0 else (if x<2652 then 2 else 2)))) else (if x<2788 then (if x<2702 then (if x<2674 then 3 else 3) else (if x<2762 then 2 else (if x<2772 then 3 else 3))) else (if x<3192 then (if x<3158 then 2 else 4) else (if x<3226 then 1 else (if x<3252 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers237 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1740,1776,2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3102,3118,3158,3192,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers237 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers237 3256 5
  · have he : independentCachedBranchMembers237.erase 3256=independentCachedBranchMembers235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound235
  · have he : independentCachedBranchMembers237.filter (independentCachedEdge 3256)=independentCachedBranchMembers236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound236
def independentCachedBranchMembers238 : Finset ℕ := ([1596,1642,1652,1702,1720,1740,1776,2618,2638,2668,2674,2716,2762,2772,2792,3118,3192,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers238 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers238 5 (fun x => (if x<2668 then (if x<1720 then (if x<1652 then (if x<1642 then 0 else 0) else (if x<1702 then 1 else 0)) else (if x<1776 then (if x<1740 then 1 else 0) else (if x<2618 then 0 else (if x<2638 then 2 else 2)))) else (if x<2792 then (if x<2716 then (if x<2674 then 3 else 3) else (if x<2762 then 2 else (if x<2772 then 3 else 3))) else (if x<3192 then (if x<3118 then 2 else 4) else (if x<3252 then 1 else (if x<3298 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers239 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1740,1776,2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3102,3118,3158,3192,3226,3238,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers239 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers239 3238 5
  · have he : independentCachedBranchMembers239.erase 3238=independentCachedBranchMembers237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound237
  · have he : independentCachedBranchMembers239.filter (independentCachedEdge 3238)=independentCachedBranchMembers238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound238
def independentCachedBranchMembers240 : Finset ℕ := ([1626,1642,1652,1686,1702,1720,1740,2618,2638,2716,2732,2738,2758,2776,2792,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers240 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers240 5 (fun x => (if x<2716 then (if x<1702 then (if x<1652 then (if x<1642 then 0 else 1) else (if x<1686 then 0 else 0)) else (if x<1740 then (if x<1720 then 1 else 0) else (if x<2618 then 0 else (if x<2638 then 2 else 2)))) else (if x<2792 then (if x<2738 then (if x<2732 then 2 else 3) else (if x<2758 then 3 else (if x<2776 then 3 else 3))) else (if x<3192 then (if x<3158 then 2 else 4) else (if x<3226 then 1 else (if x<3252 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers241 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1740,1776,2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3102,3118,3158,3188,3192,3226,3238,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers241 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers241 3188 5
  · have he : independentCachedBranchMembers241.erase 3188=independentCachedBranchMembers239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound239
  · have he : independentCachedBranchMembers241.filter (independentCachedEdge 3188)=independentCachedBranchMembers240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound240
def independentCachedBranchMembers242 : Finset ℕ := ([1596,1642,1652,1702,1720,1740,1776,2614,2652,2702,2732,2738,2758,2776,2788,3118,3192,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers242 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers242 5 (fun x => (if x<2702 then (if x<1720 then (if x<1652 then (if x<1642 then 0 else 0) else (if x<1702 then 1 else 0)) else (if x<1776 then (if x<1740 then 1 else 0) else (if x<2614 then 0 else (if x<2652 then 2 else 2)))) else (if x<2788 then (if x<2738 then (if x<2732 then 2 else 3) else (if x<2758 then 3 else (if x<2776 then 3 else 3))) else (if x<3192 then (if x<3118 then 2 else 4) else (if x<3252 then 1 else (if x<3298 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers243 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1740,1776,2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3226,3238,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers243 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers243 3178 5
  · have he : independentCachedBranchMembers243.erase 3178=independentCachedBranchMembers241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound241
  · have he : independentCachedBranchMembers243.filter (independentCachedEdge 3178)=independentCachedBranchMembers242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound242
def independentCachedBranchMembers244 : Finset ℕ := ([1596,1626,1686,1776,2614,2618,2638,2652,2702,2716,2788,2792,3102,3178,3188,3192,3238,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers244 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers244 5 (fun x => (if x<2788 then (if x<2618 then (if x<1686 then (if x<1626 then 0 else 0) else (if x<1776 then 0 else (if x<2614 then 0 else 1))) else (if x<2652 then (if x<2638 then 2 else 1) else (if x<2702 then 2 else (if x<2716 then 2 else 1)))) else (if x<3192 then (if x<3102 then (if x<2792 then 1 else 2) else (if x<3178 then 0 else (if x<3188 then 3 else 3))) else (if x<3252 then (if x<3238 then 0 else 3) else (if x<3256 then 0 else (if x<3276 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers245 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1740,1746,1776,2614,2618,2638,2652,2668,2674,2702,2716,2732,2738,2758,2762,2772,2776,2788,2792,3102,3118,3158,3178,3188,3192,3226,3238,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers245 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers245 1746 5
  · have he : independentCachedBranchMembers245.erase 1746=independentCachedBranchMembers243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound243
  · have he : independentCachedBranchMembers245.filter (independentCachedEdge 1746)=independentCachedBranchMembers244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound244
def independentCachedBranchMembers246 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2788,2792,2800,3102,3118,3130,3158,3164,3178,3180,3186,3188,3192,3214,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers246 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers246 2764 6
  · have he : independentCachedBranchMembers246.erase 2764=independentCachedBranchMembers228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound228
  · have he : independentCachedBranchMembers246.filter (independentCachedEdge 2764)=independentCachedBranchMembers245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound245
def independentCachedBranchMembers247 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2620,2680,2710,2716,2730,2738,2762,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers247 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers247 6 (fun x => (if x<2762 then (if x<1764 then (if x<1678 then (if x<1628 then 0 else (if x<1642 then 0 else 0)) else (if x<1720 then 0 else (if x<1746 then 0 else 0))) else (if x<2710 then (if x<2620 then 0 else (if x<2680 then 1 else 2)) else (if x<2730 then (if x<2716 then 1 else 2) else (if x<2738 then 1 else 2)))) else (if x<3238 then (if x<3130 then (if x<2788 then 2 else (if x<3102 then 1 else 3)) else (if x<3188 then (if x<3180 then 4 else 3) else (if x<3226 then 4 else 5))) else (if x<3270 then (if x<3244 then 3 else (if x<3252 then 4 else 5)) else (if x<3298 then (if x<3284 then 5 else 3) else (if x<3304 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers248 : Finset ℕ := ([1642,1720,1746,2620,2680,2710,2730,3130,3180,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers248 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers248 5 (fun x => (if x<2730 then (if x<2620 then (if x<1720 then 0 else (if x<1746 then 0 else 0)) else (if x<2680 then 1 else (if x<2710 then 2 else 1))) else (if x<3244 then (if x<3130 then 1 else (if x<3180 then 2 else 2)) else (if x<3284 then (if x<3270 then 3 else 3) else (if x<3304 then 4 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers249 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2620,2680,2710,2716,2730,2738,2762,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers249 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers249 3276 5
  · have he : independentCachedBranchMembers249.erase 3276=independentCachedBranchMembers247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound247
  · have he : independentCachedBranchMembers249.filter (independentCachedEdge 3276)=independentCachedBranchMembers248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound248
def independentCachedBranchMembers250 : Finset ℕ := ([1590,1746,1764,2738,2762,3130,3188,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers250 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers250 5 (fun x => (if x<3188 then (if x<2738 then (if x<1746 then 0 else (if x<1764 then 0 else 0)) else (if x<2762 then 1 else (if x<3130 then 1 else 2))) else (if x<3244 then (if x<3226 then 2 else (if x<3238 then 1 else 2)) else (if x<3298 then (if x<3284 then 3 else 3) else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers251 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2620,2638,2680,2710,2716,2730,2738,2762,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers251 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers251 2638 5
  · have he : independentCachedBranchMembers251.erase 2638=independentCachedBranchMembers249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound249
  · have he : independentCachedBranchMembers251.filter (independentCachedEdge 2638)=independentCachedBranchMembers250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound250
def independentCachedBranchMembers252 : Finset ℕ := ([1642,1678,1764,2680,2716,2762,3102,3130,3180,3188,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers252 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers252 5 (fun x => (if x<3130 then (if x<2680 then (if x<1678 then 0 else (if x<1764 then 0 else 0)) else (if x<2762 then (if x<2716 then 1 else 1) else (if x<3102 then 1 else 2))) else (if x<3244 then (if x<3180 then 3 else (if x<3188 then 2 else 3)) else (if x<3270 then (if x<3252 then 3 else 2) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers253 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2620,2638,2680,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers253 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers253 2776 5
  · have he : independentCachedBranchMembers253.erase 2776=independentCachedBranchMembers251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound251
  · have he : independentCachedBranchMembers253.filter (independentCachedEdge 2776)=independentCachedBranchMembers252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound252
def independentCachedBranchMembers254 : Finset ℕ := ([1628,1720,1764,2680,2716,2738,3102,3180,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers254 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers254 5 (fun x => (if x<3180 then (if x<2680 then (if x<1720 then 0 else (if x<1764 then 0 else 0)) else (if x<2738 then (if x<2716 then 1 else 1) else (if x<3102 then 1 else 2))) else (if x<3252 then (if x<3226 then 2 else (if x<3238 then 3 else 2)) else (if x<3284 then (if x<3270 then 3 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers255 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2620,2638,2674,2680,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers255 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers255 2674 5
  · have he : independentCachedBranchMembers255.erase 2674=independentCachedBranchMembers253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound253
  · have he : independentCachedBranchMembers255.filter (independentCachedEdge 2674)=independentCachedBranchMembers254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound254
end EntropyDesigns.QuadraticRefinement
