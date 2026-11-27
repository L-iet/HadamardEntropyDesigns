/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch24
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3200 : Finset ℕ := ([48,130,1594,1628,1650,1702,1708,1738,2614,2620,2650,2702,2730,2764,2786,3132,3162,3188,3214,3242,3270,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3200 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3200 3214 4
  · have he : independentCachedBranchMembers3200.erase 3214=independentCachedBranchMembers3198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3198
  · have he : independentCachedBranchMembers3200.filter (independentCachedEdge 3214)=independentCachedBranchMembers3199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3199
def independentCachedBranchMembers3201 : Finset ℕ := ([1628,1650,1708,2620,2702,2764,2786,3162,3188,3242,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3201 4 (fun x => (if x<2764 then (if x<1708 then (if x<1650 then 0 else 0) else (if x<2620 then 1 else (if x<2702 then 1 else 1))) else (if x<3188 then (if x<2786 then 0 else (if x<3162 then 0 else 2)) else (if x<3242 then 2 else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3202 : Finset ℕ := ([48,130,1594,1628,1650,1702,1708,1738,2614,2620,2650,2702,2730,2758,2764,2786,3132,3162,3188,3214,3242,3270,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3202 2758 4
  · have he : independentCachedBranchMembers3202.erase 2758=independentCachedBranchMembers3200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3200
  · have he : independentCachedBranchMembers3202.filter (independentCachedEdge 2758)=independentCachedBranchMembers3201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3201
def independentCachedBranchMembers3203 : Finset ℕ := ([48,80,130,132,1594,1626,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3203 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3203 1626 5
  · have he : independentCachedBranchMembers3203.erase 1626=independentCachedBranchMembers3197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3197
  · have he : independentCachedBranchMembers3203.filter (independentCachedEdge 1626)=independentCachedBranchMembers3202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3202
def independentCachedBranchMembers3204 : Finset ℕ := ([80,132,1594,1628,1652,1708,1734,1738,2620,2646,2650,2674,2702,2730,2764,2788,3132,3158,3162,3186,3214,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3204 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3204 5 (fun x => (if x<2702 then (if x<1734 then (if x<1628 then (if x<132 then 0 else (if x<1594 then 0 else 1)) else (if x<1652 then 1 else (if x<1708 then 2 else 0))) else (if x<2646 then (if x<1738 then 2 else (if x<2620 then 1 else 1)) else (if x<2650 then 2 else (if x<2674 then 0 else 3)))) else (if x<3162 then (if x<2788 then (if x<2730 then 0 else (if x<2764 then 1 else 1)) else (if x<3132 then 2 else (if x<3158 then 4 else 3))) else (if x<3238 then (if x<3186 then 4 else (if x<3214 then 0 else 3)) else (if x<3242 then 0 else (if x<3276 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3205 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3205 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3205 1596 5
  · have he : independentCachedBranchMembers3205.erase 1596=independentCachedBranchMembers3203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3203
  · have he : independentCachedBranchMembers3205.filter (independentCachedEdge 1596)=independentCachedBranchMembers3204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3204
def independentCachedBranchMembers3206 : Finset ℕ := ([48,80,130,1596,1628,1650,1678,1738,2614,2620,2646,2652,2674,2680,2702,2730,2762,2788,3102,3130,3162,3188,3238,3244,3270,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3206 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3206 5 (fun x => (if x<2680 then (if x<1678 then (if x<1596 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1628 then 0 else (if x<1650 then 1 else 1))) else (if x<2620 then (if x<1738 then 0 else (if x<2614 then 2 else 2)) else (if x<2652 then (if x<2646 then 3 else 1) else (if x<2674 then 4 else 3)))) else (if x<3162 then (if x<2762 then (if x<2702 then 0 else (if x<2730 then 2 else 3)) else (if x<3102 then (if x<2788 then 0 else 3) else (if x<3130 then 4 else 3))) else (if x<3244 then (if x<3188 then 1 else (if x<3238 then 0 else 4)) else (if x<3276 then (if x<3270 then 3 else 0) else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3207 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3207 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3207 3300 5
  · have he : independentCachedBranchMembers3207.erase 3300=independentCachedBranchMembers3205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3205
  · have he : independentCachedBranchMembers3207.filter (independentCachedEdge 3300)=independentCachedBranchMembers3206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3206
def independentCachedBranchMembers3208 : Finset ℕ := ([80,130,132,1626,1628,1678,1708,1734,2614,2650,2652,2680,2702,2730,2732,2758,2786,2788,3102,3130,3132,3158,3186,3188,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3208 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3208 5 (fun x => (if x<2730 then (if x<1708 then (if x<1626 then (if x<130 then 0 else (if x<132 then 0 else 1)) else (if x<1628 then 1 else (if x<1678 then 0 else 0))) else (if x<2650 then (if x<1734 then 2 else (if x<2614 then 1 else 3)) else (if x<2680 then (if x<2652 then 2 else 3) else (if x<2702 then 0 else 2)))) else (if x<3132 then (if x<2786 then (if x<2732 then 0 else (if x<2758 then 3 else 3)) else (if x<3102 then (if x<2788 then 4 else 1) else (if x<3130 then 4 else 1))) else (if x<3188 then (if x<3158 then 3 else (if x<3186 then 3 else 2)) else (if x<3274 then (if x<3238 then 0 else 0) else (if x<3276 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3209 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3209 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3209 3126 5
  · have he : independentCachedBranchMembers3209.erase 3126=independentCachedBranchMembers3207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3207
  · have he : independentCachedBranchMembers3209.filter (independentCachedEdge 3126)=independentCachedBranchMembers3208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3208
def independentCachedBranchMembers3210 : Finset ℕ := ([80,130,1594,1628,1652,1678,1702,1708,1738,1768,2614,2620,2650,2674,2680,2730,2758,2764,2788,3130,3158,3188,3214,3238,3244,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3210 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3210 5 (fun x => (if x<2674 then (if x<1702 then (if x<1628 then (if x<130 then 0 else (if x<1594 then 0 else 1)) else (if x<1652 then 0 else (if x<1678 then 1 else 0))) else (if x<1768 then (if x<1708 then 1 else (if x<1738 then 2 else 2)) else (if x<2620 then (if x<2614 then 1 else 1) else (if x<2650 then 2 else 2)))) else (if x<3158 then (if x<2758 then (if x<2680 then 3 else (if x<2730 then 0 else 0)) else (if x<2788 then (if x<2764 then 3 else 2) else (if x<3130 then 1 else 3))) else (if x<3238 then (if x<3188 then 3 else (if x<3214 then 0 else 3)) else (if x<3274 then (if x<3244 then 0 else 4) else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3211 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1708,1734,1738,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3211 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3211 2618 5
  · have he : independentCachedBranchMembers3211.erase 2618=independentCachedBranchMembers3209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3209
  · have he : independentCachedBranchMembers3211.filter (independentCachedEdge 2618)=independentCachedBranchMembers3210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3210
def independentCachedBranchMembers3212 : Finset ℕ := ([80,130,1594,1628,1650,1708,1734,1738,1768,2680,2730,2786,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3212 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3212 5 (fun x => (if x<2730 then (if x<1708 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else (if x<1650 then 0 else 2))) else (if x<1738 then (if x<1734 then 1 else 2) else (if x<1768 then 1 else (if x<2680 then 2 else 0)))) else (if x<3188 then (if x<3132 then (if x<2786 then 0 else 2) else (if x<3158 then 1 else (if x<3162 then 3 else 1))) else (if x<3242 then (if x<3192 then 0 else (if x<3238 then 3 else 0)) else (if x<3276 then 1 else (if x<3298 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3213 : Finset ℕ := ([130,1734,1768,2680,3132,3162,3188,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3213 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3213 4 (fun x => (if x<3162 then (if x<1768 then (if x<1734 then 0 else 0) else (if x<2680 then 1 else (if x<3132 then 0 else 0))) else (if x<3242 then (if x<3188 then 2 else 2) else (if x<3276 then 1 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3214 : Finset ℕ := ([80,130,1594,1628,1650,1708,1734,1738,1768,2650,2680,2730,2786,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3214 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3214 2650 4
  · have he : independentCachedBranchMembers3214.erase 2650=independentCachedBranchMembers3212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3212
  · have he : independentCachedBranchMembers3214.filter (independentCachedEdge 2650)=independentCachedBranchMembers3213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3213
def independentCachedBranchMembers3215 : Finset ℕ := ([80,130,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3215 4 (fun x => (if x<3188 then (if x<3132 then (if x<130 then 0 else 0) else (if x<3158 then 1 else (if x<3162 then 1 else 2))) else (if x<3242 then (if x<3192 then 0 else (if x<3238 then 3 else 0)) else (if x<3276 then 2 else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3216 : Finset ℕ := ([80,130,1594,1628,1650,1708,1734,1738,1768,2650,2680,2730,2764,2786,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3216 2764 4
  · have he : independentCachedBranchMembers3216.erase 2764=independentCachedBranchMembers3214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3214
  · have he : independentCachedBranchMembers3216.filter (independentCachedEdge 2764)=independentCachedBranchMembers3215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3215
def independentCachedBranchMembers3217 : Finset ℕ := ([130,1594,1738,2650,2730,3132,3158,3192,3238,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3217 4 (fun x => (if x<3132 then (if x<1738 then (if x<1594 then 0 else 1) else (if x<2650 then 0 else (if x<2730 then 1 else 0))) else (if x<3238 then (if x<3158 then 2 else (if x<3192 then 2 else 1)) else (if x<3276 then 2 else (if x<3298 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3218 : Finset ℕ := ([80,130,1594,1628,1650,1708,1734,1738,1768,2646,2650,2680,2730,2764,2786,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3218 2646 4
  · have he : independentCachedBranchMembers3218.erase 2646=independentCachedBranchMembers3216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3216
  · have he : independentCachedBranchMembers3218.filter (independentCachedEdge 2646)=independentCachedBranchMembers3217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3217
def independentCachedBranchMembers3219 : Finset ℕ := ([80,1650,1768,2680,2786,3132,3158,3162,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3219 4 (fun x => (if x<3132 then (if x<1768 then (if x<1650 then 0 else 0) else (if x<2680 then 1 else (if x<2786 then 0 else 1))) else (if x<3238 then (if x<3158 then 2 else (if x<3162 then 2 else 0)) else (if x<3242 then 2 else (if x<3276 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3220 : Finset ℕ := ([80,130,1594,1628,1650,1708,1734,1738,1768,2620,2646,2650,2680,2730,2764,2786,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3220 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3220 2620 4
  · have he : independentCachedBranchMembers3220.erase 2620=independentCachedBranchMembers3218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3218
  · have he : independentCachedBranchMembers3220.filter (independentCachedEdge 2620)=independentCachedBranchMembers3219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3219
def independentCachedBranchMembers3221 : Finset ℕ := ([1650,1708,1734,1738,2620,2646,2650,2786,3132,3158,3162,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3221 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3221 4 (fun x => (if x<2650 then (if x<1738 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<2620 then 1 else (if x<2646 then 1 else 0))) else (if x<3158 then (if x<2786 then 1 else (if x<3132 then 0 else 2)) else (if x<3162 then 2 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3222 : Finset ℕ := ([80,130,1594,1628,1650,1678,1708,1734,1738,1768,2620,2646,2650,2680,2730,2764,2786,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3222 1678 4
  · have he : independentCachedBranchMembers3222.erase 1678=independentCachedBranchMembers3220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3220
  · have he : independentCachedBranchMembers3222.filter (independentCachedEdge 1678)=independentCachedBranchMembers3221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3221
def independentCachedBranchMembers3223 : Finset ℕ := ([80,130,1650,1708,1734,1738,2680,2730,2764,3132,3158,3162,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3223 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3223 4 (fun x => (if x<2680 then (if x<1708 then (if x<130 then 0 else (if x<1650 then 0 else 1)) else (if x<1734 then 2 else (if x<1738 then 1 else 2))) else (if x<3132 then (if x<2730 then 0 else (if x<2764 then 0 else 1)) else (if x<3162 then (if x<3158 then 2 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3224 : Finset ℕ := ([80,130,1594,1628,1650,1678,1708,1734,1738,1768,2620,2646,2650,2680,2730,2764,2786,3102,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3224 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3224 3102 4
  · have he : independentCachedBranchMembers3224.erase 3102=independentCachedBranchMembers3222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3222
  · have he : independentCachedBranchMembers3224.filter (independentCachedEdge 3102)=independentCachedBranchMembers3223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3223
def independentCachedBranchMembers3225 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3225 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3225 1740 5
  · have he : independentCachedBranchMembers3225.erase 1740=independentCachedBranchMembers3211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3211
  · have he : independentCachedBranchMembers3225.filter (independentCachedEdge 1740)=independentCachedBranchMembers3224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3224
def independentCachedBranchMembers3226 : Finset ℕ := ([80,130,132,1626,1628,1650,1652,1678,1702,1708,2650,2652,2674,2680,2702,2730,2732,3158,3162,3188,3192,3214,3238,3242,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3226 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3226 5 (fun x => (if x<2674 then (if x<1652 then (if x<1626 then (if x<130 then 0 else (if x<132 then 0 else 1)) else (if x<1628 then 1 else (if x<1650 then 0 else 2))) else (if x<1708 then (if x<1678 then 3 else (if x<1702 then 0 else 2)) else (if x<2650 then 3 else (if x<2652 then 2 else 4)))) else (if x<3162 then (if x<2730 then (if x<2680 then 1 else (if x<2702 then 0 else 2)) else (if x<2732 then 0 else (if x<3158 then 4 else 3))) else (if x<3214 then (if x<3188 then 4 else (if x<3192 then 0 else 1)) else (if x<3242 then (if x<3238 then 3 else 0) else (if x<3244 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3227 : Finset ℕ := ([130,1628,1650,1702,2652,2674,2730,3158,3162,3188,3192,3214,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3227 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3227 4 (fun x => (if x<2730 then (if x<1702 then (if x<1628 then 0 else (if x<1650 then 0 else 1)) else (if x<2652 then 1 else (if x<2674 then 2 else 2))) else (if x<3188 then (if x<3158 then 0 else (if x<3162 then 2 else 1)) else (if x<3214 then (if x<3192 then 0 else 2) else (if x<3244 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3228 : Finset ℕ := ([80,130,132,1626,1628,1650,1652,1678,1702,1708,2650,2652,2674,2680,2702,2730,2732,3158,3162,3186,3188,3192,3214,3238,3242,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3228 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3228 3186 4
  · have he : independentCachedBranchMembers3228.erase 3186=independentCachedBranchMembers3226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3226
  · have he : independentCachedBranchMembers3228.filter (independentCachedEdge 3186)=independentCachedBranchMembers3227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3227
def independentCachedBranchMembers3229 : Finset ℕ := ([130,132,1678,1702,2650,2652,2674,2730,2732,3158,3192,3214,3238] : List ℕ).toFinset
theorem independentCachedBranchBound3229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3229 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3229 4 (fun x => (if x<2674 then (if x<1702 then (if x<132 then 0 else (if x<1678 then 1 else 0)) else (if x<2650 then 1 else (if x<2652 then 1 else 2))) else (if x<3158 then (if x<2730 then 2 else (if x<2732 then 0 else 3)) else (if x<3214 then (if x<3192 then 2 else 1) else (if x<3238 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3230 : Finset ℕ := ([80,130,132,1626,1628,1650,1652,1678,1702,1708,2646,2650,2652,2674,2680,2702,2730,2732,3158,3162,3186,3188,3192,3214,3238,3242,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3230 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3230 2646 4
  · have he : independentCachedBranchMembers3230.erase 2646=independentCachedBranchMembers3228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3228
  · have he : independentCachedBranchMembers3230.filter (independentCachedEdge 2646)=independentCachedBranchMembers3229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3229
def independentCachedBranchMembers3231 : Finset ℕ := ([48,80,130,132,192,1594,1596,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3231 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3231 192 5
  · have he : independentCachedBranchMembers3231.erase 192=independentCachedBranchMembers3225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3225
  · have he : independentCachedBranchMembers3231.filter (independentCachedEdge 192)=independentCachedBranchMembers3230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3230
def independentCachedBranchMembers3232 : Finset ℕ := ([48,80,130,1596,1628,1652,1678,1702,1734,1738,2652,2680,2702,2730,2758,2762,3132,3188,3192,3214,3238,3242,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3232 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3232 5 (fun x => (if x<2680 then (if x<1652 then (if x<130 then (if x<80 then 0 else 1) else (if x<1596 then 0 else (if x<1628 then 0 else 1))) else (if x<1734 then (if x<1678 then 2 else (if x<1702 then 0 else 2)) else (if x<1738 then 3 else (if x<2652 then 4 else 2)))) else (if x<3188 then (if x<2758 then (if x<2702 then 0 else (if x<2730 then 2 else 1)) else (if x<2762 then 4 else (if x<3132 then 0 else 3))) else (if x<3238 then (if x<3192 then 0 else (if x<3214 then 2 else 3)) else (if x<3242 then 1 else (if x<3298 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3233 : Finset ℕ := ([80,1628,1702,1738,2652,2680,2762,3132,3188,3214,3242,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3233 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3233 4 (fun x => (if x<2762 then (if x<1738 then (if x<1628 then 0 else (if x<1702 then 0 else 1)) else (if x<2652 then 1 else (if x<2680 then 2 else 0))) else (if x<3214 then (if x<3132 then 2 else (if x<3188 then 2 else 0)) else (if x<3242 then 1 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3234 : Finset ℕ := ([48,80,130,1596,1628,1652,1678,1702,1734,1738,2652,2680,2702,2730,2758,2762,3132,3188,3192,3214,3238,3242,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3234 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3234 3274 4
  · have he : independentCachedBranchMembers3234.erase 3274=independentCachedBranchMembers3232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3232
  · have he : independentCachedBranchMembers3234.filter (independentCachedEdge 3274)=independentCachedBranchMembers3233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3233
def independentCachedBranchMembers3235 : Finset ℕ := ([48,80,1652,1678,2652,2730,2758,2762,3188,3192,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3235 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3235 4 (fun x => (if x<2758 then (if x<1678 then (if x<80 then 0 else (if x<1652 then 1 else 0)) else (if x<2652 then 1 else (if x<2730 then 2 else 1))) else (if x<3192 then (if x<2762 then 2 else (if x<3188 then 0 else 1)) else (if x<3214 then 2 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3236 : Finset ℕ := ([48,80,130,1596,1628,1652,1678,1702,1734,1738,2652,2680,2702,2730,2758,2762,2786,3132,3188,3192,3214,3238,3242,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3236 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3236 2786 4
  · have he : independentCachedBranchMembers3236.erase 2786=independentCachedBranchMembers3234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3234
  · have he : independentCachedBranchMembers3236.filter (independentCachedEdge 2786)=independentCachedBranchMembers3235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3235
def independentCachedBranchMembers3237 : Finset ℕ := ([80,1628,1652,1734,2652,2730,2758,3132,3192,3214,3238,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3237 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3237 4 (fun x => (if x<2758 then (if x<1734 then (if x<1628 then 0 else (if x<1652 then 0 else 1)) else (if x<2652 then 1 else (if x<2730 then 2 else 0))) else (if x<3214 then (if x<3132 then 2 else (if x<3192 then 1 else 2)) else (if x<3274 then (if x<3238 then 1 else 0) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3238 : Finset ℕ := ([48,80,130,1596,1628,1652,1678,1702,1734,1738,2652,2680,2702,2730,2758,2762,2786,3132,3188,3192,3214,3238,3242,3270,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3238 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3238 3270 4
  · have he : independentCachedBranchMembers3238.erase 3270=independentCachedBranchMembers3236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3236
  · have he : independentCachedBranchMembers3238.filter (independentCachedEdge 3270)=independentCachedBranchMembers3237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3237
def independentCachedBranchMembers3239 : Finset ℕ := ([80,1596,1678,1702,2652,2680,2758,2762,2786,3132,3214,3238,3242] : List ℕ).toFinset
theorem independentCachedBranchBound3239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3239 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3239 4 (fun x => (if x<2758 then (if x<1702 then (if x<1596 then 0 else (if x<1678 then 1 else 0)) else (if x<2652 then 1 else (if x<2680 then 1 else 0))) else (if x<3132 then (if x<2762 then 1 else (if x<2786 then 2 else 3)) else (if x<3238 then (if x<3214 then 2 else 2) else (if x<3242 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3240 : Finset ℕ := ([48,80,130,1596,1628,1652,1678,1702,1734,1738,2620,2652,2680,2702,2730,2758,2762,2786,3132,3188,3192,3214,3238,3242,3270,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3240 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3240 2620 4
  · have he : independentCachedBranchMembers3240.erase 2620=independentCachedBranchMembers3238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3238
  · have he : independentCachedBranchMembers3240.filter (independentCachedEdge 2620)=independentCachedBranchMembers3239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3239
def independentCachedBranchMembers3241 : Finset ℕ := ([18,48,80,130,132,192,1594,1596,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3241 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3241 18 5
  · have he : independentCachedBranchMembers3241.erase 18=independentCachedBranchMembers3231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3231
  · have he : independentCachedBranchMembers3241.filter (independentCachedEdge 18)=independentCachedBranchMembers3240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3240
def independentCachedBranchMembers3242 : Finset ℕ := ([48,80,130,1594,1626,1652,1702,1708,1734,1740,1768,2614,2652,2674,2680,2702,2730,2762,2788,3132,3158,3186,3192,3214,3242,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3242 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3242 5 (fun x => (if x<2674 then (if x<1702 then (if x<1594 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1626 then 2 else (if x<1652 then 1 else 0))) else (if x<1740 then (if x<1708 then 2 else (if x<1734 then 3 else 0)) else (if x<2614 then (if x<1768 then 4 else 2) else (if x<2652 then 2 else 1)))) else (if x<3158 then (if x<2730 then (if x<2680 then 1 else (if x<2702 then 0 else 3)) else (if x<2788 then (if x<2762 then 2 else 0) else (if x<3132 then 2 else 0))) else (if x<3214 then (if x<3186 then 1 else (if x<3192 then 3 else 1)) else (if x<3274 then (if x<3242 then 0 else 3) else (if x<3300 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3243 : Finset ℕ := ([80,1626,1708,1734,2614,2680,2702,2730,2788,3132,3158,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3243 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3243 4 (fun x => (if x<2702 then (if x<1734 then (if x<1626 then 0 else (if x<1708 then 0 else 1)) else (if x<2614 then 1 else (if x<2680 then 2 else 0))) else (if x<3132 then (if x<2730 then 1 else (if x<2788 then 2 else 1)) else (if x<3186 then (if x<3158 then 3 else 2) else (if x<3274 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3244 : Finset ℕ := ([1708,1734,2680,2730,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3244 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3244 3 (fun x => (if x<2730 then (if x<1734 then 0 else (if x<2680 then 0 else 1)) else (if x<3186 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3245 : Finset ℕ := ([80,1626,1708,1734,2614,2652,2680,2702,2730,2788,3132,3158,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3245 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3245 2652 3
  · have he : independentCachedBranchMembers3245.erase 2652=independentCachedBranchMembers3243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3243
  · have he : independentCachedBranchMembers3245.filter (independentCachedEdge 2652)=independentCachedBranchMembers3244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3244
def independentCachedBranchMembers3246 : Finset ℕ := ([1626,1708,2614,2788,3158,3186] : List ℕ).toFinset
theorem independentCachedBranchBound3246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3246 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3246 3 (fun x => (if x<2788 then (if x<1708 then 0 else (if x<2614 then 1 else 2)) else (if x<3158 then 0 else (if x<3186 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3247 : Finset ℕ := ([80,130,1626,1708,1734,2614,2652,2680,2702,2730,2788,3132,3158,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound3247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3247 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3247 130 3
  · have he : independentCachedBranchMembers3247.erase 130=independentCachedBranchMembers3245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3245
  · have he : independentCachedBranchMembers3247.filter (independentCachedEdge 130)=independentCachedBranchMembers3246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3246
def independentCachedBranchMembers3248 : Finset ℕ := ([48,80,130,1594,1626,1652,1702,1708,1734,1740,1768,2614,2652,2674,2680,2702,2730,2762,2788,3126,3132,3158,3186,3192,3214,3242,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3248 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3248 3126 4
  · have he : independentCachedBranchMembers3248.erase 3126=independentCachedBranchMembers3242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3242
  · have he : independentCachedBranchMembers3248.filter (independentCachedEdge 3126)=independentCachedBranchMembers3247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3247
def independentCachedBranchMembers3249 : Finset ℕ := ([48,130,1594,1702,1740,2614,2652,2674,2730,3132,3158,3192,3214,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3249 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3249 4 (fun x => (if x<2674 then (if x<1702 then (if x<130 then 0 else (if x<1594 then 0 else 1)) else (if x<2614 then (if x<1740 then 1 else 2) else (if x<2652 then 1 else 2))) else (if x<3192 then (if x<3132 then (if x<2730 then 2 else 1) else (if x<3158 then 0 else 3)) else (if x<3274 then (if x<3214 then 3 else 0) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3250 : Finset ℕ := ([48,80,130,1594,1626,1652,1702,1708,1734,1740,1768,2614,2646,2652,2674,2680,2702,2730,2762,2788,3126,3132,3158,3186,3192,3214,3242,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3250 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3250 2646 4
  · have he : independentCachedBranchMembers3250.erase 2646=independentCachedBranchMembers3248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3248
  · have he : independentCachedBranchMembers3250.filter (independentCachedEdge 2646)=independentCachedBranchMembers3249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3249
def independentCachedBranchMembers3251 : Finset ℕ := ([1626,1702,1740,1768,2614,2652,2680,2762,3132,3158,3186,3214,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3251 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3251 4 (fun x => (if x<2762 then (if x<1768 then (if x<1702 then 0 else (if x<1740 then 1 else 0)) else (if x<2652 then (if x<2614 then 1 else 1) else (if x<2680 then 0 else 1))) else (if x<3186 then (if x<3132 then 0 else (if x<3158 then 2 else 2)) else (if x<3242 then (if x<3214 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3252 : Finset ℕ := ([1740,1768,2614,2762,3132,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3252 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3252 3 (fun x => (if x<2762 then (if x<1768 then 0 else (if x<2614 then 1 else 0)) else (if x<3132 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3253 : Finset ℕ := ([80,1626,1702,1740,1768,2614,2652,2680,2762,3132,3158,3186,3214,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3253 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3253 80 3
  · have he : independentCachedBranchMembers3253.erase 80=independentCachedBranchMembers3251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3251
  · have he : independentCachedBranchMembers3253.filter (independentCachedEdge 80)=independentCachedBranchMembers3252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3252
def independentCachedBranchMembers3254 : Finset ℕ := ([48,80,130,1594,1626,1652,1702,1708,1734,1740,1768,2614,2620,2646,2652,2674,2680,2702,2730,2762,2788,3126,3132,3158,3186,3192,3214,3242,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3254 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3254 2620 4
  · have he : independentCachedBranchMembers3254.erase 2620=independentCachedBranchMembers3250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3250
  · have he : independentCachedBranchMembers3254.filter (independentCachedEdge 2620)=independentCachedBranchMembers3253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3253
def independentCachedBranchMembers3255 : Finset ℕ := ([18,48,80,130,132,192,1594,1596,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1764,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3255 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3255 1764 5
  · have he : independentCachedBranchMembers3255.erase 1764=independentCachedBranchMembers3241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3241
  · have he : independentCachedBranchMembers3255.filter (independentCachedEdge 1764)=independentCachedBranchMembers3254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3254
def independentCachedBranchMembers3256 : Finset ℕ := ([48,130,132,192,1626,1628,1650,1652,1708,1734,1768,2620,2646,2680,2702,2762,2764,2786,2788,3130,3132,3158,3192,3214,3238,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3256 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3256 5 (fun x => (if x<2702 then (if x<1652 then (if x<192 then (if x<130 then 0 else (if x<132 then 0 else 1)) else (if x<1628 then (if x<1626 then 2 else 1) else (if x<1650 then 3 else 3))) else (if x<1768 then (if x<1708 then 0 else (if x<1734 then 4 else 0)) else (if x<2646 then (if x<2620 then 2 else 0) else (if x<2680 then 3 else 1)))) else (if x<3158 then (if x<2786 then (if x<2762 then 0 else (if x<2764 then 2 else 3)) else (if x<3130 then (if x<2788 then 3 else 1) else (if x<3132 then 1 else 4))) else (if x<3274 then (if x<3214 then (if x<3192 then 4 else 0) else (if x<3238 then 4 else 1)) else (if x<3298 then (if x<3276 then 0 else 2) else (if x<3300 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3257 : Finset ℕ := ([1628,1652,1708,1768,2620,2680,2764,2788,3130,3158,3214,3238,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3257 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3257 4 (fun x => (if x<2788 then (if x<1768 then (if x<1652 then 0 else (if x<1708 then 1 else 0)) else (if x<2680 then (if x<2620 then 1 else 0) else (if x<2764 then 1 else 0))) else (if x<3214 then (if x<3130 then 1 else (if x<3158 then 2 else 2)) else (if x<3274 then (if x<3238 then 2 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3258 : Finset ℕ := ([1708,1768,2764,2788,3130,3158] : List ℕ).toFinset
theorem independentCachedBranchBound3258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3258 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3258 3 (fun x => (if x<2788 then (if x<1768 then 0 else (if x<2764 then 1 else 0)) else (if x<3130 then 1 else (if x<3158 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3259 : Finset ℕ := ([130,1628,1652,1708,1768,2620,2680,2764,2788,3130,3158,3214,3238,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3259 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3259 130 3
  · have he : independentCachedBranchMembers3259.erase 130=independentCachedBranchMembers3257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3257
  · have he : independentCachedBranchMembers3259.filter (independentCachedEdge 130)=independentCachedBranchMembers3258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3258
def independentCachedBranchMembers3260 : Finset ℕ := ([48,130,132,192,1626,1628,1650,1652,1708,1734,1768,2618,2620,2646,2680,2702,2762,2764,2786,2788,3130,3132,3158,3192,3214,3238,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3260 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3260 2618 4
  · have he : independentCachedBranchMembers3260.erase 2618=independentCachedBranchMembers3256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3256
  · have he : independentCachedBranchMembers3260.filter (independentCachedEdge 2618)=independentCachedBranchMembers3259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3259
def independentCachedBranchMembers3261 : Finset ℕ := ([18,48,80,130,132,192,1594,1596,1622,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1764,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3261 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3261 1622 5
  · have he : independentCachedBranchMembers3261.erase 1622=independentCachedBranchMembers3255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3255
  · have he : independentCachedBranchMembers3261.filter (independentCachedEdge 1622)=independentCachedBranchMembers3260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3260
def independentCachedBranchMembers3262 : Finset ℕ := ([48,80,130,132,1596,1626,1628,1650,1652,1678,1702,1734,1768,2620,2650,2652,2674,2702,2758,3102,3158,3192,3244,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3262 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3262 5 (fun x => (if x<2620 then (if x<1628 then (if x<132 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1596 then 1 else (if x<1626 then 0 else 1))) else (if x<1678 then (if x<1650 then 2 else (if x<1652 then 2 else 3)) else (if x<1734 then (if x<1702 then 0 else 3) else (if x<1768 then 2 else 2)))) else (if x<3102 then (if x<2674 then (if x<2650 then 4 else (if x<2652 then 4 else 3)) else (if x<2702 then 1 else (if x<2758 then 3 else 0))) else (if x<3244 then (if x<3158 then 4 else (if x<3192 then 2 else 0)) else (if x<3276 then (if x<3274 then 1 else 0) else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3263 : Finset ℕ := ([80,130,1596,1626,1650,1734,2652,2702,3158,3244,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3263 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3263 4 (fun x => (if x<2652 then (if x<1626 then (if x<130 then 0 else (if x<1596 then 0 else 1)) else (if x<1650 then 1 else (if x<1734 then 2 else 2))) else (if x<3244 then (if x<2702 then 0 else (if x<3158 then 0 else 2)) else (if x<3274 then 1 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3264 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1734,1768,2620,2650,2652,2674,2702,2758,3102,3158,3192,3244,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3264 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3264 1594 4
  · have he : independentCachedBranchMembers3264.erase 1594=independentCachedBranchMembers3262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3262
  · have he : independentCachedBranchMembers3264.filter (independentCachedEdge 1594)=independentCachedBranchMembers3263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3263
def independentCachedBranchMembers3265 : Finset ℕ := ([48,132,1596,1626,1650,1734,2620,2650,2674,2758,3158,3244,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3265 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3265 4 (fun x => (if x<2650 then (if x<1626 then (if x<132 then 0 else (if x<1596 then 0 else 1)) else (if x<1734 then (if x<1650 then 1 else 0) else (if x<2620 then 0 else 2))) else (if x<3158 then (if x<2674 then 2 else (if x<2758 then 3 else 3)) else (if x<3274 then (if x<3244 then 3 else 1) else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3266 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1734,1768,2620,2650,2652,2674,2702,2758,3102,3158,3192,3242,3244,3274,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3266 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3266 3242 4
  · have he : independentCachedBranchMembers3266.erase 3242=independentCachedBranchMembers3264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3264
  · have he : independentCachedBranchMembers3266.filter (independentCachedEdge 3242)=independentCachedBranchMembers3265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3265
def independentCachedBranchMembers3267 : Finset ℕ := ([48,80,130,1596,1628,1650,1678,2620,2652,2674,2702,3102,3244,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3267 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3267 4 (fun x => (if x<2620 then (if x<1596 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1650 then (if x<1628 then 0 else 1) else (if x<1678 then 1 else 0))) else (if x<3102 then (if x<2674 then (if x<2652 then 2 else 3) else (if x<2702 then 2 else 3)) else (if x<3276 then (if x<3244 then 3 else 2) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3268 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1734,1768,2620,2650,2652,2674,2702,2758,3102,3158,3192,3242,3244,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3268 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3268 3300 4
  · have he : independentCachedBranchMembers3268.erase 3300=independentCachedBranchMembers3266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3266
  · have he : independentCachedBranchMembers3268.filter (independentCachedEdge 3300)=independentCachedBranchMembers3267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3267
def independentCachedBranchMembers3269 : Finset ℕ := ([80,130,132,1626,1628,1678,1734,2650,2652,2702,2758,3102,3158,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3269 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3269 4 (fun x => (if x<2650 then (if x<1626 then (if x<130 then 0 else (if x<132 then 0 else 1)) else (if x<1678 then (if x<1628 then 1 else 0) else (if x<1734 then 0 else 1))) else (if x<3102 then (if x<2702 then (if x<2652 then 2 else 3) else (if x<2758 then 2 else 3)) else (if x<3274 then (if x<3158 then 2 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3270 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1734,1768,2620,2650,2652,2674,2702,2758,3102,3126,3158,3192,3242,3244,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3270 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3270 3126 4
  · have he : independentCachedBranchMembers3270.erase 3126=independentCachedBranchMembers3268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3268
  · have he : independentCachedBranchMembers3270.filter (independentCachedEdge 3126)=independentCachedBranchMembers3269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3269
def independentCachedBranchMembers3271 : Finset ℕ := ([80,130,1594,1628,1652,1678,1702,1768,2620,2650,2674,2758,3158,3244,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3271 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3271 4 (fun x => (if x<2620 then (if x<1652 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else 0)) else (if x<1702 then (if x<1678 then 1 else 0) else (if x<1768 then 1 else 1))) else (if x<3158 then (if x<2674 then (if x<2650 then 2 else 2) else (if x<2758 then 3 else 3)) else (if x<3274 then (if x<3244 then 3 else 2) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3272 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1734,1768,2618,2620,2650,2652,2674,2702,2758,3102,3126,3158,3192,3242,3244,3274,3276,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3272 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3272 2618 4
  · have he : independentCachedBranchMembers3272.erase 2618=independentCachedBranchMembers3270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3270
  · have he : independentCachedBranchMembers3272.filter (independentCachedEdge 2618)=independentCachedBranchMembers3271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3271
def independentCachedBranchMembers3273 : Finset ℕ := ([18,48,80,130,132,192,1594,1596,1622,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1764,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3273 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3273 3304 5
  · have he : independentCachedBranchMembers3273.erase 3304=independentCachedBranchMembers3261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3261
  · have he : independentCachedBranchMembers3273.filter (independentCachedEdge 3304)=independentCachedBranchMembers3272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3272
def independentCachedBranchMembers3274 : Finset ℕ := ([18,48,132,1596,1628,1650,1702,1734,1738,1764,1768,2614,2618,2646,2650,2680,2702,2732,2764,2786,3126,3130,3162,3188,3192,3244,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3274 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3274 5 (fun x => (if x<2650 then (if x<1734 then (if x<1596 then (if x<48 then 0 else (if x<132 then 1 else 0)) else (if x<1650 then (if x<1628 then 1 else 2) else (if x<1702 then 0 else 3))) else (if x<1768 then (if x<1738 then 2 else (if x<1764 then 3 else 0)) else (if x<2618 then (if x<2614 then 2 else 1) else (if x<2646 then 0 else 2)))) else (if x<3130 then (if x<2732 then (if x<2680 then 3 else (if x<2702 then 1 else 3)) else (if x<2786 then (if x<2764 then 0 else 2) else (if x<3126 then 2 else 4))) else (if x<3192 then (if x<3162 then 1 else (if x<3188 then 0 else 1)) else (if x<3276 then (if x<3244 then 4 else 4) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3275 : Finset ℕ := ([18,1596,1628,1764,1768,2614,2618,2646,2650,2702,2786,3188,3192,3244,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3275 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3275 4 (fun x => (if x<2646 then (if x<1764 then (if x<1596 then 0 else (if x<1628 then 1 else 2)) else (if x<2614 then (if x<1768 then 0 else 1) else (if x<2618 then 1 else 0))) else (if x<3188 then (if x<2702 then (if x<2650 then 2 else 3) else (if x<2786 then 3 else 1)) else (if x<3244 then (if x<3192 then 2 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3276 : Finset ℕ := ([18,48,132,1596,1628,1650,1702,1734,1738,1764,1768,2614,2618,2646,2650,2680,2702,2732,2764,2786,3126,3130,3162,3188,3192,3214,3244,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3276 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3276 3214 4
  · have he : independentCachedBranchMembers3276.erase 3214=independentCachedBranchMembers3274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3274
  · have he : independentCachedBranchMembers3276.filter (independentCachedEdge 3214)=independentCachedBranchMembers3275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3275
def independentCachedBranchMembers3277 : Finset ℕ := ([18,48,1596,1734,1738,1764,1768,2614,2618,2764,2786,3126,3130,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3277 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3277 4 (fun x => (if x<2614 then (if x<1734 then (if x<48 then 0 else (if x<1596 then 1 else 1)) else (if x<1764 then (if x<1738 then 2 else 3) else (if x<1768 then 0 else 2))) else (if x<3126 then (if x<2764 then (if x<2618 then 1 else 0) else (if x<2786 then 2 else 2)) else (if x<3276 then (if x<3130 then 3 else 1) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3278 : Finset ℕ := ([18,48,80,132,1596,1628,1650,1702,1734,1738,1764,1768,2614,2618,2646,2650,2680,2702,2732,2764,2786,3126,3130,3162,3188,3192,3214,3244,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3278 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3278 80 4
  · have he : independentCachedBranchMembers3278.erase 80=independentCachedBranchMembers3276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3276
  · have he : independentCachedBranchMembers3278.filter (independentCachedEdge 80)=independentCachedBranchMembers3277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3277
def independentCachedBranchMembers3279 : Finset ℕ := ([132,1596,1702,1738,1764,2618,2646,2680,2702,2764,2786,3126,3162,3188,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3279 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3279 4 (fun x => (if x<2680 then (if x<1738 then (if x<1596 then 0 else (if x<1702 then 1 else 0)) else (if x<2618 then (if x<1764 then 2 else 1) else (if x<2646 then 1 else 3))) else (if x<3126 then (if x<2764 then (if x<2702 then 0 else 2) else (if x<2786 then 3 else 1)) else (if x<3188 then (if x<3162 then 3 else 0) else (if x<3244 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3280 : Finset ℕ := ([1702,1764,2646,2786,3162,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3280 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3280 3 (fun x => (if x<2786 then (if x<1764 then 0 else (if x<2646 then 1 else 2)) else (if x<3162 then 0 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3281 : Finset ℕ := ([48,132,1596,1702,1738,1764,2618,2646,2680,2702,2764,2786,3126,3162,3188,3244] : List ℕ).toFinset
theorem independentCachedBranchBound3281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3281 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3281 48 3
  · have he : independentCachedBranchMembers3281.erase 48=independentCachedBranchMembers3279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3279
  · have he : independentCachedBranchMembers3281.filter (independentCachedEdge 48)=independentCachedBranchMembers3280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3280
def independentCachedBranchMembers3282 : Finset ℕ := ([18,48,80,132,1596,1628,1650,1702,1734,1738,1764,1768,2614,2618,2646,2650,2680,2702,2732,2764,2786,3126,3130,3158,3162,3188,3192,3214,3244,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3282 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3282 3158 4
  · have he : independentCachedBranchMembers3282.erase 3158=independentCachedBranchMembers3278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3278
  · have he : independentCachedBranchMembers3282.filter (independentCachedEdge 3158)=independentCachedBranchMembers3281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3281
def independentCachedBranchMembers3283 : Finset ℕ := ([18,48,80,130,132,192,1594,1596,1622,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1762,1764,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3283 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3283 1762 5
  · have he : independentCachedBranchMembers3283.erase 1762=independentCachedBranchMembers3273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3273
  · have he : independentCachedBranchMembers3283.filter (independentCachedEdge 1762)=independentCachedBranchMembers3282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3282
def independentCachedBranchMembers3284 : Finset ℕ := ([80,130,132,1594,1596,1622,1650,1652,1702,1738,1740,1768,2614,2652,2680,2702,2730,2732,2758,2788,3126,3162,3192,3214,3242,3244,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3284 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3284 5 (fun x => (if x<2680 then (if x<1652 then (if x<1594 then (if x<130 then 0 else (if x<132 then 0 else 1)) else (if x<1622 then (if x<1596 then 1 else 2) else (if x<1650 then 2 else 3))) else (if x<1740 then (if x<1702 then 0 else (if x<1738 then 0 else 3)) else (if x<2614 then (if x<1768 then 2 else 4) else (if x<2652 then 2 else 0)))) else (if x<3162 then (if x<2732 then (if x<2702 then 1 else (if x<2730 then 0 else 4)) else (if x<2788 then (if x<2758 then 2 else 2) else (if x<3126 then 1 else 3))) else (if x<3242 then (if x<3192 then 1 else (if x<3214 then 0 else 3)) else (if x<3270 then (if x<3244 then 0 else 4) else (if x<3298 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3285 : Finset ℕ := ([1596,1652,1740,1768,2652,2680,2732,2788,3126,3162,3214,3242,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3285 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3285 4 (fun x => (if x<2788 then (if x<1768 then (if x<1652 then 0 else (if x<1740 then 1 else 0)) else (if x<2680 then (if x<2652 then 1 else 0) else (if x<2732 then 1 else 0))) else (if x<3214 then (if x<3126 then 1 else (if x<3162 then 2 else 2)) else (if x<3270 then (if x<3242 then 2 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3286 : Finset ℕ := ([1740,1768,2732,2788,3126,3162] : List ℕ).toFinset
theorem independentCachedBranchBound3286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3286 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3286 3 (fun x => (if x<2788 then (if x<1768 then 0 else (if x<2732 then 1 else 0)) else (if x<3126 then 1 else (if x<3162 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3287 : Finset ℕ := ([130,1596,1652,1740,1768,2652,2680,2732,2788,3126,3162,3214,3242,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3287 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3287 130 3
  · have he : independentCachedBranchMembers3287.erase 130=independentCachedBranchMembers3285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3285
  · have he : independentCachedBranchMembers3287.filter (independentCachedEdge 130)=independentCachedBranchMembers3286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3286
def independentCachedBranchMembers3288 : Finset ℕ := ([80,130,132,1594,1596,1622,1650,1652,1702,1738,1740,1768,2614,2650,2652,2680,2702,2730,2732,2758,2788,3126,3162,3192,3214,3242,3244,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3288 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3288 2650 4
  · have he : independentCachedBranchMembers3288.erase 2650=independentCachedBranchMembers3284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3284
  · have he : independentCachedBranchMembers3288.filter (independentCachedEdge 2650)=independentCachedBranchMembers3287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3287
def independentCachedBranchMembers3289 : Finset ℕ := ([130,1596,1622,1650,1738,2614,2652,2680,2702,2730,2788,3162,3244,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3289 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3289 4 (fun x => (if x<2680 then (if x<1650 then (if x<1596 then 0 else (if x<1622 then 0 else 1)) else (if x<2614 then (if x<1738 then 2 else 1) else (if x<2652 then 1 else 0))) else (if x<3162 then (if x<2730 then (if x<2702 then 2 else 3) else (if x<2788 then 1 else 3)) else (if x<3270 then (if x<3244 then 2 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3290 : Finset ℕ := ([1596,1738,2614,2788,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3290 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3290 3 (fun x => (if x<2788 then (if x<1738 then 0 else (if x<2614 then 1 else 0)) else (if x<3270 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3291 : Finset ℕ := ([80,130,1596,1622,1650,1738,2614,2652,2680,2702,2730,2788,3162,3244,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3291 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3291 80 3
  · have he : independentCachedBranchMembers3291.erase 80=independentCachedBranchMembers3289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3289
  · have he : independentCachedBranchMembers3291.filter (independentCachedEdge 80)=independentCachedBranchMembers3290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3290
def independentCachedBranchMembers3292 : Finset ℕ := ([80,130,132,1594,1596,1622,1650,1652,1702,1738,1740,1768,2614,2650,2652,2680,2702,2730,2732,2758,2788,3126,3162,3192,3214,3242,3244,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3292 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3292 3300 4
  · have he : independentCachedBranchMembers3292.erase 3300=independentCachedBranchMembers3288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3288
  · have he : independentCachedBranchMembers3292.filter (independentCachedEdge 3300)=independentCachedBranchMembers3291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3291
def independentCachedBranchMembers3293 : Finset ℕ := ([80,132,1594,1622,1652,1740,2652,2730,2758,2788,3126,3162,3192,3214,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3293 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3293 4 (fun x => (if x<2758 then (if x<1652 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1622 then 1 else 1)) else (if x<2652 then (if x<1740 then 2 else 2) else (if x<2730 then 2 else 1))) else (if x<3192 then (if x<3126 then (if x<2788 then 1 else 2) else (if x<3162 then 3 else 0)) else (if x<3244 then (if x<3214 then 3 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3294 : Finset ℕ := ([80,130,132,1594,1596,1622,1650,1652,1702,1738,1740,1768,2614,2650,2652,2680,2702,2730,2732,2758,2786,2788,3126,3162,3192,3214,3242,3244,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3294 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3294 2786 4
  · have he : independentCachedBranchMembers3294.erase 2786=independentCachedBranchMembers3292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3292
  · have he : independentCachedBranchMembers3294.filter (independentCachedEdge 2786)=independentCachedBranchMembers3293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3293
def independentCachedBranchMembers3295 : Finset ℕ := ([18,48,80,130,132,192,1590,1594,1596,1622,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1762,1764,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3295 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3295 1590 5
  · have he : independentCachedBranchMembers3295.erase 1590=independentCachedBranchMembers3283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3283
  · have he : independentCachedBranchMembers3295.filter (independentCachedEdge 1590)=independentCachedBranchMembers3294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3294
def independentCachedBranchMembers3296 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1734,1768,2614,2646,2680,2730,2732,2762,2764,2786,2788,3132,3162,3186,3188,3214,3238,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3296 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3296 5 (fun x => (if x<2680 then (if x<1652 then (if x<132 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1628 then (if x<1594 then 1 else 2) else (if x<1650 then 2 else 1))) else (if x<1734 then (if x<1678 then 0 else (if x<1702 then 2 else 1)) else (if x<2614 then (if x<1768 then 0 else 2) else (if x<2646 then 3 else 4)))) else (if x<3132 then (if x<2762 then (if x<2730 then 0 else (if x<2732 then 2 else 1)) else (if x<2786 then (if x<2764 then 0 else 2) else (if x<2788 then 3 else 4))) else (if x<3214 then (if x<3186 then (if x<3162 then 0 else 1) else (if x<3188 then 3 else 4)) else (if x<3270 then (if x<3238 then 0 else 3) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3297 : Finset ℕ := ([80,130,1594,1628,1652,1678,1702,1768,2646,2732,2762,2786,3132,3162,3186,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3297 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3297 4 (fun x => (if x<2646 then (if x<1652 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else 0)) else (if x<1702 then (if x<1678 then 1 else 0) else (if x<1768 then 1 else 1))) else (if x<3132 then (if x<2762 then (if x<2732 then 2 else 3) else (if x<2786 then 2 else 3)) else (if x<3186 then (if x<3162 then 3 else 2) else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3298 : Finset ℕ := ([48,80,130,132,1594,1628,1650,1652,1678,1702,1734,1768,2614,2646,2680,2730,2732,2762,2764,2786,2788,3130,3132,3162,3186,3188,3214,3238,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3298 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3298 3130 4
  · have he : independentCachedBranchMembers3298.erase 3130=independentCachedBranchMembers3296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3296
  · have he : independentCachedBranchMembers3298.filter (independentCachedEdge 3130)=independentCachedBranchMembers3297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3297
def independentCachedBranchMembers3299 : Finset ℕ := ([48,130,1594,1628,1650,1702,2614,2730,2764,2786,3132,3162,3188,3214,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3299 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3299 4 (fun x => (if x<2764 then (if x<1650 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else 1)) else (if x<2614 then (if x<1702 then 2 else 2) else (if x<2730 then 2 else 1))) else (if x<3188 then (if x<3132 then (if x<2786 then 1 else 2) else (if x<3162 then 0 else 3)) else (if x<3270 then (if x<3214 then 3 else 0) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3300 : Finset ℕ := ([48,80,130,132,1594,1626,1628,1650,1652,1678,1702,1734,1768,2614,2646,2680,2730,2732,2762,2764,2786,2788,3130,3132,3162,3186,3188,3214,3238,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3300 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3300 1626 4
  · have he : independentCachedBranchMembers3300.erase 1626=independentCachedBranchMembers3298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3298
  · have he : independentCachedBranchMembers3300.filter (independentCachedEdge 1626)=independentCachedBranchMembers3299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3299
def independentCachedBranchMembers3301 : Finset ℕ := ([80,132,1594,1628,1652,1734,2646,2730,2764,2788,3132,3162,3186,3214,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3301 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3301 4 (fun x => (if x<2764 then (if x<1652 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1628 then 1 else 1)) else (if x<2646 then (if x<1734 then 2 else 2) else (if x<2730 then 2 else 1))) else (if x<3186 then (if x<3132 then (if x<2788 then 1 else 2) else (if x<3162 then 3 else 0)) else (if x<3238 then (if x<3214 then 3 else 0) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3302 : Finset ℕ := ([48,80,130,132,1594,1596,1626,1628,1650,1652,1678,1702,1734,1768,2614,2646,2680,2730,2732,2762,2764,2786,2788,3130,3132,3162,3186,3188,3214,3238,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3302 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3302 1596 4
  · have he : independentCachedBranchMembers3302.erase 1596=independentCachedBranchMembers3300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3300
  · have he : independentCachedBranchMembers3302.filter (independentCachedEdge 1596)=independentCachedBranchMembers3301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3301
def independentCachedBranchMembers3303 : Finset ℕ := ([18,48,80,130,132,192,1590,1594,1596,1622,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1762,1764,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,2792,3102,3126,3130,3132,3158,3162,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3303 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3303 2792 5
  · have he : independentCachedBranchMembers3303.erase 2792=independentCachedBranchMembers3295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3295
  · have he : independentCachedBranchMembers3303.filter (independentCachedEdge 2792)=independentCachedBranchMembers3302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3302
def independentCachedBranchMembers3304 : Finset ℕ := ([18,48,132,192,1590,1594,1628,1650,1708,1734,1738,1764,2614,2618,2652,2674,2702,2758,2788,2792,3102,3132,3158,3162,3188,3192,3238,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3304 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3304 5 (fun x => (if x<2652 then (if x<1650 then (if x<192 then (if x<48 then 0 else (if x<132 then 1 else 0)) else (if x<1594 then (if x<1590 then 1 else 1) else (if x<1628 then 0 else 2))) else (if x<1738 then (if x<1708 then 2 else (if x<1734 then 0 else 1)) else (if x<2614 then (if x<1764 then 2 else 2) else (if x<2618 then 3 else 1)))) else (if x<3132 then (if x<2758 then (if x<2674 then 3 else (if x<2702 then 0 else 3)) else (if x<2792 then (if x<2788 then 4 else 0) else (if x<3102 then 4 else 3))) else (if x<3192 then (if x<3162 then (if x<3158 then 1 else 4) else (if x<3188 then 0 else 2)) else (if x<3276 then (if x<3238 then 4 else 3) else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3305 : Finset ℕ := ([18,48,132,192,1590,1650,1734,1764,2614,2674,2758,2788,3158,3188,3238,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3305 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3305 4 (fun x => (if x<2614 then (if x<1590 then (if x<132 then (if x<48 then 0 else 1) else (if x<192 then 0 else 1)) else (if x<1734 then (if x<1650 then 1 else 0) else (if x<1764 then 1 else 0))) else (if x<3158 then (if x<2758 then (if x<2674 then 2 else 3) else (if x<2788 then 2 else 3)) else (if x<3238 then (if x<3188 then 2 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3306 : Finset ℕ := ([18,48,132,192,1590,1594,1628,1650,1708,1734,1738,1764,2614,2618,2652,2674,2702,2758,2788,2792,3102,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3306 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3306 3242 4
  · have he : independentCachedBranchMembers3306.erase 3242=independentCachedBranchMembers3304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3304
  · have he : independentCachedBranchMembers3306.filter (independentCachedEdge 3242)=independentCachedBranchMembers3305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3305
def independentCachedBranchMembers3307 : Finset ℕ := ([18,132,1594,1628,1650,1708,1738,1764,2614,2702,2758,2792,3102,3158,3192,3238] : List ℕ).toFinset
theorem independentCachedBranchBound3307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3307 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3307 4 (fun x => (if x<2614 then (if x<1650 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1628 then 0 else 1)) else (if x<1738 then (if x<1708 then 1 else 0) else (if x<1764 then 1 else 1))) else (if x<3102 then (if x<2758 then (if x<2702 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3192 then (if x<3158 then 2 else 3) else (if x<3238 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3308 : Finset ℕ := ([18,48,132,192,1590,1594,1628,1650,1708,1734,1738,1764,2614,2618,2652,2674,2702,2758,2762,2788,2792,3102,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3308 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3308 2762 4
  · have he : independentCachedBranchMembers3308.erase 2762=independentCachedBranchMembers3306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3306
  · have he : independentCachedBranchMembers3308.filter (independentCachedEdge 2762)=independentCachedBranchMembers3307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3307
def independentCachedBranchMembers3309 : Finset ℕ := ([48,192,1590,1594,1628,1708,1734,1738,2674,2702,2788,2792,3102,3188,3192,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3309 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3309 4 (fun x => (if x<2674 then (if x<1628 then (if x<1590 then (if x<192 then 0 else 0) else (if x<1594 then 0 else 1)) else (if x<1734 then (if x<1708 then 1 else 1) else (if x<1738 then 0 else 1))) else (if x<3102 then (if x<2788 then (if x<2702 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3192 then (if x<3188 then 3 else 2) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3310 : Finset ℕ := ([18,48,132,192,1590,1594,1628,1650,1708,1734,1738,1764,2614,2618,2652,2674,2702,2732,2758,2762,2788,2792,3102,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3310 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3310 2732 4
  · have he : independentCachedBranchMembers3310.erase 2732=independentCachedBranchMembers3308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3308
  · have he : independentCachedBranchMembers3310.filter (independentCachedEdge 2732)=independentCachedBranchMembers3309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3309
def independentCachedBranchMembers3311 : Finset ℕ := ([132,1590,1708,1738,1764,2618,2652,2674,2702,2758,2792,3132,3162,3188,3238] : List ℕ).toFinset
theorem independentCachedBranchBound3311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3311 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3311 4 (fun x => (if x<2674 then (if x<1738 then (if x<1590 then 0 else (if x<1708 then 1 else 0)) else (if x<2618 then (if x<1764 then 2 else 1) else (if x<2652 then 1 else 3))) else (if x<3132 then (if x<2758 then (if x<2702 then 0 else 2) else (if x<2792 then 3 else 1)) else (if x<3188 then (if x<3162 then 3 else 0) else (if x<3238 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3312 : Finset ℕ := ([1708,1764,2652,2792,3162,3238] : List ℕ).toFinset
theorem independentCachedBranchBound3312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3312 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3312 3 (fun x => (if x<2792 then (if x<1764 then 0 else (if x<2652 then 1 else 2)) else (if x<3162 then 0 else (if x<3238 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3313 : Finset ℕ := ([48,132,1590,1708,1738,1764,2618,2652,2674,2702,2758,2792,3132,3162,3188,3238] : List ℕ).toFinset
theorem independentCachedBranchBound3313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3313 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3313 48 3
  · have he : independentCachedBranchMembers3313.erase 48=independentCachedBranchMembers3311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3311
  · have he : independentCachedBranchMembers3313.filter (independentCachedEdge 48)=independentCachedBranchMembers3312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3312
def independentCachedBranchMembers3314 : Finset ℕ := ([18,48,132,192,1590,1594,1628,1650,1708,1734,1738,1764,1768,2614,2618,2652,2674,2702,2732,2758,2762,2788,2792,3102,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3314 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3314 1768 4
  · have he : independentCachedBranchMembers3314.erase 1768=independentCachedBranchMembers3310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3310
  · have he : independentCachedBranchMembers3314.filter (independentCachedEdge 1768)=independentCachedBranchMembers3313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3313
def independentCachedBranchMembers3315 : Finset ℕ := ([192,1650,1708,1734,1738,2614,2618,2652,2702,2788,2792,3132,3158,3162,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3315 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3315 4 (fun x => (if x<2652 then (if x<1734 then (if x<1650 then 0 else (if x<1708 then 1 else 2)) else (if x<2614 then (if x<1738 then 0 else 1) else (if x<2618 then 1 else 0))) else (if x<3132 then (if x<2788 then (if x<2702 then 3 else 1) else (if x<2792 then 2 else 3)) else (if x<3162 then (if x<3158 then 0 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3316 : Finset ℕ := ([1734,1738,2652,2702,3132,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3316 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3316 3 (fun x => (if x<2702 then (if x<1738 then 0 else (if x<2652 then 1 else 2)) else (if x<3132 then 0 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3317 : Finset ℕ := ([18,192,1650,1708,1734,1738,2614,2618,2652,2702,2788,2792,3132,3158,3162,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3317 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3317 18 3
  · have he : independentCachedBranchMembers3317.erase 18=independentCachedBranchMembers3315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3315
  · have he : independentCachedBranchMembers3317.filter (independentCachedEdge 18)=independentCachedBranchMembers3316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3316
def independentCachedBranchMembers3318 : Finset ℕ := ([18,48,132,192,1590,1594,1628,1650,1678,1708,1734,1738,1764,1768,2614,2618,2652,2674,2702,2732,2758,2762,2788,2792,3102,3132,3158,3162,3188,3192,3238,3242,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3318 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3318 1678 4
  · have he : independentCachedBranchMembers3318.erase 1678=independentCachedBranchMembers3314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3314
  · have he : independentCachedBranchMembers3318.filter (independentCachedEdge 1678)=independentCachedBranchMembers3317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3317
def independentCachedBranchMembers3319 : Finset ℕ := ([18,48,80,130,132,192,1590,1594,1596,1622,1626,1628,1650,1652,1678,1702,1708,1734,1738,1740,1762,1764,1768,2614,2618,2620,2646,2650,2652,2674,2680,2702,2730,2732,2758,2762,2764,2786,2788,2792,3102,3126,3130,3132,3158,3162,3164,3186,3188,3192,3214,3238,3242,3244,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3319 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3319 3164 5
  · have he : independentCachedBranchMembers3319.erase 3164=independentCachedBranchMembers3303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3303
  · have he : independentCachedBranchMembers3319.filter (independentCachedEdge 3164)=independentCachedBranchMembers3318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3318
def independentCachedBranchMembers3320 : Finset ℕ := ([12,18,40,48,72,80,130,132,144,192,222,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3320 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3320 144 6
  · have he : independentCachedBranchMembers3320.erase 144=independentCachedBranchMembers3172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3172
  · have he : independentCachedBranchMembers3320.filter (independentCachedEdge 144)=independentCachedBranchMembers3319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3319
def independentCachedBranchMembers3321 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1748,1752,1768,2606,2614,2652,2680,2710,2714,2730,2764,2788,2800,3102,3180,3188,3192,3238,3242,3250,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3321 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3321 6 (fun x => (if x<2680 then (if x<1678 then (if x<1594 then (if x<130 then (if x<80 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1644 then (if x<1628 then 2 else 0) else (if x<1652 then 2 else 1))) else (if x<1768 then (if x<1748 then (if x<1702 then 2 else 3) else (if x<1752 then 3 else 1)) else (if x<2614 then (if x<2606 then 3 else 2) else (if x<2652 then 4 else 1)))) else (if x<3180 then (if x<2764 then (if x<2714 then (if x<2710 then 0 else 3) else (if x<2730 then 2 else 3)) else (if x<2800 then (if x<2788 then 2 else 3) else (if x<3102 then 1 else 4))) else (if x<3242 then (if x<3192 then (if x<3188 then 0 else 4) else (if x<3238 then 1 else 0)) else (if x<3276 then (if x<3250 then 5 else 4) else (if x<3284 then 5 else (if x<3288 then 1 else 4)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3322 : Finset ℕ := ([80,252,1594,1628,1644,1702,2606,2680,2788,3102,3188,3192,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3322 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3322 5 (fun x => (if x<2680 then (if x<1628 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1702 then (if x<1644 then 0 else 1) else (if x<2606 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2788 then 0 else 1) else (if x<3188 then 2 else 0)) else (if x<3284 then (if x<3250 then 2 else 2) else (if x<3288 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3323 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2680,2710,2714,2730,2764,2788,2800,3102,3180,3188,3192,3238,3242,3250,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3323 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3323 1714 5
  · have he : independentCachedBranchMembers3323.erase 1714=independentCachedBranchMembers3321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3321
  · have he : independentCachedBranchMembers3323.filter (independentCachedEdge 1714)=independentCachedBranchMembers3322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3322
def independentCachedBranchMembers3324 : Finset ℕ := ([80,130,1594,1628,1652,1678,1702,1714,1748,1768,2606,2652,2714,3102,3180,3192,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3324 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3324 5 (fun x => (if x<1768 then (if x<1652 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else 0)) else (if x<1702 then (if x<1678 then 1 else 0) else (if x<1714 then 1 else (if x<1748 then 2 else 2)))) else (if x<3180 then (if x<2652 then (if x<2606 then 1 else 3) else (if x<2714 then 2 else (if x<3102 then 3 else 3))) else (if x<3242 then (if x<3192 then 3 else 0) else (if x<3276 then 0 else (if x<3288 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3325 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2680,2710,2714,2730,2764,2788,2800,3102,3180,3188,3192,3238,3242,3250,3276,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3325 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3325 3304 5
  · have he : independentCachedBranchMembers3325.erase 3304=independentCachedBranchMembers3323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3323
  · have he : independentCachedBranchMembers3325.filter (independentCachedEdge 3304)=independentCachedBranchMembers3324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3324
def independentCachedBranchMembers3326 : Finset ℕ := ([72,80,252,1628,1702,1748,1768,2606,2614,2652,2680,2714,2764,2800,3102,3180,3188,3242,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3326 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3326 5 (fun x => (if x<2680 then (if x<1748 then (if x<252 then (if x<80 then 0 else 1) else (if x<1628 then 0 else (if x<1702 then 0 else 1))) else (if x<2606 then (if x<1768 then 1 else 0) else (if x<2614 then 1 else (if x<2652 then 2 else 1)))) else (if x<3180 then (if x<2764 then (if x<2714 then 0 else 2) else (if x<2800 then 0 else (if x<3102 then 2 else 2))) else (if x<3242 then (if x<3188 then 0 else 2) else (if x<3250 then 1 else (if x<3288 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3327 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2680,2710,2714,2730,2764,2788,2800,3102,3180,3188,3192,3226,3238,3242,3250,3276,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3327 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3327 3226 5
  · have he : independentCachedBranchMembers3327.erase 3226=independentCachedBranchMembers3325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3325
  · have he : independentCachedBranchMembers3327.filter (independentCachedEdge 3226)=independentCachedBranchMembers3326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3326
end EntropyDesigns.QuadraticRefinement
