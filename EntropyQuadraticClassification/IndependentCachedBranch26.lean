/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch25
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3328 : Finset ℕ := ([72,252,1628,1652,1714,1768,2606,2652,2680,2710,2714,2764,2788,3102,3180,3238,3242,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3328 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3328 5 (fun x => (if x<2710 then (if x<1714 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1652 then 0 else 1)) else (if x<2606 then (if x<1768 then 1 else 0) else (if x<2652 then 2 else (if x<2680 then 1 else 0)))) else (if x<3180 then (if x<2764 then (if x<2714 then 2 else 1) else (if x<2788 then 0 else (if x<3102 then 2 else 2))) else (if x<3242 then (if x<3238 then 0 else 2) else (if x<3284 then 1 else (if x<3288 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3329 : Finset ℕ := ([252,1768,2606,2764,2788,3102,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3329 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3329 4 (fun x => (if x<2788 then (if x<2606 then (if x<1768 then 0 else 0) else (if x<2764 then 1 else 0)) else (if x<3284 then (if x<3102 then 1 else 1) else (if x<3288 then 1 else 0))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3330 : Finset ℕ := ([72,130,252,1628,1652,1714,1768,2606,2652,2680,2710,2714,2764,2788,3102,3180,3238,3242,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3330 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3330 130 4
  · have he : independentCachedBranchMembers3330.erase 130=independentCachedBranchMembers3328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3328
  · have he : independentCachedBranchMembers3330.filter (independentCachedEdge 130)=independentCachedBranchMembers3329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3329
def independentCachedBranchMembers3331 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2680,2710,2714,2730,2764,2788,2800,3102,3118,3180,3188,3192,3226,3238,3242,3250,3276,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3331 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3331 3118 5
  · have he : independentCachedBranchMembers3331.erase 3118=independentCachedBranchMembers3327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3327
  · have he : independentCachedBranchMembers3331.filter (independentCachedEdge 3118)=independentCachedBranchMembers3330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3330
def independentCachedBranchMembers3332 : Finset ℕ := ([1594,1644,1652,1678,1714,1752,2606,2614,2652,2680,2714,2764,2800,3102,3180,3188,3242,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3332 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3332 5 (fun x => (if x<2680 then (if x<1714 then (if x<1652 then (if x<1644 then 0 else 0) else (if x<1678 then 1 else 0)) else (if x<2606 then (if x<1752 then 1 else 0) else (if x<2614 then 0 else (if x<2652 then 1 else 1)))) else (if x<3180 then (if x<2764 then (if x<2714 then 0 else 0) else (if x<2800 then 0 else (if x<3102 then 1 else 2))) else (if x<3242 then (if x<3188 then 2 else 3) else (if x<3250 then 2 else (if x<3288 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3333 : Finset ℕ := ([1594,1752,2606,2614,2764,2800,3102,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3333 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3333 4 (fun x => (if x<2764 then (if x<2606 then (if x<1752 then 0 else 0) else (if x<2614 then 0 else 1)) else (if x<3102 then (if x<2800 then 0 else 1) else (if x<3288 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3334 : Finset ℕ := ([130,1594,1644,1652,1678,1714,1752,2606,2614,2652,2680,2714,2764,2800,3102,3180,3188,3242,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3334 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3334 130 4
  · have he : independentCachedBranchMembers3334.erase 130=independentCachedBranchMembers3332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3332
  · have he : independentCachedBranchMembers3334.filter (independentCachedEdge 130)=independentCachedBranchMembers3333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3333
def independentCachedBranchMembers3335 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2680,2710,2714,2730,2764,2776,2788,2800,3102,3118,3180,3188,3192,3226,3238,3242,3250,3276,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3335 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3335 2776 5
  · have he : independentCachedBranchMembers3335.erase 2776=independentCachedBranchMembers3331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3331
  · have he : independentCachedBranchMembers3335.filter (independentCachedEdge 2776)=independentCachedBranchMembers3334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3334
def independentCachedBranchMembers3336 : Finset ℕ := ([1594,1644,1678,1702,1748,1752,2606,2652,2680,2710,2714,2764,2788,3102,3180,3238,3242,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3336 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3336 5 (fun x => (if x<2710 then (if x<1748 then (if x<1678 then (if x<1644 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<2606 then (if x<1752 then 1 else 0) else (if x<2652 then 0 else (if x<2680 then 1 else 0)))) else (if x<3180 then (if x<2764 then (if x<2714 then 1 else 0) else (if x<2788 then 0 else (if x<3102 then 1 else 2))) else (if x<3242 then (if x<3238 then 2 else 2) else (if x<3284 then 3 else (if x<3288 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3337 : Finset ℕ := ([1594,1644,2710,2714,2764,2788,3102,3180] : List ℕ).toFinset
theorem independentCachedBranchBound3337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3337 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3337 4 (fun x => (if x<2764 then (if x<2710 then (if x<1644 then 0 else 0) else (if x<2714 then 1 else 0)) else (if x<3102 then (if x<2788 then 0 else 1) else (if x<3180 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3338 : Finset ℕ := ([80,1594,1644,1678,1702,1748,1752,2606,2652,2680,2710,2714,2764,2788,3102,3180,3238,3242,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3338 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3338 80 4
  · have he : independentCachedBranchMembers3338.erase 80=independentCachedBranchMembers3336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3336
  · have he : independentCachedBranchMembers3338.filter (independentCachedEdge 80)=independentCachedBranchMembers3337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3337
def independentCachedBranchMembers3339 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2668,2680,2710,2714,2730,2764,2776,2788,2800,3102,3118,3180,3188,3192,3226,3238,3242,3250,3276,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3339 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3339 2668 5
  · have he : independentCachedBranchMembers3339.erase 2668=independentCachedBranchMembers3335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3335
  · have he : independentCachedBranchMembers3339.filter (independentCachedEdge 2668)=independentCachedBranchMembers3338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3338
def independentCachedBranchMembers3340 : Finset ℕ := ([1594,1628,1678,1768,2606,2614,2652,2710,2714,2788,2800,3102,3180,3188,3192,3238,3242,3250,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3340 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3340 5 (fun x => (if x<2800 then (if x<2614 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1768 then 0 else (if x<2606 then 0 else 1))) else (if x<2710 then (if x<2652 then 2 else 1) else (if x<2714 then 1 else (if x<2788 then 2 else 1)))) else (if x<3238 then (if x<3180 then (if x<3102 then 2 else 0) else (if x<3188 then 1 else (if x<3192 then 2 else 0))) else (if x<3276 then (if x<3242 then 1 else (if x<3250 then 0 else 2)) else (if x<3284 then 0 else (if x<3288 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3341 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2668,2680,2710,2714,2730,2764,2776,2788,2800,3102,3118,3164,3180,3188,3192,3226,3238,3242,3250,3276,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3341 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3341 3164 5
  · have he : independentCachedBranchMembers3341.erase 3164=independentCachedBranchMembers3339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3339
  · have he : independentCachedBranchMembers3341.filter (independentCachedEdge 3164)=independentCachedBranchMembers3340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3340
def independentCachedBranchMembers3342 : Finset ℕ := ([72,130,1594,1628,1644,1702,2614,2652,2668,2710,2714,2730,2764,2800,3102,3118,3188,3192,3250,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3342 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3342 5 (fun x => (if x<2730 then (if x<1702 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else (if x<1644 then 0 else 1))) else (if x<2668 then (if x<2614 then 1 else (if x<2652 then 2 else 2)) else (if x<2710 then 0 else (if x<2714 then 3 else 2)))) else (if x<3188 then (if x<2800 then (if x<2764 then 3 else 3) else (if x<3102 then 2 else (if x<3118 then 2 else 1))) else (if x<3284 then (if x<3192 then 2 else (if x<3250 then 0 else 0)) else (if x<3288 then 3 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3343 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2668,2680,2710,2714,2730,2764,2776,2788,2800,3102,3118,3164,3180,3188,3192,3226,3238,3242,3250,3276,3284,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3343 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3343 3312 5
  · have he : independentCachedBranchMembers3343.erase 3312=independentCachedBranchMembers3341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3341
  · have he : independentCachedBranchMembers3343.filter (independentCachedEdge 3312)=independentCachedBranchMembers3342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3342
def independentCachedBranchMembers3344 : Finset ℕ := ([80,252,1594,1628,1652,1752,2606,2652,2710,2730,2764,2776,2788,2800,3102,3180,3192,3226,3238,3250,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3344 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3344 5 (fun x => (if x<2776 then (if x<1752 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1628 then 1 else (if x<1652 then 0 else 1))) else (if x<2710 then (if x<2606 then 1 else (if x<2652 then 2 else 2)) else (if x<2730 then 2 else (if x<2764 then 3 else 3)))) else (if x<3192 then (if x<2800 then (if x<2788 then 0 else 2) else (if x<3102 then 3 else (if x<3180 then 2 else 2))) else (if x<3250 then (if x<3226 then 0 else (if x<3238 then 1 else 2)) else (if x<3284 then 3 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3345 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2668,2680,2710,2714,2730,2764,2776,2788,2800,3102,3118,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3345 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3345 3222 5
  · have he : independentCachedBranchMembers3345.erase 3222=independentCachedBranchMembers3343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3343
  · have he : independentCachedBranchMembers3345.filter (independentCachedEdge 3222)=independentCachedBranchMembers3344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3344
def independentCachedBranchMembers3346 : Finset ℕ := ([72,252,1594,1628,1644,1678,1714,1748,1752,1768,2606,2680,2710,2714,2730,2764,2800,3164,3180,3250,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3346 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3346 5 (fun x => (if x<2680 then (if x<1678 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1628 then 1 else (if x<1644 then 0 else 1))) else (if x<1752 then (if x<1714 then 1 else (if x<1748 then 2 else 2)) else (if x<1768 then 1 else (if x<2606 then 0 else 1)))) else (if x<3164 then (if x<2730 then (if x<2710 then 0 else (if x<2714 then 2 else 1)) else (if x<2764 then 2 else (if x<2800 then 0 else 2))) else (if x<3284 then (if x<3180 then 3 else (if x<3250 then 0 else 4)) else (if x<3288 then 4 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3347 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2668,2680,2702,2710,2714,2730,2764,2776,2788,2800,3102,3118,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3347 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3347 2702 5
  · have he : independentCachedBranchMembers3347.erase 2702=independentCachedBranchMembers3345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3345
  · have he : independentCachedBranchMembers3347.filter (independentCachedEdge 2702)=independentCachedBranchMembers3346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3346
def independentCachedBranchMembers3348 : Finset ℕ := ([72,130,1644,1678,1702,1714,1748,1768,2606,2652,2710,2730,2764,2776,2788,2800,3102,3180,3192,3226,3238,3250,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3348 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3348 5 (fun x => (if x<2764 then (if x<1748 then (if x<1678 then (if x<130 then 0 else (if x<1644 then 0 else 0)) else (if x<1702 then 1 else (if x<1714 then 0 else 1))) else (if x<2652 then (if x<1768 then 1 else (if x<2606 then 1 else 2)) else (if x<2710 then 0 else (if x<2730 then 0 else 1)))) else (if x<3192 then (if x<2800 then (if x<2776 then 1 else (if x<2788 then 3 else 2)) else (if x<3102 then 1 else (if x<3180 then 2 else 2))) else (if x<3250 then (if x<3226 then 0 else (if x<3238 then 3 else 2)) else (if x<3284 then 0 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3349 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2668,2680,2702,2710,2714,2730,2764,2772,2776,2788,2800,3102,3118,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3349 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3349 2772 5
  · have he : independentCachedBranchMembers3349.erase 2772=independentCachedBranchMembers3347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3347
  · have he : independentCachedBranchMembers3349.filter (independentCachedEdge 2772)=independentCachedBranchMembers3348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3348
def independentCachedBranchMembers3350 : Finset ℕ := ([80,252,1652,1678,1714,1748,1752,1768,2614,2652,2668,2710,2714,2730,2764,2800,3102,3118,3188,3192,3250,3284,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3350 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3350 5 (fun x => (if x<2714 then (if x<1752 then (if x<1678 then (if x<252 then 0 else (if x<1652 then 0 else 0)) else (if x<1714 then 1 else (if x<1748 then 1 else 1))) else (if x<2652 then (if x<1768 then 0 else (if x<2614 then 1 else 2)) else (if x<2668 then 0 else (if x<2710 then 2 else 1)))) else (if x<3188 then (if x<2800 then (if x<2730 then 3 else (if x<2764 then 1 else 1)) else (if x<3102 then 0 else (if x<3118 then 3 else 2))) else (if x<3284 then (if x<3192 then 2 else (if x<3250 then 0 else 2)) else (if x<3288 then 0 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3351 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2800,3102,3118,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3351 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3351 2738 5
  · have he : independentCachedBranchMembers3351.erase 2738=independentCachedBranchMembers3349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3349
  · have he : independentCachedBranchMembers3351.filter (independentCachedEdge 2738)=independentCachedBranchMembers3350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3350
def independentCachedBranchMembers3352 : Finset ℕ := ([72,130,1652,1678,1714,1748,1752,1768,2614,2652,2710,2714,2730,2764,2800,3180,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3352 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3352 5 (fun x => (if x<2714 then (if x<1748 then (if x<1652 then (if x<130 then 0 else 0) else (if x<1678 then 1 else (if x<1714 then 2 else 0))) else (if x<2614 then (if x<1752 then 2 else (if x<1768 then 1 else 2)) else (if x<2652 then 1 else (if x<2710 then 0 else 0)))) else (if x<3222 then (if x<2764 then (if x<2730 then 1 else 2) else (if x<2800 then 2 else (if x<3180 then 1 else 0))) else (if x<3242 then (if x<3226 then 3 else (if x<3238 then 4 else 0)) else (if x<3276 then 3 else (if x<3312 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3353 : Finset ℕ := ([1678,1768,2614,2652,2710,2714,2800,3180,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3353 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3353 4 (fun x => (if x<2714 then (if x<2614 then (if x<1768 then 0 else 0) else (if x<2652 then 1 else (if x<2710 then 1 else 0))) else (if x<3238 then (if x<2800 then 1 else (if x<3180 then 0 else 2)) else (if x<3242 then 2 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3354 : Finset ℕ := ([72,130,1652,1678,1714,1748,1752,1768,2614,2652,2710,2714,2730,2764,2800,3164,3180,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3354 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3354 3164 4
  · have he : independentCachedBranchMembers3354.erase 3164=independentCachedBranchMembers3352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3352
  · have he : independentCachedBranchMembers3354.filter (independentCachedEdge 3164)=independentCachedBranchMembers3353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3353
def independentCachedBranchMembers3355 : Finset ℕ := ([1678,1748,1752,2652,2710,2714,2764,3180,3238,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3355 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3355 4 (fun x => (if x<2714 then (if x<1752 then (if x<1748 then 0 else 0) else (if x<2652 then 1 else (if x<2710 then 1 else 0))) else (if x<3238 then (if x<2764 then 1 else (if x<3180 then 0 else 2)) else (if x<3242 then 2 else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3356 : Finset ℕ := ([72,130,1652,1678,1714,1748,1752,1768,2614,2652,2668,2710,2714,2730,2764,2800,3164,3180,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3356 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3356 2668 4
  · have he : independentCachedBranchMembers3356.erase 2668=independentCachedBranchMembers3354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3354
  · have he : independentCachedBranchMembers3356.filter (independentCachedEdge 2668)=independentCachedBranchMembers3355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3355
def independentCachedBranchMembers3357 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1714,1748,1752,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2800,3102,3118,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3357 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3357 1776 5
  · have he : independentCachedBranchMembers3357.erase 1776=independentCachedBranchMembers3351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3351
  · have he : independentCachedBranchMembers3357.filter (independentCachedEdge 1776)=independentCachedBranchMembers3356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3356
def independentCachedBranchMembers3358 : Finset ℕ := ([80,252,1644,1678,1702,1714,1748,1768,2652,2710,2730,2776,2788,2800,3118,3164,3188,3222,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3358 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3358 5 (fun x => (if x<2730 then (if x<1714 then (if x<1644 then (if x<252 then 0 else 0) else (if x<1678 then 1 else (if x<1702 then 1 else 2))) else (if x<1768 then (if x<1748 then 3 else 0) else (if x<2652 then 2 else (if x<2710 then 0 else 1)))) else (if x<3164 then (if x<2788 then (if x<2776 then 2 else 2) else (if x<2800 then 2 else (if x<3118 then 0 else 4))) else (if x<3222 then (if x<3188 then 3 else 0) else (if x<3276 then 3 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3359 : Finset ℕ := ([252,1644,2710,2730,2776,2788,2800,3118,3164,3188] : List ℕ).toFinset
theorem independentCachedBranchBound3359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3359 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3359 4 (fun x => (if x<2788 then (if x<2710 then (if x<1644 then 0 else 0) else (if x<2730 then 1 else (if x<2776 then 1 else 1))) else (if x<3118 then (if x<2800 then 0 else 2) else (if x<3164 then 2 else (if x<3188 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3360 : Finset ℕ := ([80,252,1644,1678,1702,1714,1748,1768,2652,2710,2730,2776,2788,2800,3118,3164,3188,3222,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3360 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3360 3242 4
  · have he : independentCachedBranchMembers3360.erase 3242=independentCachedBranchMembers3358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3358
  · have he : independentCachedBranchMembers3360.filter (independentCachedEdge 3242)=independentCachedBranchMembers3359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3359
def independentCachedBranchMembers3361 : Finset ℕ := ([1644,1678,1714,2710,2730,2776,2788,3118,3164,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3361 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3361 4 (fun x => (if x<2776 then (if x<1714 then (if x<1678 then 0 else 0) else (if x<2710 then 1 else (if x<2730 then 0 else 1))) else (if x<3164 then (if x<2788 then 2 else (if x<3118 then 2 else 3)) else (if x<3276 then 1 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3362 : Finset ℕ := ([80,252,1644,1678,1702,1714,1748,1768,2652,2710,2730,2776,2788,2800,3118,3164,3188,3222,3242,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3362 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3362 3288 4
  · have he : independentCachedBranchMembers3362.erase 3288=independentCachedBranchMembers3360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3360
  · have he : independentCachedBranchMembers3362.filter (independentCachedEdge 3288)=independentCachedBranchMembers3361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3361
def independentCachedBranchMembers3363 : Finset ℕ := ([80,1702,2652,2776,2788,3118,3188,3222,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3363 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3363 4 (fun x => (if x<3118 then (if x<2652 then (if x<1702 then 0 else 0) else (if x<2776 then 0 else (if x<2788 then 1 else 1))) else (if x<3242 then (if x<3188 then 2 else (if x<3222 then 2 else 2)) else (if x<3276 then 0 else (if x<3312 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3364 : Finset ℕ := ([80,252,1644,1678,1702,1714,1748,1768,2652,2710,2730,2764,2776,2788,2800,3118,3164,3188,3222,3242,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3364 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3364 2764 4
  · have he : independentCachedBranchMembers3364.erase 2764=independentCachedBranchMembers3362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3362
  · have he : independentCachedBranchMembers3364.filter (independentCachedEdge 2764)=independentCachedBranchMembers3363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3363
def independentCachedBranchMembers3365 : Finset ℕ := ([252,1714,1768,2730,2776,2800,3118,3164,3188,3222,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3365 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3365 4 (fun x => (if x<2800 then (if x<1768 then (if x<1714 then 0 else 1) else (if x<2730 then 0 else (if x<2776 then 1 else 0))) else (if x<3188 then (if x<3118 then 1 else (if x<3164 then 2 else 2)) else (if x<3222 then 3 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3366 : Finset ℕ := ([80,252,1644,1678,1702,1714,1748,1768,2606,2652,2710,2730,2764,2776,2788,2800,3118,3164,3188,3222,3242,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3366 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3366 2606 4
  · have he : independentCachedBranchMembers3366.erase 2606=independentCachedBranchMembers3364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3364
  · have he : independentCachedBranchMembers3366.filter (independentCachedEdge 2606)=independentCachedBranchMembers3365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3365
def independentCachedBranchMembers3367 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1714,1748,1752,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2800,3102,3118,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3367 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3367 1686 5
  · have he : independentCachedBranchMembers3367.erase 1686=independentCachedBranchMembers3357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3357
  · have he : independentCachedBranchMembers3367.filter (independentCachedEdge 1686)=independentCachedBranchMembers3366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3366
def independentCachedBranchMembers3368 : Finset ℕ := ([72,80,130,1628,1678,1686,1752,2606,2614,2652,2680,2702,2710,2730,2738,2776,2788,3102,3180,3188,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3368 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3368 5 (fun x => (if x<2730 then (if x<1752 then (if x<1628 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1678 then 0 else (if x<1686 then 1 else 0))) else (if x<2652 then (if x<2606 then 1 else (if x<2614 then 1 else 2)) else (if x<2702 then (if x<2680 then 2 else 0) else (if x<2710 then 2 else 3)))) else (if x<3188 then (if x<2788 then (if x<2738 then 3 else (if x<2776 then 0 else 3)) else (if x<3102 then 2 else (if x<3180 then 2 else 0))) else (if x<3276 then (if x<3226 then 2 else (if x<3238 then 3 else 0)) else (if x<3304 then (if x<3284 then 2 else 3) else (if x<3312 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3369 : Finset ℕ := ([80,1628,1686,2606,2680,2702,2738,2776,2788,3102,3188,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3369 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3369 4 (fun x => (if x<2738 then (if x<2606 then (if x<1628 then 0 else (if x<1686 then 0 else 1)) else (if x<2680 then 2 else (if x<2702 then 0 else 1))) else (if x<3102 then (if x<2776 then 1 else (if x<2788 then 3 else 2)) else (if x<3284 then (if x<3188 then 2 else 0) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3370 : Finset ℕ := ([72,80,130,1628,1678,1686,1714,1752,2606,2614,2652,2680,2702,2710,2730,2738,2776,2788,3102,3180,3188,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3370 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3370 1714 4
  · have he : independentCachedBranchMembers3370.erase 1714=independentCachedBranchMembers3368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3368
  · have he : independentCachedBranchMembers3370.filter (independentCachedEdge 1714)=independentCachedBranchMembers3369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3369
def independentCachedBranchMembers3371 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1714,1748,1752,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2800,3102,3118,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3371 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3371 3300 5
  · have he : independentCachedBranchMembers3371.erase 3300=independentCachedBranchMembers3367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3367
  · have he : independentCachedBranchMembers3371.filter (independentCachedEdge 3300)=independentCachedBranchMembers3370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3370
def independentCachedBranchMembers3372 : Finset ℕ := ([80,130,252,1628,1644,1678,1776,2614,2652,2668,2680,2702,2714,2730,2772,2788,2800,3102,3118,3188,3222,3238,3250,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3372 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3372 5 (fun x => (if x<2730 then (if x<1776 then (if x<1628 then (if x<130 then 0 else (if x<252 then 0 else 1)) else (if x<1644 then 0 else (if x<1678 then 1 else 0))) else (if x<2668 then (if x<2614 then 1 else (if x<2652 then 2 else 2)) else (if x<2702 then (if x<2680 then 3 else 0) else (if x<2714 then 2 else 4)))) else (if x<3188 then (if x<2800 then (if x<2772 then 0 else (if x<2788 then 3 else 1)) else (if x<3102 then 4 else (if x<3118 then 2 else 3))) else (if x<3250 then (if x<3222 then 0 else (if x<3238 then 3 else 0)) else (if x<3288 then (if x<3276 then 4 else 2) else (if x<3304 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3373 : Finset ℕ := ([130,1628,1776,2614,2668,2680,2702,2772,3102,3238,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3373 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3373 4 (fun x => (if x<2702 then (if x<2614 then (if x<1628 then 0 else (if x<1776 then 0 else 1)) else (if x<2668 then 2 else (if x<2680 then 0 else 1))) else (if x<3238 then (if x<2772 then 2 else (if x<3102 then 1 else 2)) else (if x<3250 then 2 else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3374 : Finset ℕ := ([1628,1776,2668,2702,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3374 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3374 3 (fun x => (if x<2702 then (if x<1776 then 0 else (if x<2668 then 0 else 1)) else (if x<3238 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3375 : Finset ℕ := ([130,1628,1776,2614,2668,2680,2702,2714,2772,3102,3238,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3375 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3375 2714 3
  · have he : independentCachedBranchMembers3375.erase 2714=independentCachedBranchMembers3373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3373
  · have he : independentCachedBranchMembers3375.filter (independentCachedEdge 2714)=independentCachedBranchMembers3374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3374
def independentCachedBranchMembers3376 : Finset ℕ := ([80,130,252,1628,1644,1678,1748,1776,2614,2652,2668,2680,2702,2714,2730,2772,2788,2800,3102,3118,3188,3222,3238,3250,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3376 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3376 1748 4
  · have he : independentCachedBranchMembers3376.erase 1748=independentCachedBranchMembers3372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3372
  · have he : independentCachedBranchMembers3376.filter (independentCachedEdge 1748)=independentCachedBranchMembers3375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3375
def independentCachedBranchMembers3377 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1714,1748,1752,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2800,3102,3118,3126,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3377 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3377 3126 5
  · have he : independentCachedBranchMembers3377.erase 3126=independentCachedBranchMembers3371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3371
  · have he : independentCachedBranchMembers3377.filter (independentCachedEdge 3126)=independentCachedBranchMembers3376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3376
def independentCachedBranchMembers3378 : Finset ℕ := ([80,130,1594,1628,1652,1678,1702,1714,1748,1768,2614,2668,2680,2710,2730,2764,2776,2788,2800,3118,3164,3188,3226,3238,3250,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3378 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3378 5 (fun x => (if x<2710 then (if x<1702 then (if x<1628 then (if x<130 then 0 else (if x<1594 then 0 else 1)) else (if x<1652 then 0 else (if x<1678 then 1 else 0))) else (if x<1768 then (if x<1714 then 1 else (if x<1748 then 2 else 2)) else (if x<2668 then (if x<2614 then 1 else 1) else (if x<2680 then 3 else 0)))) else (if x<3164 then (if x<2776 then (if x<2730 then 2 else (if x<2764 then 0 else 2)) else (if x<2800 then (if x<2788 then 3 else 1) else (if x<3118 then 2 else 3))) else (if x<3238 then (if x<3188 then 3 else (if x<3226 then 0 else 3)) else (if x<3284 then (if x<3250 then 0 else 4) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3379 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1714,1748,1752,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3379 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3379 2792 5
  · have he : independentCachedBranchMembers3379.erase 2792=independentCachedBranchMembers3377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3377
  · have he : independentCachedBranchMembers3379.filter (independentCachedEdge 2792)=independentCachedBranchMembers3378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3378
def independentCachedBranchMembers3380 : Finset ℕ := ([80,130,1594,1628,1644,1678,1714,1748,1752,1768,2606,2680,2710,2714,2730,2764,2800,3118,3188,3192,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3380 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3380 5 (fun x => (if x<2714 then (if x<1714 then (if x<1628 then (if x<130 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 0 else (if x<1678 then 1 else 0))) else (if x<1768 then (if x<1748 then 2 else (if x<1752 then 2 else 1)) else (if x<2680 then (if x<2606 then 2 else 1) else (if x<2710 then 0 else 2)))) else (if x<3192 then (if x<2800 then (if x<2730 then 1 else (if x<2764 then 0 else 1)) else (if x<3118 then 2 else (if x<3188 then 3 else 0))) else (if x<3238 then (if x<3222 then 3 else (if x<3226 then 4 else 3)) else (if x<3276 then (if x<3242 then 0 else 4) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3381 : Finset ℕ := ([80,130,1644,1714,1748,1752,2680,2730,2764,3118,3222,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3381 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3381 4 (fun x => (if x<2680 then (if x<1714 then (if x<130 then 0 else (if x<1644 then 0 else 1)) else (if x<1748 then 2 else (if x<1752 then 1 else 2))) else (if x<3118 then (if x<2730 then 0 else (if x<2764 then 0 else 1)) else (if x<3226 then (if x<3222 then 3 else 3) else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3382 : Finset ℕ := ([80,130,1594,1628,1644,1678,1714,1748,1752,1768,2606,2680,2710,2714,2730,2764,2800,3102,3118,3188,3192,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3382 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3382 3102 4
  · have he : independentCachedBranchMembers3382.erase 3102=independentCachedBranchMembers3380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3380
  · have he : independentCachedBranchMembers3382.filter (independentCachedEdge 3102)=independentCachedBranchMembers3381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3381
def independentCachedBranchMembers3383 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1714,1740,1748,1752,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3383 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3383 1740 5
  · have he : independentCachedBranchMembers3383.erase 1740=independentCachedBranchMembers3379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3379
  · have he : independentCachedBranchMembers3383.filter (independentCachedEdge 1740)=independentCachedBranchMembers3382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3382
def independentCachedBranchMembers3384 : Finset ℕ := ([72,80,130,1628,1644,1652,1678,1686,1702,1714,2652,2668,2680,2702,2714,2730,2738,3164,3180,3188,3192,3222,3226,3238,3242,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3384 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3384 5 (fun x => (if x<2702 then (if x<1678 then (if x<1628 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1644 then 0 else (if x<1652 then 2 else 1))) else (if x<1714 then (if x<1686 then 2 else (if x<1702 then 0 else 1)) else (if x<2668 then (if x<2652 then 3 else 1) else (if x<2680 then 0 else 2)))) else (if x<3188 then (if x<2738 then (if x<2714 then 1 else (if x<2730 then 2 else 3)) else (if x<3164 then 4 else (if x<3180 then 3 else 4))) else (if x<3226 then (if x<3192 then 2 else (if x<3222 then 0 else 2)) else (if x<3242 then (if x<3238 then 3 else 4) else (if x<3250 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3385 : Finset ℕ := ([80,1628,1652,1686,2668,2680,2702,2714,2738,3164,3188,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound3385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3385 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3385 4 (fun x => (if x<2702 then (if x<1686 then (if x<1628 then 0 else (if x<1652 then 0 else 1)) else (if x<2668 then 1 else (if x<2680 then 1 else 0))) else (if x<3164 then (if x<2714 then 1 else (if x<2738 then 2 else 3)) else (if x<3222 then (if x<3188 then 3 else 0) else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3386 : Finset ℕ := ([72,80,130,1628,1644,1652,1678,1686,1702,1714,2652,2668,2680,2702,2710,2714,2730,2738,3164,3180,3188,3192,3222,3226,3238,3242,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3386 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3386 2710 4
  · have he : independentCachedBranchMembers3386.erase 2710=independentCachedBranchMembers3384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3384
  · have he : independentCachedBranchMembers3386.filter (independentCachedEdge 2710)=independentCachedBranchMembers3385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3385
def independentCachedBranchMembers3387 : Finset ℕ := ([72,80,130,192,252,1594,1628,1644,1652,1678,1686,1702,1714,1740,1748,1752,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3387 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3387 192 5
  · have he : independentCachedBranchMembers3387.erase 192=independentCachedBranchMembers3383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3383
  · have he : independentCachedBranchMembers3387.filter (independentCachedEdge 192)=independentCachedBranchMembers3386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3386
def independentCachedBranchMembers3388 : Finset ℕ := ([80,130,252,1628,1652,1678,1702,1748,1752,1776,2606,2652,2680,2702,2730,2772,2776,2800,3118,3164,3188,3192,3238,3242,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3388 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3388 5 (fun x => (if x<2702 then (if x<1702 then (if x<1628 then (if x<130 then 0 else (if x<252 then 0 else 1)) else (if x<1652 then 0 else (if x<1678 then 1 else 0))) else (if x<1776 then (if x<1748 then 2 else (if x<1752 then 2 else 1)) else (if x<2652 then (if x<2606 then 3 else 2) else (if x<2680 then 1 else 0)))) else (if x<3188 then (if x<2776 then (if x<2730 then 3 else (if x<2772 then 0 else 3)) else (if x<3118 then (if x<2800 then 4 else 1) else (if x<3164 then 3 else 4))) else (if x<3242 then (if x<3192 then 0 else (if x<3238 then 1 else 0)) else (if x<3288 then (if x<3284 then 2 else 1) else (if x<3312 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3389 : Finset ℕ := ([18,72,80,130,192,252,1594,1628,1644,1652,1678,1686,1702,1714,1740,1748,1752,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3389 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3389 18 5
  · have he : independentCachedBranchMembers3389.erase 18=independentCachedBranchMembers3387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3387
  · have he : independentCachedBranchMembers3389.filter (independentCachedEdge 18)=independentCachedBranchMembers3388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3388
def independentCachedBranchMembers3390 : Finset ℕ := ([80,130,1594,1644,1652,1702,1748,1768,1776,2614,2652,2680,2702,2730,2788,3118,3192,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3390 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3390 5 (fun x => (if x<2680 then (if x<1702 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1644 then 1 else (if x<1652 then 1 else 0))) else (if x<1776 then (if x<1748 then 0 else (if x<1768 then 2 else 2)) else (if x<2614 then 1 else (if x<2652 then 3 else 0)))) else (if x<3192 then (if x<2730 then (if x<2702 then 1 else 0) else (if x<2788 then 2 else (if x<3118 then 1 else 3))) else (if x<3250 then (if x<3222 then 0 else (if x<3242 then 3 else 0)) else (if x<3288 then 4 else (if x<3300 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3391 : Finset ℕ := ([1594,1768,1776,2614,2652,2702,2788,3192,3242,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3391 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3391 4 (fun x => (if x<2702 then (if x<1776 then (if x<1768 then 0 else 0) else (if x<2614 then 1 else (if x<2652 then 0 else 2))) else (if x<3242 then (if x<2788 then 1 else (if x<3192 then 0 else 1)) else (if x<3250 then 2 else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3392 : Finset ℕ := ([80,130,1594,1644,1652,1702,1748,1768,1776,2614,2652,2680,2702,2730,2788,3118,3164,3192,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3392 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3392 3164 4
  · have he : independentCachedBranchMembers3392.erase 3164=independentCachedBranchMembers3390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3390
  · have he : independentCachedBranchMembers3392.filter (independentCachedEdge 3164)=independentCachedBranchMembers3391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3391
def independentCachedBranchMembers3393 : Finset ℕ := ([80,1594,1652,1748,1776,2702,2730,2788,3118,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3393 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3393 4 (fun x => (if x<2702 then (if x<1652 then (if x<1594 then 0 else 1) else (if x<1748 then 0 else (if x<1776 then 2 else 1))) else (if x<3118 then (if x<2730 then 0 else (if x<2788 then 2 else 1)) else (if x<3242 then 2 else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3394 : Finset ℕ := ([72,80,130,1594,1644,1652,1702,1748,1768,1776,2614,2652,2680,2702,2730,2788,3118,3164,3192,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3394 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3394 72 4
  · have he : independentCachedBranchMembers3394.erase 72=independentCachedBranchMembers3392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3392
  · have he : independentCachedBranchMembers3394.filter (independentCachedEdge 72)=independentCachedBranchMembers3393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3393
def independentCachedBranchMembers3395 : Finset ℕ := ([130,1594,1644,1652,2614,2652,2680,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3395 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3395 4 (fun x => (if x<2680 then (if x<1652 then (if x<1594 then 0 else (if x<1644 then 1 else 0)) else (if x<2614 then 1 else (if x<2652 then 1 else 0))) else (if x<3250 then (if x<3222 then 1 else (if x<3242 then 2 else 2)) else (if x<3288 then 0 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3396 : Finset ℕ := ([72,80,130,1594,1644,1652,1702,1748,1768,1776,2614,2652,2680,2702,2730,2776,2788,3118,3164,3192,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3396 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3396 2776 4
  · have he : independentCachedBranchMembers3396.erase 2776=independentCachedBranchMembers3394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3394
  · have he : independentCachedBranchMembers3396.filter (independentCachedEdge 2776)=independentCachedBranchMembers3395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3395
def independentCachedBranchMembers3397 : Finset ℕ := ([80,1652,1748,1768,2614,2652,2730,3118,3192,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3397 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3397 4 (fun x => (if x<2730 then (if x<1768 then (if x<1652 then 0 else (if x<1748 then 0 else 1)) else (if x<2614 then 1 else (if x<2652 then 2 else 0))) else (if x<3250 then (if x<3118 then 1 else (if x<3192 then 2 else 0)) else (if x<3288 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3398 : Finset ℕ := ([72,80,130,1594,1644,1652,1702,1748,1768,1776,2614,2652,2680,2702,2730,2738,2776,2788,3118,3164,3192,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3398 2738 4
  · have he : independentCachedBranchMembers3398.erase 2738=independentCachedBranchMembers3396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3396
  · have he : independentCachedBranchMembers3398.filter (independentCachedEdge 2738)=independentCachedBranchMembers3397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3397
def independentCachedBranchMembers3399 : Finset ℕ := ([80,130,1594,1644,1748,1768,2680,2730,3118,3192,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound3399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3399 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3399 4 (fun x => (if x<2680 then (if x<1644 then (if x<130 then 0 else (if x<1594 then 0 else 1)) else (if x<1748 then 1 else (if x<1768 then 2 else 2))) else (if x<3192 then (if x<2730 then 0 else (if x<3118 then 0 else 1)) else (if x<3222 then 1 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3400 : Finset ℕ := ([72,80,130,1594,1644,1652,1702,1740,1748,1768,1776,2614,2652,2680,2702,2730,2738,2776,2788,3118,3164,3192,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3400 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3400 1740 4
  · have he : independentCachedBranchMembers3400.erase 1740=independentCachedBranchMembers3398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3398
  · have he : independentCachedBranchMembers3400.filter (independentCachedEdge 1740)=independentCachedBranchMembers3399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3399
def independentCachedBranchMembers3401 : Finset ℕ := ([80,1644,1748,1776,2614,2652,2680,2702,2730,2788,3118,3222,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3401 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3401 4 (fun x => (if x<2702 then (if x<1776 then (if x<1644 then 0 else (if x<1748 then 1 else 0)) else (if x<2652 then (if x<2614 then 1 else 2) else (if x<2680 then 0 else 1))) else (if x<3118 then (if x<2730 then 2 else (if x<2788 then 3 else 1)) else (if x<3250 then (if x<3222 then 2 else 2) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3402 : Finset ℕ := ([1748,1776,2614,2788,3118,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3402 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3402 3 (fun x => (if x<2788 then (if x<1776 then 0 else (if x<2614 then 1 else 2)) else (if x<3118 then 0 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3403 : Finset ℕ := ([80,130,1644,1748,1776,2614,2652,2680,2702,2730,2788,3118,3222,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3403 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3403 130 3
  · have he : independentCachedBranchMembers3403.erase 130=independentCachedBranchMembers3401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3401
  · have he : independentCachedBranchMembers3403.filter (independentCachedEdge 130)=independentCachedBranchMembers3402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3402
def independentCachedBranchMembers3404 : Finset ℕ := ([72,80,130,1594,1644,1652,1702,1740,1748,1768,1776,2614,2652,2680,2702,2730,2738,2776,2788,3118,3126,3164,3192,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3404 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3404 3126 4
  · have he : independentCachedBranchMembers3404.erase 3126=independentCachedBranchMembers3400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3400
  · have he : independentCachedBranchMembers3404.filter (independentCachedEdge 3126)=independentCachedBranchMembers3403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3403
def independentCachedBranchMembers3405 : Finset ℕ := ([1594,1652,1740,1776,2614,2680,2702,2738,3118,3164,3222,3242,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3405 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3405 4 (fun x => (if x<2738 then (if x<1776 then (if x<1652 then 0 else (if x<1740 then 0 else 1)) else (if x<2680 then (if x<2614 then 1 else 0) else (if x<2702 then 0 else 1))) else (if x<3222 then (if x<3118 then 1 else (if x<3164 then 2 else 2)) else (if x<3288 then (if x<3242 then 2 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3406 : Finset ℕ := ([1594,1740,2614,2738,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3406 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3406 3 (fun x => (if x<2738 then (if x<1740 then 0 else (if x<2614 then 1 else 0)) else (if x<3222 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3407 : Finset ℕ := ([80,1594,1652,1740,1776,2614,2680,2702,2738,3118,3164,3222,3242,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3407 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3407 80 3
  · have he : independentCachedBranchMembers3407.erase 80=independentCachedBranchMembers3405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3405
  · have he : independentCachedBranchMembers3407.filter (independentCachedEdge 80)=independentCachedBranchMembers3406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3406
def independentCachedBranchMembers3408 : Finset ℕ := ([72,80,130,1594,1644,1652,1702,1740,1748,1768,1776,2614,2652,2680,2702,2710,2730,2738,2776,2788,3118,3126,3164,3192,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3408 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3408 2710 4
  · have he : independentCachedBranchMembers3408.erase 2710=independentCachedBranchMembers3404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3404
  · have he : independentCachedBranchMembers3408.filter (independentCachedEdge 2710)=independentCachedBranchMembers3407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3407
def independentCachedBranchMembers3409 : Finset ℕ := ([72,130,1652,1740,1768,2614,2702,2730,2776,3118,3164,3192,3222,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3409 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3409 4 (fun x => (if x<2730 then (if x<1740 then (if x<130 then 0 else (if x<1652 then 0 else 1)) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2702 then 1 else 1))) else (if x<3192 then (if x<3118 then (if x<2776 then 2 else 2) else (if x<3164 then 3 else 0)) else (if x<3250 then (if x<3222 then 3 else 0) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3410 : Finset ℕ := ([72,80,130,1594,1644,1652,1702,1740,1748,1768,1776,2606,2614,2652,2680,2702,2710,2730,2738,2776,2788,3118,3126,3164,3192,3222,3242,3250,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3410 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3410 2606 4
  · have he : independentCachedBranchMembers3410.erase 2606=independentCachedBranchMembers3408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3408
  · have he : independentCachedBranchMembers3410.filter (independentCachedEdge 2606)=independentCachedBranchMembers3409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3409
def independentCachedBranchMembers3411 : Finset ℕ := ([18,72,80,130,192,252,1594,1628,1644,1652,1678,1686,1702,1714,1740,1748,1752,1764,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3411 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3411 1764 5
  · have he : independentCachedBranchMembers3411.erase 1764=independentCachedBranchMembers3389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3389
  · have he : independentCachedBranchMembers3411.filter (independentCachedEdge 1764)=independentCachedBranchMembers3410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3410
def independentCachedBranchMembers3412 : Finset ℕ := ([80,130,252,1594,1652,1686,1702,1740,1752,1768,2614,2652,2680,2702,2772,2788,3126,3164,3180,3192,3226,3242,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3412 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3412 5 (fun x => (if x<2680 then (if x<1702 then (if x<1594 then (if x<130 then 0 else (if x<252 then 0 else 1)) else (if x<1652 then 2 else (if x<1686 then 0 else 2))) else (if x<1768 then (if x<1740 then 0 else (if x<1752 then 1 else 2)) else (if x<2614 then 3 else (if x<2652 then 2 else 0)))) else (if x<3180 then (if x<2788 then (if x<2702 then 2 else (if x<2772 then 0 else 1)) else (if x<3126 then 3 else (if x<3164 then 4 else 1))) else (if x<3242 then (if x<3192 then 3 else (if x<3226 then 0 else 4)) else (if x<3284 then 0 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3413 : Finset ℕ := ([252,1686,1740,1752,2652,2702,2772,3126,3180,3192,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3413 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3413 4 (fun x => (if x<2772 then (if x<1752 then (if x<1686 then 0 else (if x<1740 then 1 else 0)) else (if x<2652 then 1 else (if x<2702 then 0 else 2))) else (if x<3192 then (if x<3126 then 1 else (if x<3180 then 3 else 0)) else (if x<3242 then 2 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3414 : Finset ℕ := ([80,130,252,1594,1652,1686,1702,1740,1752,1768,2614,2652,2680,2702,2730,2772,2788,3126,3164,3180,3192,3226,3242,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3414 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3414 2730 4
  · have he : independentCachedBranchMembers3414.erase 2730=independentCachedBranchMembers3412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3412
  · have he : independentCachedBranchMembers3414.filter (independentCachedEdge 2730)=independentCachedBranchMembers3413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3413
def independentCachedBranchMembers3415 : Finset ℕ := ([80,1594,1702,1752,2652,2680,2788,3126,3180,3242,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3415 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3415 4 (fun x => (if x<2788 then (if x<1752 then (if x<1594 then 0 else (if x<1702 then 1 else 0)) else (if x<2652 then 1 else (if x<2680 then 0 else 1))) else (if x<3242 then (if x<3126 then 2 else (if x<3180 then 3 else 2)) else (if x<3284 then 0 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3416 : Finset ℕ := ([80,130,252,1594,1652,1686,1702,1740,1752,1768,2614,2652,2668,2680,2702,2730,2772,2788,3126,3164,3180,3192,3226,3242,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3416 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3416 2668 4
  · have he : independentCachedBranchMembers3416.erase 2668=independentCachedBranchMembers3414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3414
  · have he : independentCachedBranchMembers3416.filter (independentCachedEdge 2668)=independentCachedBranchMembers3415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3415
def independentCachedBranchMembers3417 : Finset ℕ := ([80,252,1594,1686,1702,1740,2680,2702,2772,2788,3192,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3417 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3417 4 (fun x => (if x<2680 then (if x<1686 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1702 then 1 else (if x<1740 then 2 else 2))) else (if x<2788 then (if x<2702 then 0 else (if x<2772 then 2 else 0)) else (if x<3192 then 2 else (if x<3284 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3418 : Finset ℕ := ([80,130,252,1594,1652,1686,1702,1714,1740,1752,1768,2614,2652,2668,2680,2702,2730,2772,2788,3126,3164,3180,3192,3226,3242,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3418 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3418 1714 4
  · have he : independentCachedBranchMembers3418.erase 1714=independentCachedBranchMembers3416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3416
  · have he : independentCachedBranchMembers3418.filter (independentCachedEdge 1714)=independentCachedBranchMembers3417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3417
def independentCachedBranchMembers3419 : Finset ℕ := ([130,1686,1714,1752,2614,2652,2680,2702,2730,2788,3180,3226,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3419 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3419 4 (fun x => (if x<2702 then (if x<1752 then (if x<1686 then 0 else (if x<1714 then 0 else 1)) else (if x<2652 then (if x<2614 then 1 else 1) else (if x<2680 then 1 else 0))) else (if x<3180 then (if x<2730 then 2 else (if x<2788 then 3 else 2)) else (if x<3284 then (if x<3226 then 0 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3420 : Finset ℕ := ([1686,1714,2614,2788,3180,3226] : List ℕ).toFinset
theorem independentCachedBranchBound3420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3420 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3420 3 (fun x => (if x<2788 then (if x<1714 then 0 else (if x<2614 then 1 else 0)) else (if x<3180 then 2 else (if x<3226 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3421 : Finset ℕ := ([80,130,1686,1714,1752,2614,2652,2680,2702,2730,2788,3180,3226,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3421 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3421 80 3
  · have he : independentCachedBranchMembers3421.erase 80=independentCachedBranchMembers3419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3419
  · have he : independentCachedBranchMembers3421.filter (independentCachedEdge 80)=independentCachedBranchMembers3420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3420
def independentCachedBranchMembers3422 : Finset ℕ := ([80,130,252,1594,1652,1686,1702,1714,1740,1752,1768,2614,2652,2668,2680,2702,2730,2772,2788,3126,3164,3180,3192,3226,3242,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3422 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3422 3300 4
  · have he : independentCachedBranchMembers3422.erase 3300=independentCachedBranchMembers3418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3418
  · have he : independentCachedBranchMembers3422.filter (independentCachedEdge 3300)=independentCachedBranchMembers3421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3421
def independentCachedBranchMembers3423 : Finset ℕ := ([1594,1686,1702,1740,2680,2702,2772,2788,3126,3164,3180,3226,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3423 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3423 4 (fun x => (if x<2788 then (if x<1740 then (if x<1686 then 0 else (if x<1702 then 0 else 1)) else (if x<2702 then (if x<2680 then 1 else 0) else (if x<2772 then 1 else 0))) else (if x<3180 then (if x<3126 then 1 else (if x<3164 then 2 else 2)) else (if x<3242 then (if x<3226 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3424 : Finset ℕ := ([1594,1740,2772,2788,3126,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3424 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3424 3 (fun x => (if x<2788 then (if x<1740 then 0 else (if x<2772 then 1 else 0)) else (if x<3126 then 1 else (if x<3312 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3425 : Finset ℕ := ([130,1594,1686,1702,1740,2680,2702,2772,2788,3126,3164,3180,3226,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3425 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3425 130 3
  · have he : independentCachedBranchMembers3425.erase 130=independentCachedBranchMembers3423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3423
  · have he : independentCachedBranchMembers3425.filter (independentCachedEdge 130)=independentCachedBranchMembers3424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3424
def independentCachedBranchMembers3426 : Finset ℕ := ([80,130,252,1594,1652,1686,1702,1714,1740,1752,1768,2614,2652,2668,2680,2702,2730,2772,2788,2800,3126,3164,3180,3192,3226,3242,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3426 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3426 2800 4
  · have he : independentCachedBranchMembers3426.erase 2800=independentCachedBranchMembers3422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3422
  · have he : independentCachedBranchMembers3426.filter (independentCachedEdge 2800)=independentCachedBranchMembers3425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3425
def independentCachedBranchMembers3427 : Finset ℕ := ([80,252,1702,1740,1768,2668,2702,2730,2788,3126,3164,3192,3226,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3427 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3427 4 (fun x => (if x<2730 then (if x<1740 then (if x<252 then 0 else (if x<1702 then 0 else 1)) else (if x<2668 then (if x<1768 then 1 else 2) else (if x<2702 then 2 else 1))) else (if x<3192 then (if x<3126 then (if x<2788 then 2 else 1) else (if x<3164 then 3 else 0)) else (if x<3284 then (if x<3226 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3428 : Finset ℕ := ([80,130,252,1594,1652,1686,1702,1714,1740,1752,1768,2614,2652,2668,2680,2702,2714,2730,2772,2788,2800,3126,3164,3180,3192,3226,3242,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3428 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3428 2714 4
  · have he : independentCachedBranchMembers3428.erase 2714=independentCachedBranchMembers3426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3426
  · have he : independentCachedBranchMembers3428.filter (independentCachedEdge 2714)=independentCachedBranchMembers3427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3427
def independentCachedBranchMembers3429 : Finset ℕ := ([18,72,80,130,192,252,1590,1594,1628,1644,1652,1678,1686,1702,1714,1740,1748,1752,1764,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3429 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3429 1590 5
  · have he : independentCachedBranchMembers3429.erase 1590=independentCachedBranchMembers3411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3411
  · have he : independentCachedBranchMembers3429.filter (independentCachedEdge 1590)=independentCachedBranchMembers3428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3428
def independentCachedBranchMembers3430 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1752,1768,1776,2652,2668,2702,2710,2776,2800,3102,3118,3192,3226,3250,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3430 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3430 5 (fun x => (if x<1776 then (if x<1644 then (if x<252 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1594 then 1 else (if x<1628 then 2 else 0))) else (if x<1686 then (if x<1652 then 2 else (if x<1678 then 1 else 2)) else (if x<1752 then (if x<1702 then 0 else 3) else (if x<1768 then 1 else 3)))) else (if x<3102 then (if x<2702 then (if x<2652 then 4 else (if x<2668 then 1 else 0)) else (if x<2776 then (if x<2710 then 4 else 3) else (if x<2800 then 3 else 1))) else (if x<3226 then (if x<3118 then 4 else (if x<3192 then 2 else 0)) else (if x<3276 then (if x<3250 then 2 else 0) else (if x<3284 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3431 : Finset ℕ := ([72,252,1644,1686,1752,1776,2668,2710,2776,2800,3118,3226,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3431 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3431 4 (fun x => (if x<2710 then (if x<1686 then (if x<252 then 0 else (if x<1644 then 0 else 0)) else (if x<1776 then (if x<1752 then 1 else 0) else (if x<2668 then 1 else 2))) else (if x<3118 then (if x<2776 then 3 else (if x<2800 then 2 else 3)) else (if x<3250 then (if x<3226 then 2 else 2) else (if x<3284 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3432 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1752,1768,1776,2652,2668,2702,2710,2776,2800,3102,3118,3192,3226,3242,3250,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3432 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3432 3242 4
  · have he : independentCachedBranchMembers3432.erase 3242=independentCachedBranchMembers3430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3430
  · have he : independentCachedBranchMembers3432.filter (independentCachedEdge 3242)=independentCachedBranchMembers3431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3431
def independentCachedBranchMembers3433 : Finset ℕ := ([72,80,130,1628,1678,1686,1752,2652,2702,2710,2776,3102,3226,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3433 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3433 4 (fun x => (if x<2652 then (if x<1628 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1686 then (if x<1678 then 0 else 1) else (if x<1752 then 0 else 1))) else (if x<3102 then (if x<2710 then (if x<2702 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3276 then (if x<3226 then 2 else 3) else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3434 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1752,1768,1776,2652,2668,2702,2710,2776,2800,3102,3118,3192,3226,3242,3250,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3434 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3434 3300 4
  · have he : independentCachedBranchMembers3434.erase 3300=independentCachedBranchMembers3432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3432
  · have he : independentCachedBranchMembers3434.filter (independentCachedEdge 3300)=independentCachedBranchMembers3433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3433
def independentCachedBranchMembers3435 : Finset ℕ := ([80,130,252,1628,1644,1678,1776,2652,2668,2702,2800,3102,3118,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3435 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3435 4 (fun x => (if x<2652 then (if x<1628 then (if x<130 then 0 else (if x<252 then 0 else 1)) else (if x<1678 then (if x<1644 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3102 then (if x<2702 then (if x<2668 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3250 then (if x<3118 then 2 else 3) else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3436 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1752,1768,1776,2652,2668,2702,2710,2776,2800,3102,3118,3126,3192,3226,3242,3250,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3436 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3436 3126 4
  · have he : independentCachedBranchMembers3436.erase 3126=independentCachedBranchMembers3434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3434
  · have he : independentCachedBranchMembers3436.filter (independentCachedEdge 3126)=independentCachedBranchMembers3435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3435
def independentCachedBranchMembers3437 : Finset ℕ := ([80,130,1594,1628,1652,1678,1702,1768,2668,2710,2776,2800,3118,3226,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3437 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3437 4 (fun x => (if x<2668 then (if x<1652 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else 0)) else (if x<1702 then (if x<1678 then 1 else 0) else (if x<1768 then 1 else 1))) else (if x<3118 then (if x<2776 then (if x<2710 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3250 then (if x<3226 then 2 else 2) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3438 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1752,1768,1776,2652,2668,2702,2710,2776,2792,2800,3102,3118,3126,3192,3226,3242,3250,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3438 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3438 2792 4
  · have he : independentCachedBranchMembers3438.erase 2792=independentCachedBranchMembers3436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3436
  · have he : independentCachedBranchMembers3438.filter (independentCachedEdge 2792)=independentCachedBranchMembers3437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3437
def independentCachedBranchMembers3439 : Finset ℕ := ([18,72,80,130,192,252,1590,1594,1628,1644,1652,1678,1686,1702,1714,1740,1748,1752,1764,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3439 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3439 3130 5
  · have he : independentCachedBranchMembers3439.erase 3130=independentCachedBranchMembers3429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3429
  · have he : independentCachedBranchMembers3439.filter (independentCachedEdge 3130)=independentCachedBranchMembers3438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3438
def independentCachedBranchMembers3440 : Finset ℕ := ([72,252,1594,1644,1652,1678,1686,1714,1752,1764,2614,2652,2680,2714,2764,2800,3192,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3440 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3440 5 (fun x => (if x<2652 then (if x<1678 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1644 then 1 else (if x<1652 then 0 else 1))) else (if x<1752 then (if x<1686 then 2 else (if x<1714 then 1 else 2)) else (if x<1764 then 0 else (if x<2614 then 2 else 1)))) else (if x<3226 then (if x<2764 then (if x<2680 then 0 else (if x<2714 then 1 else 1)) else (if x<2800 then 2 else (if x<3192 then 2 else 0))) else (if x<3284 then (if x<3238 then 3 else (if x<3276 then 3 else 0)) else (if x<3304 then 3 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3441 : Finset ℕ := ([252,1644,1678,1764,2614,2652,2680,2714,2800,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3441 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3441 4 (fun x => (if x<2680 then (if x<1764 then (if x<1644 then 0 else (if x<1678 then 0 else 1)) else (if x<2614 then 1 else (if x<2652 then 2 else 0))) else (if x<3238 then (if x<2714 then 2 else (if x<2800 then 1 else 1)) else (if x<3276 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3442 : Finset ℕ := ([72,252,1594,1644,1652,1678,1686,1714,1752,1764,2614,2652,2680,2714,2764,2800,3126,3192,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3442 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3442 3126 4
  · have he : independentCachedBranchMembers3442.erase 3126=independentCachedBranchMembers3440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3440
  · have he : independentCachedBranchMembers3442.filter (independentCachedEdge 3126)=independentCachedBranchMembers3441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3441
def independentCachedBranchMembers3443 : Finset ℕ := ([1594,1652,1678,1714,2614,2680,2764,2800,3226,3238,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3443 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3443 4 (fun x => (if x<2764 then (if x<1714 then (if x<1652 then 0 else (if x<1678 then 0 else 1)) else (if x<2614 then 1 else (if x<2680 then 0 else 0))) else (if x<3238 then (if x<2800 then 1 else (if x<3226 then 1 else 2)) else (if x<3284 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3444 : Finset ℕ := ([72,252,1594,1644,1652,1678,1686,1714,1752,1764,2614,2652,2680,2714,2764,2792,2800,3126,3192,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3444 2792 4
  · have he : independentCachedBranchMembers3444.erase 2792=independentCachedBranchMembers3442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3442
  · have he : independentCachedBranchMembers3444.filter (independentCachedEdge 2792)=independentCachedBranchMembers3443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3443
def independentCachedBranchMembers3445 : Finset ℕ := ([72,252,1652,1686,1714,1764,2614,2800,3192,3226,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3445 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3445 4 (fun x => (if x<2614 then (if x<1686 then (if x<252 then 0 else (if x<1652 then 0 else 1)) else (if x<1714 then 1 else (if x<1764 then 2 else 2))) else (if x<3226 then (if x<2800 then 1 else (if x<3192 then 2 else 0)) else (if x<3276 then 3 else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3446 : Finset ℕ := ([72,252,1594,1644,1652,1678,1686,1714,1752,1764,2606,2614,2652,2680,2714,2764,2792,2800,3126,3192,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3446 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3446 2606 4
  · have he : independentCachedBranchMembers3446.erase 2606=independentCachedBranchMembers3444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3444
  · have he : independentCachedBranchMembers3446.filter (independentCachedEdge 2606)=independentCachedBranchMembers3445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3445
def independentCachedBranchMembers3447 : Finset ℕ := ([72,1644,1652,1678,1686,1714,2652,2680,2714,3192,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound3447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3447 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3447 4 (fun x => (if x<2652 then (if x<1678 then (if x<1644 then 0 else (if x<1652 then 0 else 1)) else (if x<1686 then 2 else (if x<1714 then 1 else 2))) else (if x<3192 then (if x<2680 then 0 else (if x<2714 then 1 else 1)) else (if x<3226 then 0 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3448 : Finset ℕ := ([72,192,252,1594,1644,1652,1678,1686,1714,1752,1764,2606,2614,2652,2680,2714,2764,2792,2800,3126,3192,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3448 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3448 192 4
  · have he : independentCachedBranchMembers3448.erase 192=independentCachedBranchMembers3446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3446
  · have he : independentCachedBranchMembers3448.filter (independentCachedEdge 192)=independentCachedBranchMembers3447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3447
def independentCachedBranchMembers3449 : Finset ℕ := ([72,1644,1678,1714,2606,2652,2764,2800,3126,3192,3226,3238,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3449 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3449 4 (fun x => (if x<2800 then (if x<1714 then (if x<1644 then 0 else (if x<1678 then 0 else 1)) else (if x<2652 then (if x<2606 then 1 else 2) else (if x<2764 then 0 else 1))) else (if x<3226 then (if x<3126 then 1 else (if x<3192 then 2 else 0)) else (if x<3284 then (if x<3238 then 3 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3450 : Finset ℕ := ([72,192,252,1594,1644,1652,1678,1686,1714,1752,1764,2606,2614,2652,2680,2714,2764,2772,2792,2800,3126,3192,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3450 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3450 2772 4
  · have he : independentCachedBranchMembers3450.erase 2772=independentCachedBranchMembers3448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3448
  · have he : independentCachedBranchMembers3450.filter (independentCachedEdge 2772)=independentCachedBranchMembers3449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3449
def independentCachedBranchMembers3451 : Finset ℕ := ([192,1594,1678,1686,1764,2606,2614,2652,2714,2792,2800,3192,3238,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3451 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3451 4 (fun x => (if x<2652 then (if x<1686 then (if x<1594 then 0 else (if x<1678 then 0 else 1)) else (if x<2606 then (if x<1764 then 2 else 1) else (if x<2614 then 0 else 2))) else (if x<3192 then (if x<2792 then (if x<2714 then 3 else 1) else (if x<2800 then 3 else 1)) else (if x<3276 then (if x<3238 then 3 else 2) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3452 : Finset ℕ := ([72,192,252,1594,1644,1652,1678,1686,1714,1752,1764,2606,2614,2652,2680,2714,2764,2772,2792,2800,3126,3164,3192,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3452 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3452 3164 4
  · have he : independentCachedBranchMembers3452.erase 3164=independentCachedBranchMembers3450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3450
  · have he : independentCachedBranchMembers3452.filter (independentCachedEdge 3164)=independentCachedBranchMembers3451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3451
def independentCachedBranchMembers3453 : Finset ℕ := ([72,192,1594,1644,1686,1714,1764,2614,2714,2764,2792,3126,3226,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3453 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3453 4 (fun x => (if x<2614 then (if x<1644 then (if x<192 then 0 else (if x<1594 then 1 else 1)) else (if x<1714 then (if x<1686 then 0 else 2) else (if x<1764 then 3 else 2))) else (if x<3126 then (if x<2764 then (if x<2714 then 1 else 2) else (if x<2792 then 0 else 2)) else (if x<3276 then (if x<3226 then 3 else 3) else (if x<3304 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3454 : Finset ℕ := ([72,80,192,252,1594,1644,1652,1678,1686,1714,1752,1764,2606,2614,2652,2680,2714,2764,2772,2792,2800,3126,3164,3192,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3454 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3454 80 4
  · have he : independentCachedBranchMembers3454.erase 80=independentCachedBranchMembers3452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3452
  · have he : independentCachedBranchMembers3454.filter (independentCachedEdge 80)=independentCachedBranchMembers3453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3453
def independentCachedBranchMembers3455 : Finset ℕ := ([252,1652,1686,1714,1764,2606,2652,2680,2714,2764,2792,3126,3238,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3455 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3455 4 (fun x => (if x<2680 then (if x<1714 then (if x<1652 then 0 else (if x<1686 then 0 else 1)) else (if x<2606 then (if x<1764 then 2 else 1) else (if x<2652 then 3 else 0))) else (if x<3126 then (if x<2764 then (if x<2714 then 3 else 1) else (if x<2792 then 2 else 1)) else (if x<3284 then (if x<3238 then 2 else 3) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
