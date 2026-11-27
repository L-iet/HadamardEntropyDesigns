/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch172
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8320 : Finset ℕ := ([48,72,132,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3132,3162,3174,3192,3222,3242,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8320 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8320 48 4
  · have he : independentCachedBranchMembers8320.erase 48=independentCachedBranchMembers8318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8318
  · have he : independentCachedBranchMembers8320.filter (independentCachedEdge 48)=independentCachedBranchMembers8319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8319
def independentCachedBranchMembers8321 : Finset ℕ := ([48,72,132,252,1590,1614,1692,1764,2618,2652,2702,2792,3132,3162,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8321 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8321 4 (fun x => (if x<2618 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3132 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8322 : Finset ℕ := ([48,72,132,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8322 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8322 3282 4
  · have he : independentCachedBranchMembers8322.erase 3282=independentCachedBranchMembers8320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8320
  · have he : independentCachedBranchMembers8322.filter (independentCachedEdge 3282)=independentCachedBranchMembers8321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8321
def independentCachedBranchMembers8323 : Finset ℕ := ([48,72,132,252,1644,1650,1734,1752,2732,2738,2762,2772,3132,3162,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8323 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8323 4 (fun x => (if x<2732 then (if x<1644 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3132 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8324 : Finset ℕ := ([48,72,132,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8324 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8324 3102 4
  · have he : independentCachedBranchMembers8324.erase 3102=independentCachedBranchMembers8322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8322
  · have he : independentCachedBranchMembers8324.filter (independentCachedEdge 3102)=independentCachedBranchMembers8323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8323
def independentCachedBranchMembers8325 : Finset ℕ := ([1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792] : List ℕ).toFinset
theorem independentCachedBranchBound8325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8325 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8325 4 (fun x => (if x<2618 then (if x<1692 then (if x<1644 then (if x<1614 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<1764 then 1 else 0))) else (if x<2738 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2772 then (if x<2762 then 3 else 3) else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8326 : Finset ℕ := ([48,72,132,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8326 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8326 3072 4
  · have he : independentCachedBranchMembers8326.erase 3072=independentCachedBranchMembers8324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8324
  · have he : independentCachedBranchMembers8326.filter (independentCachedEdge 3072)=independentCachedBranchMembers8325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8325
def independentCachedBranchMembers8327 : Finset ℕ := ([48,252,1590,1644,1650,1764,2618,2732,2738,2792,3132,3174,3192,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8327 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8327 4 (fun x => (if x<2738 then (if x<1650 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2732 then 2 else 2))) else (if x<3192 then (if x<3132 then (if x<2792 then 1 else 1) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8328 : Finset ℕ := ([48,72,132,222,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8328 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8328 222 4
  · have he : independentCachedBranchMembers8328.erase 222=independentCachedBranchMembers8326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8326
  · have he : independentCachedBranchMembers8328.filter (independentCachedEdge 222)=independentCachedBranchMembers8327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8327
def independentCachedBranchMembers8329 : Finset ℕ := ([72,132,1614,1644,1650,1692,2652,2702,2732,2738,3162,3174,3192,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8329 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8329 4 (fun x => (if x<2732 then (if x<1650 then (if x<1614 then (if x<132 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2652 then (if x<1692 then 1 else 2) else (if x<2702 then 2 else 1))) else (if x<3192 then (if x<3162 then (if x<2738 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3222 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8330 : Finset ℕ := ([48,72,132,192,222,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8330 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8330 192 4
  · have he : independentCachedBranchMembers8330.erase 192=independentCachedBranchMembers8328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8328
  · have he : independentCachedBranchMembers8330.filter (independentCachedEdge 192)=independentCachedBranchMembers8329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8329
def independentCachedBranchMembers8331 : Finset ℕ := ([48,252,1614,1692,1734,1752,2652,2702,2762,2772,3132,3174,3192,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8331 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8331 4 (fun x => (if x<2762 then (if x<1734 then (if x<1614 then (if x<252 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1752 then 2 else 2) else (if x<2702 then 1 else 1))) else (if x<3192 then (if x<3132 then (if x<2772 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8332 : Finset ℕ := ([18,48,72,132,192,222,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8332 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8332 18 4
  · have he : independentCachedBranchMembers8332.erase 18=independentCachedBranchMembers8330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8330
  · have he : independentCachedBranchMembers8332.filter (independentCachedEdge 18)=independentCachedBranchMembers8331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8331
def independentCachedBranchMembers8333 : Finset ℕ := ([72,132,1590,1734,1752,1764,2618,2762,2772,2792,3162,3174,3192,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8333 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8333 4 (fun x => (if x<2772 then (if x<1752 then (if x<1590 then (if x<132 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2762 then 1 else 1))) else (if x<3192 then (if x<3162 then (if x<2792 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3222 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8334 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8334 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8334 12 4
  · have he : independentCachedBranchMembers8334.erase 12=independentCachedBranchMembers8332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8332
  · have he : independentCachedBranchMembers8334.filter (independentCachedEdge 12)=independentCachedBranchMembers8333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8333
def independentCachedBranchMembers8335 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8335 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8335 2730 5
  · have he : independentCachedBranchMembers8335.erase 2730=independentCachedBranchMembers8315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8315
  · have he : independentCachedBranchMembers8335.filter (independentCachedEdge 2730)=independentCachedBranchMembers8334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8334
def independentCachedBranchMembers8336 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8336 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8336 5 (fun x => (if x<2702 then (if x<1734 then (if x<1652 then (if x<1644 then 0 else (if x<1650 then 1 else 1)) else (if x<1702 then 0 else (if x<1720 then 0 else 0))) else (if x<2620 then (if x<1752 then 1 else (if x<2618 then 1 else 2)) else (if x<2650 then 3 else (if x<2652 then 3 else 2)))) else (if x<3192 then (if x<2800 then (if x<2710 then 2 else (if x<2792 then 3 else 2)) else (if x<3102 then 3 else (if x<3174 then 2 else 0))) else (if x<3252 then (if x<3244 then 0 else (if x<3250 then 4 else 4)) else (if x<3276 then (if x<3274 then 0 else 4) else (if x<3284 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8337 : Finset ℕ := ([1642,1650,1702,1734,2618,2650,2702,2710,3102,3174,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8337 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8337 4 (fun x => (if x<2702 then (if x<1734 then (if x<1650 then 0 else (if x<1702 then 1 else 0)) else (if x<2618 then 1 else (if x<2650 then 1 else 0))) else (if x<3174 then (if x<2710 then 1 else (if x<3102 then 0 else 2)) else (if x<3250 then 2 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8338 : Finset ℕ := ([252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8338 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8338 252 4
  · have he : independentCachedBranchMembers8338.erase 252=independentCachedBranchMembers8336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8336
  · have he : independentCachedBranchMembers8338.filter (independentCachedEdge 252)=independentCachedBranchMembers8337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8337
def independentCachedBranchMembers8339 : Finset ℕ := ([1644,1652,1720,1752,2620,2652,2792,2800,3102,3174,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8339 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8339 4 (fun x => (if x<2792 then (if x<1752 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<2620 then 1 else (if x<2652 then 0 else 1))) else (if x<3174 then (if x<2800 then 0 else (if x<3102 then 1 else 2)) else (if x<3250 then 2 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8340 : Finset ℕ := ([132,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8340 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8340 132 4
  · have he : independentCachedBranchMembers8340.erase 132=independentCachedBranchMembers8338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8338
  · have he : independentCachedBranchMembers8340.filter (independentCachedEdge 132)=independentCachedBranchMembers8339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8339
def independentCachedBranchMembers8341 : Finset ℕ := ([1650,1652,1720,1734,2618,2620,2702,2800,3102,3174,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8341 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8341 4 (fun x => (if x<2702 then (if x<1734 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<2618 then 1 else (if x<2620 then 0 else 1))) else (if x<3174 then (if x<2800 then 1 else (if x<3102 then 0 else 2)) else (if x<3244 then 2 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8342 : Finset ℕ := ([72,132,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8342 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8342 72 4
  · have he : independentCachedBranchMembers8342.erase 72=independentCachedBranchMembers8340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8340
  · have he : independentCachedBranchMembers8342.filter (independentCachedEdge 72)=independentCachedBranchMembers8341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8341
def independentCachedBranchMembers8343 : Finset ℕ := ([1642,1644,1702,1752,2650,2652,2710,2792,3102,3174,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8343 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8343 4 (fun x => (if x<2710 then (if x<1752 then (if x<1644 then 0 else (if x<1702 then 1 else 0)) else (if x<2650 then 1 else (if x<2652 then 0 else 1))) else (if x<3174 then (if x<2792 then 0 else (if x<3102 then 1 else 2)) else (if x<3244 then 2 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8344 : Finset ℕ := ([48,72,132,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3102,3174,3192,3244,3250,3252,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8344 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8344 48 4
  · have he : independentCachedBranchMembers8344.erase 48=independentCachedBranchMembers8342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8342
  · have he : independentCachedBranchMembers8344.filter (independentCachedEdge 48)=independentCachedBranchMembers8343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8343
def independentCachedBranchMembers8345 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,2618,2652,2702,2792,3244,3250,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8345 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8345 4 (fun x => (if x<2618 then (if x<1642 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3244 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3274 then (if x<3250 then 3 else 3) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8346 : Finset ℕ := ([48,72,132,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3102,3174,3192,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8346 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8346 3282 4
  · have he : independentCachedBranchMembers8346.erase 3282=independentCachedBranchMembers8344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8344
  · have he : independentCachedBranchMembers8346.filter (independentCachedEdge 3282)=independentCachedBranchMembers8345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8345
def independentCachedBranchMembers8347 : Finset ℕ := ([48,72,132,252,1644,1650,1734,1752,2620,2650,2710,2800,3244,3250,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8347 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8347 4 (fun x => (if x<2620 then (if x<1644 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3244 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3274 then (if x<3250 then 3 else 3) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8348 : Finset ℕ := ([48,72,132,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8348 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8348 3242 4
  · have he : independentCachedBranchMembers8348.erase 3242=independentCachedBranchMembers8346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8346
  · have he : independentCachedBranchMembers8348.filter (independentCachedEdge 3242)=independentCachedBranchMembers8347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8347
def independentCachedBranchMembers8349 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8349 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8349 4 (fun x => (if x<2618 then (if x<1702 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else 0)) else (if x<1734 then (if x<1720 then 0 else 0) else (if x<1752 then 1 else 1))) else (if x<2702 then (if x<2650 then (if x<2620 then 2 else 3) else (if x<2652 then 3 else 2)) else (if x<2792 then (if x<2710 then 2 else 3) else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8350 : Finset ℕ := ([48,72,132,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8350 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8350 3072 4
  · have he : independentCachedBranchMembers8350.erase 3072=independentCachedBranchMembers8348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8348
  · have he : independentCachedBranchMembers8350.filter (independentCachedEdge 3072)=independentCachedBranchMembers8349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8349
def independentCachedBranchMembers8351 : Finset ℕ := ([132,252,1644,1652,1702,1734,2620,2652,2702,2710,3102,3174,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8351 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8351 4 (fun x => (if x<2702 then (if x<1702 then (if x<1644 then (if x<252 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<2620 then (if x<1734 then 1 else 2) else (if x<2652 then 2 else 1))) else (if x<3244 then (if x<3102 then (if x<2710 then 2 else 1) else (if x<3174 then 3 else 3)) else (if x<3276 then (if x<3252 then 0 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
