/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch173
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8352 : Finset ℕ := ([48,72,132,250,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8352 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8352 250 4
  · have he : independentCachedBranchMembers8352.erase 250=independentCachedBranchMembers8350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8350
  · have he : independentCachedBranchMembers8352.filter (independentCachedEdge 250)=independentCachedBranchMembers8351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8351
def independentCachedBranchMembers8353 : Finset ℕ := ([132,252,1642,1650,1720,1752,2618,2650,2792,2800,3102,3174,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8353 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8353 4 (fun x => (if x<2792 then (if x<1720 then (if x<1642 then (if x<252 then 0 else 0) else (if x<1650 then 1 else 2)) else (if x<2618 then (if x<1752 then 1 else 2) else (if x<2650 then 1 else 2))) else (if x<3244 then (if x<3102 then (if x<2800 then 1 else 2) else (if x<3174 then 3 else 3)) else (if x<3276 then (if x<3252 then 0 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8354 : Finset ℕ := ([48,72,130,132,250,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8354 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8354 130 4
  · have he : independentCachedBranchMembers8354.erase 130=independentCachedBranchMembers8352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8352
  · have he : independentCachedBranchMembers8354.filter (independentCachedEdge 130)=independentCachedBranchMembers8353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8353
def independentCachedBranchMembers8355 : Finset ℕ := ([48,72,1642,1644,1720,1734,2618,2620,2710,2792,3102,3174,3250,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8355 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8355 4 (fun x => (if x<2710 then (if x<1720 then (if x<1642 then (if x<72 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2618 then (if x<1734 then 1 else 2) else (if x<2620 then 1 else 2))) else (if x<3250 then (if x<3102 then (if x<2792 then 2 else 1) else (if x<3174 then 3 else 3)) else (if x<3274 then (if x<3252 then 0 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8356 : Finset ℕ := ([48,72,80,130,132,250,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8356 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8356 80 4
  · have he : independentCachedBranchMembers8356.erase 80=independentCachedBranchMembers8354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8354
  · have he : independentCachedBranchMembers8356.filter (independentCachedEdge 80)=independentCachedBranchMembers8355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8355
def independentCachedBranchMembers8357 : Finset ℕ := ([48,72,1650,1652,1702,1752,2650,2652,2702,2800,3102,3174,3250,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8357 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8357 4 (fun x => (if x<2702 then (if x<1702 then (if x<1650 then (if x<72 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<2650 then (if x<1752 then 1 else 2) else (if x<2652 then 1 else 2))) else (if x<3250 then (if x<3102 then (if x<2800 then 1 else 2) else (if x<3174 then 3 else 3)) else (if x<3274 then (if x<3252 then 0 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8358 : Finset ℕ := ([40,48,72,80,130,132,250,252,1642,1644,1650,1652,1702,1720,1734,1752,2618,2620,2650,2652,2702,2710,2792,2800,3072,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8358 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8358 40 4
  · have he : independentCachedBranchMembers8358.erase 40=independentCachedBranchMembers8356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8356
  · have he : independentCachedBranchMembers8358.filter (independentCachedEdge 40)=independentCachedBranchMembers8357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8357
def independentCachedBranchMembers8359 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2590,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8359 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8359 2590 5
  · have he : independentCachedBranchMembers8359.erase 2590=independentCachedBranchMembers8335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8335
  · have he : independentCachedBranchMembers8359.filter (independentCachedEdge 2590)=independentCachedBranchMembers8358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8358
def independentCachedBranchMembers8360 : Finset ℕ := ([1614,1642,1644,1650,1652,1692,1702,1720,1734,1752,1764,3072,3130,3132,3162,3164,3174,3192,3214,3222,3244,3250,3252,3274,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8360 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8360 5 (fun x => (if x<3162 then (if x<1720 then (if x<1650 then (if x<1642 then 0 else (if x<1644 then 1 else 2)) else (if x<1692 then (if x<1652 then 0 else 1) else (if x<1702 then 2 else 0))) else (if x<1764 then (if x<1734 then 1 else (if x<1752 then 2 else 3)) else (if x<3130 then (if x<3072 then 3 else 4) else (if x<3132 then 4 else 2)))) else (if x<3250 then (if x<3192 then (if x<3164 then 0 else (if x<3174 then 4 else 0)) else (if x<3222 then (if x<3214 then 1 else 0) else (if x<3244 then 2 else 4))) else (if x<3276 then (if x<3252 then 0 else (if x<3274 then 1 else 4)) else (if x<3304 then (if x<3284 then 2 else 3) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8361 : Finset ℕ := ([1650,1652,1702,1752,3072,3162,3164,3192,3214,3244,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8361 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8361 4 (fun x => (if x<3164 then (if x<1752 then (if x<1652 then 0 else (if x<1702 then 1 else 0)) else (if x<3072 then 1 else (if x<3162 then 2 else 0))) else (if x<3244 then (if x<3192 then 1 else (if x<3214 then 2 else 0)) else (if x<3284 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8362 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1692,1702,1720,1734,1752,1764,3072,3130,3132,3162,3164,3174,3192,3214,3222,3244,3250,3252,3274,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8362 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8362 1590 4
  · have he : independentCachedBranchMembers8362.erase 1590=independentCachedBranchMembers8360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8360
  · have he : independentCachedBranchMembers8362.filter (independentCachedEdge 1590)=independentCachedBranchMembers8361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8361
def independentCachedBranchMembers8363 : Finset ℕ := ([1590,1614,1642,1652,1692,1702,1720,1764,3132,3162,3222,3244,3250,3274,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8363 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8363 4 (fun x => (if x<3132 then (if x<1692 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1764 then 1 else 0))) else (if x<3250 then (if x<3222 then (if x<3162 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8364 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1692,1702,1720,1734,1752,1764,3072,3130,3132,3162,3164,3174,3192,3214,3222,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8364 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8364 3282 4
  · have he : independentCachedBranchMembers8364.erase 3282=independentCachedBranchMembers8362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8362
  · have he : independentCachedBranchMembers8364.filter (independentCachedEdge 3282)=independentCachedBranchMembers8363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8363
def independentCachedBranchMembers8365 : Finset ℕ := ([1590,1614,1644,1650,1692,1734,1752,1764,3130,3164,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8365 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8365 4 (fun x => (if x<3130 then (if x<1692 then (if x<1644 then (if x<1614 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<1764 then 1 else 0))) else (if x<3250 then (if x<3214 then (if x<3164 then 2 else 2) else (if x<3244 then 2 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8366 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1692,1702,1720,1734,1752,1764,3072,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8366 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8366 3242 4
  · have he : independentCachedBranchMembers8366.erase 3242=independentCachedBranchMembers8364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8364
  · have he : independentCachedBranchMembers8366.filter (independentCachedEdge 3242)=independentCachedBranchMembers8365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8365
def independentCachedBranchMembers8367 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1734,1752,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8367 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8367 4 (fun x => (if x<3130 then (if x<1702 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else 0)) else (if x<1734 then (if x<1720 then 0 else 0) else (if x<1752 then 1 else 1))) else (if x<3214 then (if x<3162 then (if x<3132 then 2 else 3) else (if x<3164 then 3 else 2)) else (if x<3304 then (if x<3222 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8368 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1692,1702,1720,1734,1752,1764,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8368 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8368 3102 4
  · have he : independentCachedBranchMembers8368.erase 3102=independentCachedBranchMembers8366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8366
  · have he : independentCachedBranchMembers8368.filter (independentCachedEdge 3102)=independentCachedBranchMembers8367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8367
def independentCachedBranchMembers8369 : Finset ℕ := ([1642,1650,1692,1702,1734,1764,3072,3130,3162,3192,3214,3222,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8369 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8369 4 (fun x => (if x<3162 then (if x<1734 then (if x<1692 then (if x<1650 then 0 else 1) else (if x<1702 then 2 else 0)) else (if x<3072 then (if x<1764 then 1 else 2) else (if x<3130 then 3 else 1))) else (if x<3244 then (if x<3214 then (if x<3192 then 0 else 3) else (if x<3222 then 1 else 0)) else (if x<3276 then (if x<3252 then 2 else 3) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8370 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1692,1702,1720,1734,1752,1762,1764,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8370 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8370 1762 4
  · have he : independentCachedBranchMembers8370.erase 1762=independentCachedBranchMembers8368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8368
  · have he : independentCachedBranchMembers8370.filter (independentCachedEdge 1762)=independentCachedBranchMembers8369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8369
def independentCachedBranchMembers8371 : Finset ℕ := ([1644,1652,1692,1720,1752,1764,3072,3132,3164,3192,3244,3252,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8371 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8371 4 (fun x => (if x<3164 then (if x<1752 then (if x<1692 then (if x<1652 then 0 else 1) else (if x<1720 then 0 else 1)) else (if x<3072 then (if x<1764 then 2 else 2) else (if x<3132 then 3 else 0))) else (if x<3276 then (if x<3244 then (if x<3192 then 3 else 1) else (if x<3252 then 3 else 1)) else (if x<3304 then (if x<3284 then 0 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8372 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8372 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8372 1690 4
  · have he : independentCachedBranchMembers8372.erase 1690=independentCachedBranchMembers8370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8370
  · have he : independentCachedBranchMembers8372.filter (independentCachedEdge 1690)=independentCachedBranchMembers8371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8371
def independentCachedBranchMembers8373 : Finset ℕ := ([1590,1614,1650,1652,1720,1734,3072,3130,3132,3192,3214,3250,3252,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8373 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8373 4 (fun x => (if x<3132 then (if x<1720 then (if x<1650 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<3072 then (if x<1734 then 1 else 2) else (if x<3130 then 3 else 1))) else (if x<3252 then (if x<3214 then (if x<3192 then 2 else 3) else (if x<3250 then 2 else 0)) else (if x<3276 then (if x<3274 then 3 else 0) else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8374 : Finset ℕ := ([1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8374 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8374 1622 4
  · have he : independentCachedBranchMembers8374.erase 1622=independentCachedBranchMembers8372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8372
  · have he : independentCachedBranchMembers8374.filter (independentCachedEdge 1622)=independentCachedBranchMembers8373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8373
def independentCachedBranchMembers8375 : Finset ℕ := ([1590,1614,1642,1644,1702,1752,3072,3162,3164,3192,3222,3250,3252,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8375 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8375 4 (fun x => (if x<3164 then (if x<1702 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<3072 then (if x<1752 then 1 else 2) else (if x<3162 then 3 else 1))) else (if x<3252 then (if x<3222 then (if x<3192 then 2 else 3) else (if x<3250 then 1 else 0)) else (if x<3276 then (if x<3274 then 3 else 0) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8376 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8376 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8376 1582 4
  · have he : independentCachedBranchMembers8376.erase 1582=independentCachedBranchMembers8374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8374
  · have he : independentCachedBranchMembers8376.filter (independentCachedEdge 1582)=independentCachedBranchMembers8375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8375
def independentCachedBranchMembers8377 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2560,2590,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8377 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8377 2560 5
  · have he : independentCachedBranchMembers8377.erase 2560=independentCachedBranchMembers8359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8359
  · have he : independentCachedBranchMembers8377.filter (independentCachedEdge 2560)=independentCachedBranchMembers8376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8376
def independentCachedBranchMembers8378 : Finset ℕ := ([192,252,1622,1642,1644,1652,1734,1752,1762,1764,2652,2662,2762,2772,2792,2800,3162,3174,3192,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8378 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8378 5 (fun x => (if x<2762 then (if x<1734 then (if x<1642 then (if x<252 then 0 else (if x<1622 then 0 else 1)) else (if x<1644 then 1 else (if x<1652 then 2 else 3))) else (if x<1764 then (if x<1752 then 2 else (if x<1762 then 0 else 3)) else (if x<2652 then 0 else (if x<2662 then 3 else 1)))) else (if x<3192 then (if x<2800 then (if x<2772 then 3 else (if x<2792 then 0 else 0)) else (if x<3162 then 3 else (if x<3174 then 4 else 2))) else (if x<3284 then (if x<3276 then 2 else (if x<3282 then 0 else 2)) else (if x<3304 then 4 else (if x<3312 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8379 : Finset ℕ := ([252,1642,1652,1764,2762,2772,2800,3174,3192,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8379 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8379 4 (fun x => (if x<2800 then (if x<1764 then (if x<1642 then 0 else (if x<1652 then 1 else 0)) else (if x<2762 then 1 else (if x<2772 then 2 else 0))) else (if x<3276 then (if x<3174 then 2 else (if x<3192 then 1 else 3)) else (if x<3282 then 3 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8380 : Finset ℕ := ([192,252,1622,1642,1644,1652,1734,1752,1762,1764,2652,2662,2762,2770,2772,2792,2800,3162,3174,3192,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8380 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8380 2770 4
  · have he : independentCachedBranchMembers8380.erase 2770=independentCachedBranchMembers8378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8378
  · have he : independentCachedBranchMembers8380.filter (independentCachedEdge 2770)=independentCachedBranchMembers8379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8379
def independentCachedBranchMembers8381 : Finset ℕ := ([192,1622,1762,1764,2652,2792,2800,3174,3192,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8381 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8381 4 (fun x => (if x<2800 then (if x<1764 then (if x<1622 then 0 else (if x<1762 then 1 else 0)) else (if x<2652 then 1 else (if x<2792 then 2 else 0))) else (if x<3276 then (if x<3174 then 2 else (if x<3192 then 1 else 2)) else (if x<3282 then 3 else (if x<3284 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8382 : Finset ℕ := ([192,252,1622,1642,1644,1652,1734,1752,1762,1764,2652,2662,2680,2762,2770,2772,2792,2800,3162,3174,3192,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8382 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8382 2680 4
  · have he : independentCachedBranchMembers8382.erase 2680=independentCachedBranchMembers8380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8380
  · have he : independentCachedBranchMembers8382.filter (independentCachedEdge 2680)=independentCachedBranchMembers8381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8381
def independentCachedBranchMembers8383 : Finset ℕ := ([192,252,1622,1642,1652,1762,2652,2762,2772,2792,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8383 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8383 4 (fun x => (if x<2652 then (if x<1642 then (if x<252 then 0 else (if x<1622 then 0 else 1)) else (if x<1652 then 1 else (if x<1762 then 2 else 2))) else (if x<2792 then (if x<2762 then 2 else (if x<2772 then 2 else 0)) else (if x<3284 then 0 else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
