/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch174
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8384 : Finset ℕ := ([192,252,1622,1642,1644,1650,1652,1734,1752,1762,1764,2652,2662,2680,2762,2770,2772,2792,2800,3162,3174,3192,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8384 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8384 1650 4
  · have he : independentCachedBranchMembers8384.erase 1650=independentCachedBranchMembers8382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8382
  · have he : independentCachedBranchMembers8384.filter (independentCachedEdge 1650)=independentCachedBranchMembers8383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8383
def independentCachedBranchMembers8385 : Finset ℕ := ([252,1622,1644,1652,1734,1764,2652,2662,2772,3174,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8385 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8385 4 (fun x => (if x<2652 then (if x<1652 then (if x<1622 then 0 else (if x<1644 then 1 else 0)) else (if x<1734 then 2 else (if x<1764 then 2 else 1))) else (if x<3174 then (if x<2662 then 0 else (if x<2772 then 1 else 1)) else (if x<3276 then 2 else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8386 : Finset ℕ := ([192,250,252,1622,1642,1644,1650,1652,1734,1752,1762,1764,2652,2662,2680,2762,2770,2772,2792,2800,3162,3174,3192,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8386 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8386 250 4
  · have he : independentCachedBranchMembers8386.erase 250=independentCachedBranchMembers8384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8384
  · have he : independentCachedBranchMembers8386.filter (independentCachedEdge 250)=independentCachedBranchMembers8385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8385
def independentCachedBranchMembers8387 : Finset ℕ := ([192,1642,1644,1734,1762,1764,2662,2762,2792,3174,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8387 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8387 4 (fun x => (if x<2662 then (if x<1734 then (if x<1642 then 0 else (if x<1644 then 1 else 2)) else (if x<1762 then 0 else (if x<1764 then 2 else 1))) else (if x<3174 then (if x<2762 then 1 else (if x<2792 then 0 else 1)) else (if x<3276 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8388 : Finset ℕ := ([80,192,250,252,1622,1642,1644,1650,1652,1734,1752,1762,1764,2652,2662,2680,2762,2770,2772,2792,2800,3162,3174,3192,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8388 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8388 80 4
  · have he : independentCachedBranchMembers8388.erase 80=independentCachedBranchMembers8386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8386
  · have he : independentCachedBranchMembers8388.filter (independentCachedEdge 80)=independentCachedBranchMembers8387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8387
def independentCachedBranchMembers8389 : Finset ℕ := ([252,1622,1644,1650,1764,2652,2662,2680,2762,2772,2800,3162,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8389 4 (fun x => (if x<2680 then (if x<1650 then (if x<1622 then 0 else (if x<1644 then 1 else 0)) else (if x<2652 then (if x<1764 then 2 else 1) else (if x<2662 then 0 else 1))) else (if x<3162 then (if x<2772 then (if x<2762 then 2 else 3) else (if x<2800 then 1 else 3)) else (if x<3282 then (if x<3276 then 2 else 0) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8390 : Finset ℕ := ([1644,1764,2662,2762,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8390 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8390 3 (fun x => (if x<2762 then (if x<1764 then 0 else (if x<2662 then 1 else 0)) else (if x<3276 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8391 : Finset ℕ := ([80,252,1622,1644,1650,1764,2652,2662,2680,2762,2772,2800,3162,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8391 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8391 80 3
  · have he : independentCachedBranchMembers8391.erase 80=independentCachedBranchMembers8389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8389
  · have he : independentCachedBranchMembers8391.filter (independentCachedEdge 80)=independentCachedBranchMembers8390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8390
def independentCachedBranchMembers8392 : Finset ℕ := ([80,192,250,252,1622,1642,1644,1650,1652,1734,1752,1762,1764,2652,2662,2680,2762,2770,2772,2792,2800,3162,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8392 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8392 3274 4
  · have he : independentCachedBranchMembers8392.erase 3274=independentCachedBranchMembers8388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8388
  · have he : independentCachedBranchMembers8392.filter (independentCachedEdge 3274)=independentCachedBranchMembers8391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8391
def independentCachedBranchMembers8393 : Finset ℕ := ([250,1642,1650,1734,1764,2652,2662,2762,2770,2792,2800,3162,3192,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8393 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8393 4 (fun x => (if x<2762 then (if x<1734 then (if x<1642 then 0 else (if x<1650 then 0 else 1)) else (if x<2652 then (if x<1764 then 1 else 2) else (if x<2662 then 3 else 1))) else (if x<3162 then (if x<2792 then (if x<2770 then 0 else 1) else (if x<2800 then 2 else 3)) else (if x<3276 then (if x<3192 then 0 else 3) else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8394 : Finset ℕ := ([1642,1650,2652,2662,3162,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8394 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8394 3 (fun x => (if x<2662 then (if x<1650 then 0 else (if x<2652 then 1 else 2)) else (if x<3162 then 0 else (if x<3192 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8395 : Finset ℕ := ([192,250,1642,1650,1734,1764,2652,2662,2762,2770,2792,2800,3162,3192,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8395 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8395 192 3
  · have he : independentCachedBranchMembers8395.erase 192=independentCachedBranchMembers8393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8393
  · have he : independentCachedBranchMembers8395.filter (independentCachedEdge 192)=independentCachedBranchMembers8394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8394
def independentCachedBranchMembers8396 : Finset ℕ := ([80,192,250,252,1622,1642,1644,1650,1652,1734,1752,1762,1764,2652,2662,2680,2762,2770,2772,2792,2800,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8396 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8396 3164 4
  · have he : independentCachedBranchMembers8396.erase 3164=independentCachedBranchMembers8392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8392
  · have he : independentCachedBranchMembers8396.filter (independentCachedEdge 3164)=independentCachedBranchMembers8395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8395
def independentCachedBranchMembers8397 : Finset ℕ := ([80,250,1622,1642,1652,1762,2652,2762,2772,2792,3162,3174,3192,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8397 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8397 4 (fun x => (if x<2772 then (if x<1652 then (if x<1622 then (if x<250 then 0 else 0) else (if x<1642 then 1 else 1)) else (if x<2652 then (if x<1762 then 2 else 2) else (if x<2762 then 2 else 2))) else (if x<3192 then (if x<3162 then (if x<2792 then 1 else 1) else (if x<3174 then 0 else 3)) else (if x<3282 then (if x<3276 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8398 : Finset ℕ := ([80,192,250,252,1622,1642,1644,1650,1652,1734,1752,1762,1764,2652,2662,2680,2762,2764,2770,2772,2792,2800,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8398 2764 4
  · have he : independentCachedBranchMembers8398.erase 2764=independentCachedBranchMembers8396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8396
  · have he : independentCachedBranchMembers8398.filter (independentCachedEdge 2764)=independentCachedBranchMembers8397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8397
def independentCachedBranchMembers8399 : Finset ℕ := ([192,252,1644,1652,1734,1762,2652,2680,2762,2770,3162,3174,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8399 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8399 4 (fun x => (if x<2762 then (if x<1734 then (if x<1644 then (if x<252 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<2652 then (if x<1762 then 1 else 2) else (if x<2680 then 2 else 1))) else (if x<3276 then (if x<3162 then (if x<2770 then 2 else 1) else (if x<3174 then 3 else 3)) else (if x<3304 then (if x<3284 then 0 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8400 : Finset ℕ := ([80,192,250,252,1622,1642,1644,1650,1652,1734,1752,1762,1764,2650,2652,2662,2680,2762,2764,2770,2772,2792,2800,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8400 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8400 2650 4
  · have he : independentCachedBranchMembers8400.erase 2650=independentCachedBranchMembers8398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8398
  · have he : independentCachedBranchMembers8400.filter (independentCachedEdge 2650)=independentCachedBranchMembers8399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8399
def independentCachedBranchMembers8401 : Finset ℕ := ([80,192,250,252,1622,1642,1644,1734,2680,2770,2772,2792,3192,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8401 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8401 4 (fun x => (if x<2680 then (if x<1622 then (if x<250 then (if x<192 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1644 then (if x<1642 then 2 else 2) else (if x<1734 then 3 else 3))) else (if x<3192 then (if x<2772 then (if x<2770 then 0 else 0) else (if x<2792 then 1 else 1)) else (if x<3284 then (if x<3282 then 3 else 3) else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8402 : Finset ℕ := ([80,192,250,252,1614,1622,1642,1644,1650,1652,1734,1752,1762,1764,2650,2652,2662,2680,2762,2764,2770,2772,2792,2800,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8402 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8402 1614 4
  · have he : independentCachedBranchMembers8402.erase 1614=independentCachedBranchMembers8400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8400
  · have he : independentCachedBranchMembers8402.filter (independentCachedEdge 1614)=independentCachedBranchMembers8401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8401
def independentCachedBranchMembers8403 : Finset ℕ := ([250,252,1642,1644,1650,1652,1762,1764,2662,2680,2792,2800,3174,3192,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8403 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8403 4 (fun x => (if x<2662 then (if x<1650 then (if x<1642 then (if x<252 then 0 else 1) else (if x<1644 then 0 else 1)) else (if x<1762 then (if x<1652 then 2 else 3) else (if x<1764 then 3 else 2))) else (if x<3174 then (if x<2792 then (if x<2680 then 2 else 0) else (if x<2800 then 1 else 2)) else (if x<3304 then (if x<3192 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8404 : Finset ℕ := ([80,192,222,250,252,1614,1622,1642,1644,1650,1652,1734,1752,1762,1764,2650,2652,2662,2680,2762,2764,2770,2772,2792,2800,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8404 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8404 222 4
  · have he : independentCachedBranchMembers8404.erase 222=independentCachedBranchMembers8402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8402
  · have he : independentCachedBranchMembers8404.filter (independentCachedEdge 222)=independentCachedBranchMembers8403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8403
def independentCachedBranchMembers8405 : Finset ℕ := ([80,192,1622,1650,1652,1734,1762,1764,2662,2770,2772,2800,3174,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8405 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8405 4 (fun x => (if x<2662 then (if x<1652 then (if x<1622 then (if x<192 then 0 else 1) else (if x<1650 then 0 else 2)) else (if x<1762 then (if x<1734 then 3 else 1) else (if x<1764 then 3 else 2))) else (if x<3174 then (if x<2772 then (if x<2770 then 2 else 0) else (if x<2800 then 1 else 2)) else (if x<3284 then (if x<3282 then 3 else 1) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8406 : Finset ℕ := ([72,80,192,222,250,252,1614,1622,1642,1644,1650,1652,1734,1752,1762,1764,2650,2652,2662,2680,2762,2764,2770,2772,2792,2800,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8406 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8406 72 4
  · have he : independentCachedBranchMembers8406.erase 72=independentCachedBranchMembers8404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8404
  · have he : independentCachedBranchMembers8406.filter (independentCachedEdge 72)=independentCachedBranchMembers8405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8405
def independentCachedBranchMembers8407 : Finset ℕ := ([12,18,40,48,72,80,130,132,190,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2560,2590,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8407 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8407 190 5
  · have he : independentCachedBranchMembers8407.erase 190=independentCachedBranchMembers8377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8377
  · have he : independentCachedBranchMembers8407.filter (independentCachedEdge 190)=independentCachedBranchMembers8406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8406
def independentCachedBranchMembers8408 : Finset ℕ := ([192,222,1582,1590,1642,1650,1652,1690,1692,1734,1752,2618,2662,2680,2702,2762,2764,2770,2772,3130,3132,3174,3214,3222,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8408 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8408 5 (fun x => (if x<2680 then (if x<1652 then (if x<1590 then (if x<222 then 0 else (if x<1582 then 0 else 1)) else (if x<1642 then 2 else (if x<1650 then 2 else 1))) else (if x<1734 then (if x<1690 then 3 else (if x<1692 then 1 else 3)) else (if x<2618 then (if x<1752 then 0 else 0) else (if x<2662 then 1 else 1)))) else (if x<3132 then (if x<2764 then (if x<2702 then 4 else (if x<2762 then 1 else 0)) else (if x<2772 then (if x<2770 then 4 else 1) else (if x<3130 then 0 else 2))) else (if x<3222 then (if x<3174 then 3 else (if x<3214 then 2 else 3)) else (if x<3276 then (if x<3274 then 2 else 2) else (if x<3284 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8409 : Finset ℕ := ([192,1582,1590,1652,1690,1752,2662,2762,2770,3132,3174,3274] : List ℕ).toFinset
theorem independentCachedBranchBound8409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8409 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8409 4 (fun x => (if x<2662 then (if x<1652 then (if x<1582 then 0 else (if x<1590 then 0 else 1)) else (if x<1690 then 2 else (if x<1752 then 1 else 2))) else (if x<3132 then (if x<2762 then 1 else (if x<2770 then 1 else 0)) else (if x<3174 then 0 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8410 : Finset ℕ := ([132,192,222,1582,1590,1642,1650,1652,1690,1692,1734,1752,2618,2662,2680,2702,2762,2764,2770,2772,3130,3132,3174,3214,3222,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8410 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8410 132 4
  · have he : independentCachedBranchMembers8410.erase 132=independentCachedBranchMembers8408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8408
  · have he : independentCachedBranchMembers8410.filter (independentCachedEdge 132)=independentCachedBranchMembers8409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8409
def independentCachedBranchMembers8411 : Finset ℕ := ([222,1582,1642,1690,1692,1752,2662,2770,2772,3174,3222,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8411 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8411 4 (fun x => (if x<2662 then (if x<1690 then (if x<1582 then 0 else (if x<1642 then 1 else 2)) else (if x<1692 then 0 else (if x<1752 then 1 else 2))) else (if x<3174 then (if x<2770 then 1 else (if x<2772 then 0 else 1)) else (if x<3222 then 2 else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8412 : Finset ℕ := ([48,132,192,222,1582,1590,1642,1650,1652,1690,1692,1734,1752,2618,2662,2680,2702,2762,2764,2770,2772,3130,3132,3174,3214,3222,3274,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8412 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8412 48 4
  · have he : independentCachedBranchMembers8412.erase 48=independentCachedBranchMembers8410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8410
  · have he : independentCachedBranchMembers8412.filter (independentCachedEdge 48)=independentCachedBranchMembers8411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8411
def independentCachedBranchMembers8413 : Finset ℕ := ([132,1590,1642,1652,1692,2618,2662,2680,2702,2764,2770,3132,3222,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8413 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8413 4 (fun x => (if x<2680 then (if x<1652 then (if x<1590 then 0 else (if x<1642 then 1 else 0)) else (if x<2618 then (if x<1692 then 2 else 1) else (if x<2662 then 0 else 1))) else (if x<3132 then (if x<2764 then (if x<2702 then 2 else 3) else (if x<2770 then 1 else 3)) else (if x<3274 then (if x<3222 then 2 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8414 : Finset ℕ := ([1642,1692,2662,2770,3222,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8414 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8414 3 (fun x => (if x<2770 then (if x<1692 then 0 else (if x<2662 then 1 else 0)) else (if x<3222 then 2 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8415 : Finset ℕ := ([48,132,1590,1642,1652,1692,2618,2662,2680,2702,2764,2770,3132,3222,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8415 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8415 48 3
  · have he : independentCachedBranchMembers8415.erase 48=independentCachedBranchMembers8413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8413
  · have he : independentCachedBranchMembers8415.filter (independentCachedEdge 48)=independentCachedBranchMembers8414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8414
end EntropyDesigns.QuadraticRefinement
