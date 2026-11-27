/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch171
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8288 : Finset ℕ := ([40,72,132,250,1590,1622,1642,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2710,2762,2772,2792,3130,3162,3174,3192,3222,3242,3252,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8288 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8288 3284 4
  · have he : independentCachedBranchMembers8288.erase 3284=independentCachedBranchMembers8284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8284
  · have he : independentCachedBranchMembers8288.filter (independentCachedEdge 3284)=independentCachedBranchMembers8287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8287
def independentCachedBranchMembers8289 : Finset ℕ := ([132,1622,1702,1720,1764,2618,2662,2680,2710,2762,2772,3162,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8289 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8289 4 (fun x => (if x<2680 then (if x<1720 then (if x<1622 then 0 else (if x<1702 then 1 else 0)) else (if x<2618 then (if x<1764 then 2 else 1) else (if x<2662 then 2 else 1))) else (if x<3162 then (if x<2762 then (if x<2710 then 0 else 3) else (if x<2772 then 3 else 1)) else (if x<3252 then (if x<3242 then 0 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8290 : Finset ℕ := ([1702,1764,2662,2762,3162,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8290 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8290 3 (fun x => (if x<2762 then (if x<1764 then 0 else (if x<2662 then 1 else 0)) else (if x<3162 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8291 : Finset ℕ := ([40,132,1622,1702,1720,1764,2618,2662,2680,2710,2762,2772,3162,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8291 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8291 40 3
  · have he : independentCachedBranchMembers8291.erase 40=independentCachedBranchMembers8289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8289
  · have he : independentCachedBranchMembers8291.filter (independentCachedEdge 40)=independentCachedBranchMembers8290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8290
def independentCachedBranchMembers8292 : Finset ℕ := ([40,72,132,250,1590,1622,1642,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2710,2762,2772,2792,3130,3162,3174,3192,3222,3242,3252,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8292 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8292 3274 4
  · have he : independentCachedBranchMembers8292.erase 3274=independentCachedBranchMembers8288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8288
  · have he : independentCachedBranchMembers8292.filter (independentCachedEdge 3274)=independentCachedBranchMembers8291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8291
def independentCachedBranchMembers8293 : Finset ℕ := ([40,72,132,250,1590,1622,1690,1764,2618,2650,2710,2792,3130,3162,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8293 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8293 4 (fun x => (if x<2618 then (if x<1590 then (if x<132 then (if x<72 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1690 then (if x<1622 then 2 else 3) else (if x<1764 then 2 else 3))) else (if x<3130 then (if x<2710 then (if x<2650 then 0 else 1) else (if x<2792 then 0 else 1)) else (if x<3222 then (if x<3162 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8294 : Finset ℕ := ([40,72,132,250,1590,1622,1642,1652,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2710,2762,2772,2792,3130,3162,3174,3192,3222,3242,3252,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8294 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8294 1652 4
  · have he : independentCachedBranchMembers8294.erase 1652=independentCachedBranchMembers8292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8292
  · have he : independentCachedBranchMembers8294.filter (independentCachedEdge 1652)=independentCachedBranchMembers8293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8293
def independentCachedBranchMembers8295 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8295 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8295 12 5
  · have he : independentCachedBranchMembers8295.erase 12=independentCachedBranchMembers8279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8279
  · have he : independentCachedBranchMembers8295.filter (independentCachedEdge 12)=independentCachedBranchMembers8294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8294
def independentCachedBranchMembers8296 : Finset ℕ := ([130,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3130,3164,3174,3192,3214,3242,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8296 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8296 5 (fun x => (if x<2732 then (if x<1690 then (if x<1622 then (if x<250 then 0 else (if x<1582 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1762 then (if x<1734 then 0 else (if x<1752 then 2 else 2)) else (if x<2650 then (if x<2620 then 0 else 3) else (if x<2710 then 3 else 3)))) else (if x<3174 then (if x<2772 then (if x<2738 then 1 else (if x<2762 then 0 else 0)) else (if x<3130 then (if x<2800 then 1 else 3) else (if x<3164 then 4 else 4))) else (if x<3242 then (if x<3192 then 2 else (if x<3214 then 2 else 4)) else (if x<3282 then (if x<3252 then 0 else 3) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8297 : Finset ℕ := ([1644,1690,1734,1762,2620,2710,2738,2762,3130,3174,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8297 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8297 4 (fun x => (if x<2738 then (if x<1762 then (if x<1690 then 0 else (if x<1734 then 1 else 0)) else (if x<2620 then 1 else (if x<2710 then 0 else 0))) else (if x<3174 then (if x<2762 then 1 else (if x<3130 then 1 else 2)) else (if x<3252 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8298 : Finset ℕ := ([80,130,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3130,3164,3174,3192,3214,3242,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8298 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8298 80 4
  · have he : independentCachedBranchMembers8298.erase 80=independentCachedBranchMembers8296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8296
  · have he : independentCachedBranchMembers8298.filter (independentCachedEdge 80)=independentCachedBranchMembers8297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8297
def independentCachedBranchMembers8299 : Finset ℕ := ([1650,1690,1752,1762,2650,2738,2762,2800,3164,3174,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8299 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8299 4 (fun x => (if x<2762 then (if x<1762 then (if x<1690 then 0 else (if x<1752 then 0 else 1)) else (if x<2650 then 1 else (if x<2738 then 0 else 0))) else (if x<3174 then (if x<2800 then 1 else (if x<3164 then 1 else 2)) else (if x<3214 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8300 : Finset ℕ := ([40,80,130,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3130,3164,3174,3192,3214,3242,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8300 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8300 40 4
  · have he : independentCachedBranchMembers8300.erase 40=independentCachedBranchMembers8298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8298
  · have he : independentCachedBranchMembers8300.filter (independentCachedEdge 40)=independentCachedBranchMembers8299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8299
def independentCachedBranchMembers8301 : Finset ℕ := ([40,80,130,250,1582,1622,1690,1762,2620,2650,2710,2800,3130,3164,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8301 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8301 4 (fun x => (if x<2620 then (if x<1582 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3130 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8302 : Finset ℕ := ([40,80,130,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8302 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8302 3276 4
  · have he : independentCachedBranchMembers8302.erase 3276=independentCachedBranchMembers8300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8300
  · have he : independentCachedBranchMembers8302.filter (independentCachedEdge 3276)=independentCachedBranchMembers8301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8301
def independentCachedBranchMembers8303 : Finset ℕ := ([40,80,130,250,1644,1650,1734,1752,2732,2738,2762,2772,3130,3164,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8303 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8303 4 (fun x => (if x<2732 then (if x<1644 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3130 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8304 : Finset ℕ := ([40,80,130,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8304 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8304 3102 4
  · have he : independentCachedBranchMembers8304.erase 3102=independentCachedBranchMembers8302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8302
  · have he : independentCachedBranchMembers8304.filter (independentCachedEdge 3102)=independentCachedBranchMembers8303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8303
def independentCachedBranchMembers8305 : Finset ℕ := ([1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8305 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8305 4 (fun x => (if x<2620 then (if x<1690 then (if x<1644 then (if x<1622 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<1762 then 1 else 0))) else (if x<2738 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2772 then (if x<2762 then 3 else 3) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8306 : Finset ℕ := ([40,80,130,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8306 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8306 3072 4
  · have he : independentCachedBranchMembers8306.erase 3072=independentCachedBranchMembers8304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8304
  · have he : independentCachedBranchMembers8306.filter (independentCachedEdge 3072)=independentCachedBranchMembers8305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8305
def independentCachedBranchMembers8307 : Finset ℕ := ([40,250,1582,1644,1650,1762,2620,2732,2738,2800,3130,3174,3192,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8307 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8307 4 (fun x => (if x<2738 then (if x<1650 then (if x<1582 then (if x<250 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2732 then 2 else 1))) else (if x<3192 then (if x<3130 then (if x<2800 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8308 : Finset ℕ := ([40,80,130,222,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8308 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8308 222 4
  · have he : independentCachedBranchMembers8308.erase 222=independentCachedBranchMembers8306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8306
  · have he : independentCachedBranchMembers8308.filter (independentCachedEdge 222)=independentCachedBranchMembers8307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8307
def independentCachedBranchMembers8309 : Finset ℕ := ([80,130,1622,1644,1650,1690,2650,2710,2732,2738,3164,3174,3192,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8309 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8309 4 (fun x => (if x<2732 then (if x<1650 then (if x<1622 then (if x<130 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<2650 then (if x<1690 then 2 else 2) else (if x<2710 then 2 else 1))) else (if x<3192 then (if x<3164 then (if x<2738 then 1 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3214 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8310 : Finset ℕ := ([40,80,130,192,222,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8310 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8310 192 4
  · have he : independentCachedBranchMembers8310.erase 192=independentCachedBranchMembers8308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8308
  · have he : independentCachedBranchMembers8310.filter (independentCachedEdge 192)=independentCachedBranchMembers8309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8309
def independentCachedBranchMembers8311 : Finset ℕ := ([80,130,1582,1734,1752,1762,2620,2762,2772,2800,3164,3174,3192,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8311 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8311 4 (fun x => (if x<2772 then (if x<1752 then (if x<1582 then (if x<130 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2762 then 1 else 2))) else (if x<3192 then (if x<3164 then (if x<2800 then 1 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3214 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8312 : Finset ℕ := ([18,40,80,130,192,222,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8312 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8312 18 4
  · have he : independentCachedBranchMembers8312.erase 18=independentCachedBranchMembers8310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8310
  · have he : independentCachedBranchMembers8312.filter (independentCachedEdge 18)=independentCachedBranchMembers8311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8311
def independentCachedBranchMembers8313 : Finset ℕ := ([40,250,1622,1690,1734,1752,2650,2710,2762,2772,3130,3174,3192,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8313 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8313 4 (fun x => (if x<2762 then (if x<1734 then (if x<1622 then (if x<250 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1752 then 2 else 2) else (if x<2710 then 1 else 1))) else (if x<3192 then (if x<3130 then (if x<2772 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8314 : Finset ℕ := ([12,18,40,80,130,192,222,250,1582,1622,1644,1650,1690,1734,1752,1762,2620,2650,2710,2732,2738,2762,2772,2800,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8314 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8314 12 4
  · have he : independentCachedBranchMembers8314.erase 12=independentCachedBranchMembers8312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8312
  · have he : independentCachedBranchMembers8314.filter (independentCachedEdge 12)=independentCachedBranchMembers8313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8313
def independentCachedBranchMembers8315 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2740,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8315 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8315 2740 5
  · have he : independentCachedBranchMembers8315.erase 2740=independentCachedBranchMembers8295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8295
  · have he : independentCachedBranchMembers8315.filter (independentCachedEdge 2740)=independentCachedBranchMembers8314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8314
def independentCachedBranchMembers8316 : Finset ℕ := ([132,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3132,3162,3174,3192,3222,3242,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8316 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8316 5 (fun x => (if x<2732 then (if x<1692 then (if x<1614 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1764 then (if x<1734 then 0 else (if x<1752 then 2 else 2)) else (if x<2652 then (if x<2618 then 0 else 3) else (if x<2702 then 3 else 3)))) else (if x<3174 then (if x<2772 then (if x<2738 then 0 else (if x<2762 then 1 else 1)) else (if x<3132 then (if x<2792 then 0 else 3) else (if x<3162 then 4 else 4))) else (if x<3242 then (if x<3192 then 2 else (if x<3222 then 2 else 4)) else (if x<3276 then (if x<3252 then 3 else 0) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8317 : Finset ℕ := ([1650,1692,1734,1764,2618,2702,2732,2772,3132,3174,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8317 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8317 4 (fun x => (if x<2732 then (if x<1764 then (if x<1692 then 0 else (if x<1734 then 1 else 0)) else (if x<2618 then 1 else (if x<2702 then 0 else 0))) else (if x<3174 then (if x<2772 then 1 else (if x<3132 then 1 else 2)) else (if x<3242 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8318 : Finset ℕ := ([72,132,252,1590,1614,1644,1650,1692,1734,1752,1764,2618,2652,2702,2732,2738,2762,2772,2792,3132,3162,3174,3192,3222,3242,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8318 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8318 72 4
  · have he : independentCachedBranchMembers8318.erase 72=independentCachedBranchMembers8316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8316
  · have he : independentCachedBranchMembers8318.filter (independentCachedEdge 72)=independentCachedBranchMembers8317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8317
def independentCachedBranchMembers8319 : Finset ℕ := ([1644,1692,1752,1764,2652,2732,2772,2792,3162,3174,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8319 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8319 4 (fun x => (if x<2772 then (if x<1764 then (if x<1692 then 0 else (if x<1752 then 0 else 1)) else (if x<2652 then 1 else (if x<2732 then 0 else 0))) else (if x<3174 then (if x<2792 then 1 else (if x<3162 then 1 else 2)) else (if x<3222 then 2 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
