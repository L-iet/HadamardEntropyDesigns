/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch235
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10336 : Finset ℕ := ([12,66,252,1626,1644,1692,1706,1714,1738,1746,1764,2620,2652,2666,2674,2732,3132,3164,3178,3186,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10336 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10336 252 4
  · have he : independentCachedBranchMembers10336.erase 252=independentCachedBranchMembers10334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10334
  · have he : independentCachedBranchMembers10336.filter (independentCachedEdge 252)=independentCachedBranchMembers10335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10335
def independentCachedBranchMembers10337 : Finset ℕ := ([12,1644,1706,1714,1738,1746,2620,2652,3132,3164,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10337 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10337 4 (fun x => (if x<2620 then (if x<1714 then (if x<1644 then 0 else (if x<1706 then 0 else 1)) else (if x<1738 then 2 else (if x<1746 then 2 else 1))) else (if x<3164 then (if x<2652 then 0 else (if x<3132 then 3 else 3)) else (if x<3226 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10338 : Finset ℕ := ([12,66,132,252,1626,1644,1692,1706,1714,1738,1746,1764,2620,2652,2666,2674,2732,3132,3164,3178,3186,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10338 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10338 132 4
  · have he : independentCachedBranchMembers10338.erase 132=independentCachedBranchMembers10336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10336
  · have he : independentCachedBranchMembers10338.filter (independentCachedEdge 132)=independentCachedBranchMembers10337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10337
def independentCachedBranchMembers10339 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10339 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10339 1690 5
  · have he : independentCachedBranchMembers10339.erase 1690=independentCachedBranchMembers10333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10333
  · have he : independentCachedBranchMembers10339.filter (independentCachedEdge 1690)=independentCachedBranchMembers10338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10338
def independentCachedBranchMembers10340 : Finset ℕ := ([12,36,252,1596,1644,1708,1716,1740,1748,2620,2652,2668,2676,2716,2732,2788,3132,3164,3180,3188,3244,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10340 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10340 5 (fun x => (if x<2668 then (if x<1708 then (if x<252 then (if x<36 then 0 else 1) else (if x<1596 then 0 else (if x<1644 then 0 else 1))) else (if x<1748 then (if x<1716 then 2 else (if x<1740 then 1 else 0)) else (if x<2620 then 2 else (if x<2652 then 1 else 0)))) else (if x<3164 then (if x<2732 then (if x<2676 then 3 else (if x<2716 then 4 else 2)) else (if x<2788 then 0 else (if x<3132 then 1 else 3))) else (if x<3244 then (if x<3180 then 4 else (if x<3188 then 0 else 1)) else (if x<3252 then 1 else (if x<3276 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10341 : Finset ℕ := ([12,1644,1708,1716,1740,1748,2620,2652,2716,2788,3132,3164] : List ℕ).toFinset
theorem independentCachedBranchBound10341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10341 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10341 4 (fun x => (if x<2620 then (if x<1716 then (if x<1644 then 0 else (if x<1708 then 0 else 1)) else (if x<1740 then 2 else (if x<1748 then 2 else 1))) else (if x<2788 then (if x<2652 then 0 else (if x<2716 then 3 else 1)) else (if x<3132 then 1 else (if x<3164 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10342 : Finset ℕ := ([12,36,252,1596,1644,1708,1716,1740,1748,1764,2620,2652,2668,2676,2716,2732,2788,3132,3164,3180,3188,3244,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10342 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10342 1764 4
  · have he : independentCachedBranchMembers10342.erase 1764=independentCachedBranchMembers10340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10340
  · have he : independentCachedBranchMembers10342.filter (independentCachedEdge 1764)=independentCachedBranchMembers10341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10341
def independentCachedBranchMembers10343 : Finset ℕ := ([36,1596,1708,1716,1740,1748,2668,2676,2716,2788,3180,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10343 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10343 4 (fun x => (if x<2668 then (if x<1716 then (if x<1596 then 0 else (if x<1708 then 0 else 1)) else (if x<1740 then 2 else (if x<1748 then 2 else 1))) else (if x<2788 then (if x<2676 then 0 else (if x<2716 then 3 else 1)) else (if x<3180 then 1 else (if x<3188 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10344 : Finset ℕ := ([12,36,252,1596,1644,1692,1708,1716,1740,1748,1764,2620,2652,2668,2676,2716,2732,2788,3132,3164,3180,3188,3244,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10344 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10344 1692 4
  · have he : independentCachedBranchMembers10344.erase 1692=independentCachedBranchMembers10342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10342
  · have he : independentCachedBranchMembers10344.filter (independentCachedEdge 1692)=independentCachedBranchMembers10343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10343
def independentCachedBranchMembers10345 : Finset ℕ := ([12,36,1596,1644,2620,2652,2668,2676,3132,3164,3180,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10345 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10345 4 (fun x => (if x<2668 then (if x<1644 then (if x<36 then 0 else (if x<1596 then 1 else 0)) else (if x<2620 then 1 else (if x<2652 then 1 else 0))) else (if x<3164 then (if x<2676 then 2 else (if x<3132 then 3 else 2)) else (if x<3180 then 3 else (if x<3188 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10346 : Finset ℕ := ([12,36,132,252,1596,1644,1692,1708,1716,1740,1748,1764,2620,2652,2668,2676,2716,2732,2788,3132,3164,3180,3188,3244,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10346 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10346 132 4
  · have he : independentCachedBranchMembers10346.erase 132=independentCachedBranchMembers10344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10344
  · have he : independentCachedBranchMembers10346.filter (independentCachedEdge 132)=independentCachedBranchMembers10345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10345
def independentCachedBranchMembers10347 : Finset ℕ := ([12,18,36,66,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10347 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10347 250 5
  · have he : independentCachedBranchMembers10347.erase 250=independentCachedBranchMembers10339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10339
  · have he : independentCachedBranchMembers10347.filter (independentCachedEdge 250)=independentCachedBranchMembers10346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10346
def independentCachedBranchMembers10348 : Finset ℕ := ([18,66,132,1626,1650,1708,1716,1740,1748,2618,2650,2666,2674,2716,2732,2788,3130,3162,3178,3186,3244,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10348 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10348 5 (fun x => (if x<2666 then (if x<1708 then (if x<132 then (if x<66 then 0 else 1) else (if x<1626 then 0 else (if x<1650 then 0 else 1))) else (if x<1748 then (if x<1716 then 2 else (if x<1740 then 1 else 0)) else (if x<2618 then 2 else (if x<2650 then 0 else 1)))) else (if x<3162 then (if x<2732 then (if x<2674 then 3 else (if x<2716 then 4 else 1)) else (if x<2788 then 0 else (if x<3130 then 2 else 3))) else (if x<3244 then (if x<3178 then 4 else (if x<3186 then 1 else 0)) else (if x<3252 then 1 else (if x<3276 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10349 : Finset ℕ := ([66,1626,1708,1716,1740,1748,2666,2674,2716,2788,3178,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10349 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10349 4 (fun x => (if x<2666 then (if x<1716 then (if x<1626 then 0 else (if x<1708 then 0 else 1)) else (if x<1740 then 2 else (if x<1748 then 2 else 1))) else (if x<2788 then (if x<2674 then 0 else (if x<2716 then 3 else 1)) else (if x<3178 then 1 else (if x<3186 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10350 : Finset ℕ := ([18,66,132,1626,1650,1708,1716,1740,1748,1764,2618,2650,2666,2674,2716,2732,2788,3130,3162,3178,3186,3244,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10350 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10350 1764 4
  · have he : independentCachedBranchMembers10350.erase 1764=independentCachedBranchMembers10348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10348
  · have he : independentCachedBranchMembers10350.filter (independentCachedEdge 1764)=independentCachedBranchMembers10349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10349
def independentCachedBranchMembers10351 : Finset ℕ := ([18,1650,1708,1716,1740,1748,2618,2650,2716,2788,3130,3162] : List ℕ).toFinset
theorem independentCachedBranchBound10351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10351 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10351 4 (fun x => (if x<2618 then (if x<1716 then (if x<1650 then 0 else (if x<1708 then 0 else 1)) else (if x<1740 then 2 else (if x<1748 then 2 else 1))) else (if x<2788 then (if x<2650 then 0 else (if x<2716 then 3 else 1)) else (if x<3130 then 1 else (if x<3162 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10352 : Finset ℕ := ([18,66,132,1626,1650,1692,1708,1716,1740,1748,1764,2618,2650,2666,2674,2716,2732,2788,3130,3162,3178,3186,3244,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10352 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10352 1692 4
  · have he : independentCachedBranchMembers10352.erase 1692=independentCachedBranchMembers10350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10350
  · have he : independentCachedBranchMembers10352.filter (independentCachedEdge 1692)=independentCachedBranchMembers10351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10351
def independentCachedBranchMembers10353 : Finset ℕ := ([18,66,1626,1650,2618,2650,2666,2674,3130,3162,3178,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10353 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10353 4 (fun x => (if x<2666 then (if x<1650 then (if x<66 then 0 else (if x<1626 then 1 else 0)) else (if x<2618 then 1 else (if x<2650 then 0 else 1))) else (if x<3162 then (if x<2674 then 2 else (if x<3130 then 3 else 2)) else (if x<3178 then 3 else (if x<3186 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10354 : Finset ℕ := ([18,66,132,252,1626,1650,1692,1708,1716,1740,1748,1764,2618,2650,2666,2674,2716,2732,2788,3130,3162,3178,3186,3244,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10354 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10354 252 4
  · have he : independentCachedBranchMembers10354.erase 252=independentCachedBranchMembers10352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10352
  · have he : independentCachedBranchMembers10354.filter (independentCachedEdge 252)=independentCachedBranchMembers10353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10353
def independentCachedBranchMembers10355 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10355 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10355 130 5
  · have he : independentCachedBranchMembers10355.erase 130=independentCachedBranchMembers10347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10347
  · have he : independentCachedBranchMembers10355.filter (independentCachedEdge 130)=independentCachedBranchMembers10354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10354
def independentCachedBranchMembers10356 : Finset ℕ := ([12,66,130,250,1596,1650,1692,1706,1714,1738,1746,1764,2620,2652,2666,2674,2716,2738,2762,2770,2788,3130,3162,3180,3188,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10356 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10356 5 (fun x => (if x<2674 then (if x<1706 then (if x<250 then (if x<66 then 0 else (if x<130 then 0 else 1)) else (if x<1650 then (if x<1596 then 1 else 0) else (if x<1692 then 0 else 2))) else (if x<1764 then (if x<1738 then (if x<1714 then 1 else 2) else (if x<1746 then 2 else 1)) else (if x<2652 then (if x<2620 then 2 else 3) else (if x<2666 then 4 else 3)))) else (if x<3162 then (if x<2762 then (if x<2716 then 4 else (if x<2738 then 0 else 1)) else (if x<2788 then (if x<2770 then 1 else 0) else (if x<3130 then 3 else 3))) else (if x<3244 then (if x<3188 then (if x<3180 then 4 else 3) else (if x<3226 then 4 else 1)) else (if x<3276 then (if x<3252 then 0 else 2) else (if x<3298 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10357 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10357 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10357 3300 5
  · have he : independentCachedBranchMembers10357.erase 3300=independentCachedBranchMembers10355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10355
  · have he : independentCachedBranchMembers10357.filter (independentCachedEdge 3300)=independentCachedBranchMembers10356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10356
def independentCachedBranchMembers10358 : Finset ℕ := ([18,36,66,132,252,1596,1626,1644,1650,1692,1706,1716,1740,1746,1764,2620,2650,2668,2674,2716,2788,3130,3164,3178,3188,3226,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10358 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10358 5 (fun x => (if x<1764 then (if x<1644 then (if x<132 then (if x<36 then 0 else (if x<66 then 0 else 1)) else (if x<1596 then (if x<252 then 1 else 2) else (if x<1626 then 2 else 0))) else (if x<1706 then (if x<1650 then 0 else (if x<1692 then 1 else 3)) else (if x<1740 then (if x<1716 then 3 else 1) else (if x<1746 then 2 else 3)))) else (if x<3130 then (if x<2668 then (if x<2620 then 3 else (if x<2650 then 4 else 1)) else (if x<2716 then (if x<2674 then 2 else 4) else (if x<2788 then 1 else 0))) else (if x<3188 then (if x<3164 then 4 else (if x<3178 then 2 else 1)) else (if x<3244 then (if x<3226 then 4 else 0) else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10359 : Finset ℕ := ([36,132,1626,1706,1716,1764,2650,2788,3130,3178,3188,3226] : List ℕ).toFinset
theorem independentCachedBranchBound10359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10359 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10359 4 (fun x => (if x<2650 then (if x<1706 then (if x<132 then 0 else (if x<1626 then 1 else 0)) else (if x<1716 then 2 else (if x<1764 then 1 else 2))) else (if x<3178 then (if x<2788 then 1 else (if x<3130 then 0 else 2)) else (if x<3188 then 1 else (if x<3226 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10360 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1706,1716,1740,1746,1764,2620,2650,2668,2674,2716,2788,3130,3164,3178,3188,3226,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10360 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10360 12 4
  · have he : independentCachedBranchMembers10360.erase 12=independentCachedBranchMembers10358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10358
  · have he : independentCachedBranchMembers10360.filter (independentCachedEdge 12)=independentCachedBranchMembers10359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10359
def independentCachedBranchMembers10361 : Finset ℕ := ([132,252,1692,1706,1716,1740,1746,1764,2620,2650,2668,2674,3130,3164,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10361 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10361 4 (fun x => (if x<2620 then (if x<1716 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3130 then (if x<2668 then (if x<2650 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3178 then (if x<3164 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10362 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1706,1716,1740,1746,1764,2620,2650,2668,2674,2716,2770,2788,3130,3164,3178,3188,3226,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10362 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10362 2770 4
  · have he : independentCachedBranchMembers10362.erase 2770=independentCachedBranchMembers10360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10360
  · have he : independentCachedBranchMembers10362.filter (independentCachedEdge 2770)=independentCachedBranchMembers10361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10361
def independentCachedBranchMembers10363 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3242,3244,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10363 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10363 3242 5
  · have he : independentCachedBranchMembers10363.erase 3242=independentCachedBranchMembers10357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10357
  · have he : independentCachedBranchMembers10363.filter (independentCachedEdge 3242)=independentCachedBranchMembers10362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10362
def independentCachedBranchMembers10364 : Finset ℕ := ([18,36,130,250,1626,1644,1692,1706,1714,1738,1746,1764,2618,2650,2668,2676,2716,2738,2762,2770,2788,3132,3164,3178,3186,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10364 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10364 5 (fun x => (if x<2676 then (if x<1706 then (if x<250 then (if x<36 then 0 else (if x<130 then 0 else 1)) else (if x<1644 then (if x<1626 then 1 else 0) else (if x<1692 then 0 else 2))) else (if x<1764 then (if x<1738 then (if x<1714 then 1 else 2) else (if x<1746 then 2 else 1)) else (if x<2650 then (if x<2618 then 2 else 3) else (if x<2668 then 4 else 3)))) else (if x<3164 then (if x<2762 then (if x<2716 then 4 else (if x<2738 then 3 else 1)) else (if x<2788 then (if x<2770 then 1 else 0) else (if x<3132 then 0 else 3))) else (if x<3244 then (if x<3186 then (if x<3178 then 4 else 3) else (if x<3226 then 4 else 0)) else (if x<3276 then (if x<3252 then 0 else 2) else (if x<3298 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10365 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10365 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10365 3228 5
  · have he : independentCachedBranchMembers10365.erase 3228=independentCachedBranchMembers10363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10363
  · have he : independentCachedBranchMembers10365.filter (independentCachedEdge 3228)=independentCachedBranchMembers10364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10364
def independentCachedBranchMembers10366 : Finset ℕ := ([18,36,132,252,1626,1644,1690,1708,1716,1740,1748,1762,2620,2652,2666,2674,2716,2738,2762,2770,2788,3130,3162,3180,3188,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10366 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10366 5 (fun x => (if x<2674 then (if x<1708 then (if x<252 then (if x<36 then 0 else (if x<132 then 0 else 1)) else (if x<1644 then (if x<1626 then 1 else 0) else (if x<1690 then 0 else 2))) else (if x<1762 then (if x<1740 then (if x<1716 then 1 else 2) else (if x<1748 then 2 else 1)) else (if x<2652 then (if x<2620 then 2 else 3) else (if x<2666 then 4 else 3)))) else (if x<3162 then (if x<2762 then (if x<2716 then 4 else (if x<2738 then 1 else 2)) else (if x<2788 then (if x<2770 then 2 else 0) else (if x<3130 then 0 else 3))) else (if x<3244 then (if x<3188 then (if x<3180 then 4 else 3) else (if x<3226 then 4 else 0)) else (if x<3276 then (if x<3252 then 0 else 1) else (if x<3298 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10367 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10367 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10367 2786 5
  · have he : independentCachedBranchMembers10367.erase 2786=independentCachedBranchMembers10365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10365
  · have he : independentCachedBranchMembers10367.filter (independentCachedEdge 2786)=independentCachedBranchMembers10366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10366
end EntropyDesigns.QuadraticRefinement
