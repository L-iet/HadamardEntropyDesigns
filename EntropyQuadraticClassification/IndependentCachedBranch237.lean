/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch236
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10368 : Finset ℕ := ([66,130,250,1596,1626,1690,1708,1714,1738,1748,1762,2618,2652,2666,2676,2716,2770,2788,3132,3162,3180,3186,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10368 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10368 5 (fun x => (if x<2652 then (if x<1708 then (if x<1596 then (if x<130 then 0 else (if x<250 then 1 else 0)) else (if x<1626 then 1 else (if x<1690 then 0 else 1))) else (if x<1748 then (if x<1714 then 2 else (if x<1738 then 2 else 2)) else (if x<1762 then 2 else (if x<2618 then 0 else 3)))) else (if x<3132 then (if x<2716 then (if x<2666 then 3 else (if x<2676 then 0 else 1)) else (if x<2770 then 4 else (if x<2788 then 0 else 4))) else (if x<3186 then (if x<3162 then 3 else (if x<3180 then 3 else 1)) else (if x<3226 then 0 else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10369 : Finset ℕ := ([250,1714,1748,1762,2618,2652,2666,2716,3186,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10369 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10369 4 (fun x => (if x<2652 then (if x<1748 then (if x<1714 then 0 else 0) else (if x<1762 then 1 else (if x<2618 then 1 else 0))) else (if x<2716 then (if x<2666 then 1 else 1) else (if x<3186 then 2 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10370 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1708,1714,1738,1748,1762,2618,2652,2666,2676,2716,2770,2788,3132,3162,3180,3186,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10370 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10370 36 4
  · have he : independentCachedBranchMembers10370.erase 36=independentCachedBranchMembers10368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10368
  · have he : independentCachedBranchMembers10370.filter (independentCachedEdge 36)=independentCachedBranchMembers10369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10369
def independentCachedBranchMembers10371 : Finset ℕ := ([36,130,1626,1708,1714,1762,2652,2788,3132,3180,3186,3226] : List ℕ).toFinset
theorem independentCachedBranchBound10371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10371 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10371 4 (fun x => (if x<2652 then (if x<1708 then (if x<130 then 0 else (if x<1626 then 0 else 1)) else (if x<1714 then 2 else (if x<1762 then 1 else 2))) else (if x<3180 then (if x<2788 then 1 else (if x<3132 then 2 else 0)) else (if x<3186 then 3 else (if x<3226 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10372 : Finset ℕ := ([36,66,130,250,1596,1626,1650,1690,1708,1714,1738,1748,1762,2618,2652,2666,2676,2716,2770,2788,3132,3162,3180,3186,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10372 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10372 1650 4
  · have he : independentCachedBranchMembers10372.erase 1650=independentCachedBranchMembers10370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10370
  · have he : independentCachedBranchMembers10372.filter (independentCachedEdge 1650)=independentCachedBranchMembers10371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10371
def independentCachedBranchMembers10373 : Finset ℕ := ([66,250,1596,1690,1708,1714,2618,2716,3162,3180,3186,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10373 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10373 4 (fun x => (if x<2618 then (if x<1690 then (if x<250 then 0 else (if x<1596 then 0 else 1)) else (if x<1708 then 1 else (if x<1714 then 2 else 2))) else (if x<3180 then (if x<2716 then 1 else (if x<3162 then 1 else 0)) else (if x<3186 then 2 else (if x<3298 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10374 : Finset ℕ := ([36,66,130,250,1596,1626,1644,1650,1690,1708,1714,1738,1748,1762,2618,2652,2666,2676,2716,2770,2788,3132,3162,3180,3186,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10374 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10374 1644 4
  · have he : independentCachedBranchMembers10374.erase 1644=independentCachedBranchMembers10372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10372
  · have he : independentCachedBranchMembers10374.filter (independentCachedEdge 1644)=independentCachedBranchMembers10373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10373
def independentCachedBranchMembers10375 : Finset ℕ := ([66,130,1596,1738,1748,1762,2652,2666,2676,2716,3132,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10375 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10375 4 (fun x => (if x<2652 then (if x<1738 then (if x<130 then 0 else (if x<1596 then 1 else 0)) else (if x<1748 then 1 else (if x<1762 then 2 else 2))) else (if x<2716 then (if x<2666 then 2 else (if x<2676 then 2 else 1)) else (if x<3132 then 0 else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10376 : Finset ℕ := ([18,36,66,130,250,1596,1626,1644,1650,1690,1708,1714,1738,1748,1762,2618,2652,2666,2676,2716,2770,2788,3132,3162,3180,3186,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10376 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10376 18 4
  · have he : independentCachedBranchMembers10376.erase 18=independentCachedBranchMembers10374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10374
  · have he : independentCachedBranchMembers10376.filter (independentCachedEdge 18)=independentCachedBranchMembers10375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10375
def independentCachedBranchMembers10377 : Finset ℕ := ([36,250,1626,1690,1738,1748,2618,2666,2676,2788,3162,3226] : List ℕ).toFinset
theorem independentCachedBranchBound10377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10377 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10377 4 (fun x => (if x<2618 then (if x<1690 then (if x<250 then 0 else (if x<1626 then 1 else 0)) else (if x<1738 then 1 else (if x<1748 then 2 else 2))) else (if x<2788 then (if x<2666 then 1 else (if x<2676 then 2 else 2)) else (if x<3162 then 0 else (if x<3226 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10378 : Finset ℕ := ([12,18,36,66,130,250,1596,1626,1644,1650,1690,1708,1714,1738,1748,1762,2618,2652,2666,2676,2716,2770,2788,3132,3162,3180,3186,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10378 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10378 12 4
  · have he : independentCachedBranchMembers10378.erase 12=independentCachedBranchMembers10376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10376
  · have he : independentCachedBranchMembers10378.filter (independentCachedEdge 12)=independentCachedBranchMembers10377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10377
def independentCachedBranchMembers10379 : Finset ℕ := ([130,250,1690,1708,1714,1738,1748,1762,2618,2652,2666,2676,3132,3162,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10379 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10379 4 (fun x => (if x<2618 then (if x<1714 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3132 then (if x<2666 then (if x<2652 then 2 else 2) else (if x<2676 then 3 else 3)) else (if x<3180 then (if x<3162 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10380 : Finset ℕ := ([12,18,36,66,130,250,1596,1626,1644,1650,1690,1708,1714,1738,1748,1762,2618,2652,2666,2676,2716,2770,2788,3132,3162,3180,3186,3226,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10380 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10380 3244 4
  · have he : independentCachedBranchMembers10380.erase 3244=independentCachedBranchMembers10378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10378
  · have he : independentCachedBranchMembers10380.filter (independentCachedEdge 3244)=independentCachedBranchMembers10379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10379
def independentCachedBranchMembers10381 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10381 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10381 2772 5
  · have he : independentCachedBranchMembers10381.erase 2772=independentCachedBranchMembers10367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10367
  · have he : independentCachedBranchMembers10381.filter (independentCachedEdge 2772)=independentCachedBranchMembers10380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10380
def independentCachedBranchMembers10382 : Finset ℕ := ([12,66,132,252,1596,1650,1690,1708,1716,1740,1748,1762,2618,2650,2668,2676,2716,2738,2762,2770,2788,3132,3164,3178,3186,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10382 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10382 5 (fun x => (if x<2676 then (if x<1708 then (if x<252 then (if x<66 then 0 else (if x<132 then 0 else 1)) else (if x<1650 then (if x<1596 then 1 else 0) else (if x<1690 then 0 else 2))) else (if x<1762 then (if x<1740 then (if x<1716 then 1 else 2) else (if x<1748 then 2 else 1)) else (if x<2650 then (if x<2618 then 2 else 3) else (if x<2668 then 4 else 3)))) else (if x<3164 then (if x<2762 then (if x<2716 then 4 else (if x<2738 then 0 else 2)) else (if x<2788 then (if x<2770 then 2 else 0) else (if x<3132 then 1 else 3))) else (if x<3244 then (if x<3186 then (if x<3178 then 4 else 3) else (if x<3226 then 4 else 3)) else (if x<3276 then (if x<3252 then 0 else 1) else (if x<3298 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10383 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2762,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10383 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10383 2714 5
  · have he : independentCachedBranchMembers10383.erase 2714=independentCachedBranchMembers10381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10381
  · have he : independentCachedBranchMembers10383.filter (independentCachedEdge 2714)=independentCachedBranchMembers10382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10382
def independentCachedBranchMembers10384 : Finset ℕ := ([132,252,1596,1626,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2788,3130,3164,3180,3186,3226,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10384 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10384 5 (fun x => (if x<2676 then (if x<1714 then (if x<1626 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 0 else 2))) else (if x<1764 then (if x<1738 then 1 else (if x<1748 then 2 else 1)) else (if x<2650 then (if x<2620 then 0 else 2) else (if x<2666 then 2 else 3)))) else (if x<3180 then (if x<2738 then (if x<2716 then 3 else (if x<2732 then 4 else 0)) else (if x<3130 then (if x<2788 then 3 else 4) else (if x<3164 then 1 else 1))) else (if x<3252 then (if x<3186 then 3 else (if x<3226 then 3 else 4)) else (if x<3282 then (if x<3276 then 0 else 0) else (if x<3298 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10385 : Finset ℕ := ([252,1714,1748,1764,2676,2738,2788,3130,3164,3180,3226,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10385 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10385 4 (fun x => (if x<2788 then (if x<1764 then (if x<1714 then 0 else (if x<1748 then 1 else 0)) else (if x<2676 then 1 else (if x<2738 then 0 else 2))) else (if x<3180 then (if x<3130 then 2 else (if x<3164 then 1 else 0)) else (if x<3226 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10386 : Finset ℕ := ([66,132,252,1596,1626,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2788,3130,3164,3180,3186,3226,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10386 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10386 66 4
  · have he : independentCachedBranchMembers10386.erase 66=independentCachedBranchMembers10384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10384
  · have he : independentCachedBranchMembers10386.filter (independentCachedEdge 66)=independentCachedBranchMembers10385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10385
def independentCachedBranchMembers10387 : Finset ℕ := ([132,1692,1714,1748,2666,2716,2738,3130,3164,3186,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10387 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10387 4 (fun x => (if x<2738 then (if x<1748 then (if x<1692 then 0 else (if x<1714 then 0 else 1)) else (if x<2666 then 1 else (if x<2716 then 0 else 2))) else (if x<3186 then (if x<3130 then 2 else (if x<3164 then 1 else 1)) else (if x<3276 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10388 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2788,3130,3164,3180,3186,3226,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10388 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10388 36 4
  · have he : independentCachedBranchMembers10388.erase 36=independentCachedBranchMembers10386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10386
  · have he : independentCachedBranchMembers10388.filter (independentCachedEdge 36)=independentCachedBranchMembers10387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10387
def independentCachedBranchMembers10389 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1764,2620,2650,2716,2788,3130,3164,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10389 4 (fun x => (if x<2620 then (if x<1596 then (if x<132 then (if x<66 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1692 then (if x<1626 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3130 then (if x<2716 then (if x<2650 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3164 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10390 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2788,3130,3164,3180,3186,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10390 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10390 3242 4
  · have he : independentCachedBranchMembers10390.erase 3242=independentCachedBranchMembers10388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10388
  · have he : independentCachedBranchMembers10390.filter (independentCachedEdge 3242)=independentCachedBranchMembers10389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10389
def independentCachedBranchMembers10391 : Finset ℕ := ([36,66,1596,1626,1708,1714,1738,1748,2666,2676,2716,2788,3180,3186,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10391 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10391 4 (fun x => (if x<2666 then (if x<1708 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1626 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3180 then (if x<2716 then (if x<2676 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3186 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10392 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2772,2788,3130,3164,3180,3186,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10392 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10392 2772 4
  · have he : independentCachedBranchMembers10392.erase 2772=independentCachedBranchMembers10390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10390
  · have he : independentCachedBranchMembers10392.filter (independentCachedEdge 2772)=independentCachedBranchMembers10391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10391
def independentCachedBranchMembers10393 : Finset ℕ := ([132,252,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,3130,3164,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10393 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10393 4 (fun x => (if x<2620 then (if x<1714 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3130 then (if x<2666 then (if x<2650 then 2 else 2) else (if x<2676 then 3 else 3)) else (if x<3180 then (if x<3164 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10394 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10394 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10394 2762 4
  · have he : independentCachedBranchMembers10394.erase 2762=independentCachedBranchMembers10392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10392
  · have he : independentCachedBranchMembers10394.filter (independentCachedEdge 2762)=independentCachedBranchMembers10393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10393
def independentCachedBranchMembers10395 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2762,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10395 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10395 3250 5
  · have he : independentCachedBranchMembers10395.erase 3250=independentCachedBranchMembers10383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10383
  · have he : independentCachedBranchMembers10395.filter (independentCachedEdge 3250)=independentCachedBranchMembers10394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10394
def independentCachedBranchMembers10396 : Finset ℕ := ([66,130,250,1596,1626,1690,1706,1716,1740,1746,1762,2618,2652,2668,2674,2716,2732,2738,2762,2788,3132,3162,3178,3188,3226,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10396 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10396 5 (fun x => (if x<2674 then (if x<1716 then (if x<1596 then (if x<130 then 0 else (if x<250 then 1 else 0)) else (if x<1690 then (if x<1626 then 1 else 0) else (if x<1706 then 1 else 2))) else (if x<1762 then (if x<1740 then 2 else (if x<1746 then 2 else 2)) else (if x<2652 then (if x<2618 then 0 else 3) else (if x<2668 then 3 else 1)))) else (if x<3162 then (if x<2738 then (if x<2716 then 0 else (if x<2732 then 4 else 2)) else (if x<2788 then (if x<2762 then 2 else 0) else (if x<3132 then 4 else 3))) else (if x<3226 then (if x<3178 then 3 else (if x<3188 then 0 else 1)) else (if x<3282 then (if x<3276 then 4 else 3) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10397 : Finset ℕ := ([250,1706,1740,1762,2618,2652,2674,2716,2738,3178,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10397 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10397 4 (fun x => (if x<2674 then (if x<1762 then (if x<1706 then 0 else (if x<1740 then 0 else 1)) else (if x<2618 then 1 else (if x<2652 then 0 else 1))) else (if x<3178 then (if x<2716 then 1 else (if x<2738 then 2 else 2)) else (if x<3276 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10398 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1706,1716,1740,1746,1762,2618,2652,2668,2674,2716,2732,2738,2762,2788,3132,3162,3178,3188,3226,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10398 36 4
  · have he : independentCachedBranchMembers10398.erase 36=independentCachedBranchMembers10396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10396
  · have he : independentCachedBranchMembers10398.filter (independentCachedEdge 36)=independentCachedBranchMembers10397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10397
def independentCachedBranchMembers10399 : Finset ℕ := ([130,250,1690,1706,1716,1740,1746,1762,2618,2652,2668,2674,3132,3162,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10399 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10399 4 (fun x => (if x<2618 then (if x<1716 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3132 then (if x<2668 then (if x<2652 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3178 then (if x<3162 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
