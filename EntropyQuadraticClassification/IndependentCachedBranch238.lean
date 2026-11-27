/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch237
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10400 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1706,1716,1740,1746,1762,2618,2652,2668,2674,2716,2732,2738,2762,2788,3132,3162,3178,3188,3226,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10400 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10400 3252 4
  · have he : independentCachedBranchMembers10400.erase 3252=independentCachedBranchMembers10398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10398
  · have he : independentCachedBranchMembers10400.filter (independentCachedEdge 3252)=independentCachedBranchMembers10399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10399
def independentCachedBranchMembers10401 : Finset ℕ := ([36,66,1596,1626,1706,1716,1740,1746,2668,2674,2716,2788,3178,3188,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10401 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10401 4 (fun x => (if x<2668 then (if x<1706 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1626 then 0 else 0)) else (if x<1740 then (if x<1716 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3178 then (if x<2716 then (if x<2674 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3188 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10402 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1706,1716,1740,1746,1762,2618,2652,2668,2674,2716,2732,2738,2762,2788,3132,3162,3178,3188,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10402 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10402 3242 4
  · have he : independentCachedBranchMembers10402.erase 3242=independentCachedBranchMembers10400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10400
  · have he : independentCachedBranchMembers10402.filter (independentCachedEdge 3242)=independentCachedBranchMembers10401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10401
def independentCachedBranchMembers10403 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1762,2618,2652,2716,2788,3132,3162,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10403 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10403 4 (fun x => (if x<2618 then (if x<1596 then (if x<130 then (if x<66 then 0 else 0) else (if x<250 then 1 else 1)) else (if x<1690 then (if x<1626 then 0 else 0) else (if x<1762 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2652 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3162 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10404 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1706,1716,1740,1746,1762,2618,2652,2668,2674,2716,2732,2738,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10404 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10404 2772 4
  · have he : independentCachedBranchMembers10404.erase 2772=independentCachedBranchMembers10402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10402
  · have he : independentCachedBranchMembers10404.filter (independentCachedEdge 2772)=independentCachedBranchMembers10403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10403
def independentCachedBranchMembers10405 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10405 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10405 2764 5
  · have he : independentCachedBranchMembers10405.erase 2764=independentCachedBranchMembers10395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10395
  · have he : independentCachedBranchMembers10405.filter (independentCachedEdge 2764)=independentCachedBranchMembers10404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10404
def independentCachedBranchMembers10406 : Finset ℕ := ([66,250,1596,1626,1644,1692,1706,1714,1740,1748,1762,2618,2652,2666,2674,2732,2762,2770,2788,3130,3164,3178,3186,3226,3244,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10406 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10406 5 (fun x => (if x<2666 then (if x<1706 then (if x<1626 then (if x<250 then 0 else (if x<1596 then 0 else 1)) else (if x<1644 then 0 else (if x<1692 then 2 else 2))) else (if x<1748 then (if x<1714 then 1 else (if x<1740 then 3 else 1)) else (if x<2618 then (if x<1762 then 3 else 0) else (if x<2652 then 1 else 1)))) else (if x<3164 then (if x<2762 then (if x<2674 then 0 else (if x<2732 then 4 else 1)) else (if x<2788 then (if x<2770 then 1 else 0) else (if x<3130 then 4 else 3))) else (if x<3226 then (if x<3178 then 2 else (if x<3186 then 2 else 0)) else (if x<3252 then (if x<3244 then 2 else 2) else (if x<3282 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10407 : Finset ℕ := ([250,1596,1644,1706,1714,1762,2652,2762,2770,3164,3226,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10407 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10407 4 (fun x => (if x<2652 then (if x<1706 then (if x<1596 then 0 else (if x<1644 then 1 else 2)) else (if x<1714 then 0 else (if x<1762 then 1 else 2))) else (if x<3164 then (if x<2762 then 1 else (if x<2770 then 0 else 1)) else (if x<3226 then 2 else (if x<3282 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10408 : Finset ℕ := ([66,132,250,1596,1626,1644,1692,1706,1714,1740,1748,1762,2618,2652,2666,2674,2732,2762,2770,2788,3130,3164,3178,3186,3226,3244,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10408 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10408 132 4
  · have he : independentCachedBranchMembers10408.erase 132=independentCachedBranchMembers10406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10406
  · have he : independentCachedBranchMembers10408.filter (independentCachedEdge 132)=independentCachedBranchMembers10407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10407
def independentCachedBranchMembers10409 : Finset ℕ := ([66,1596,1692,1706,1748,1762,2652,2666,2762,3164,3178,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10409 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10409 4 (fun x => (if x<2652 then (if x<1706 then (if x<1596 then 0 else (if x<1692 then 0 else 1)) else (if x<1748 then 1 else (if x<1762 then 2 else 2))) else (if x<3164 then (if x<2666 then 1 else (if x<2762 then 1 else 0)) else (if x<3178 then 2 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10410 : Finset ℕ := ([18,66,132,250,1596,1626,1644,1692,1706,1714,1740,1748,1762,2618,2652,2666,2674,2732,2762,2770,2788,3130,3164,3178,3186,3226,3244,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10410 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10410 18 4
  · have he : independentCachedBranchMembers10410.erase 18=independentCachedBranchMembers10408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10408
  · have he : independentCachedBranchMembers10410.filter (independentCachedEdge 18)=independentCachedBranchMembers10409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10409
def independentCachedBranchMembers10411 : Finset ℕ := ([250,1596,1692,1706,1714,2652,2666,2674,2762,2770,2788,3130,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10411 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10411 4 (fun x => (if x<2674 then (if x<1706 then (if x<1596 then 0 else (if x<1692 then 1 else 2)) else (if x<2652 then (if x<1714 then 0 else 1) else (if x<2666 then 1 else 0))) else (if x<3130 then (if x<2770 then (if x<2762 then 2 else 3) else (if x<2788 then 1 else 3)) else (if x<3244 then (if x<3226 then 0 else 3) else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10412 : Finset ℕ := ([1706,1714,2652,2788,3130,3226] : List ℕ).toFinset
theorem independentCachedBranchBound10412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10412 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10412 3 (fun x => (if x<2788 then (if x<1714 then 0 else (if x<2652 then 1 else 0)) else (if x<3130 then 2 else (if x<3226 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10413 : Finset ℕ := ([66,250,1596,1692,1706,1714,2652,2666,2674,2762,2770,2788,3130,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10413 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10413 66 3
  · have he : independentCachedBranchMembers10413.erase 66=independentCachedBranchMembers10411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10411
  · have he : independentCachedBranchMembers10413.filter (independentCachedEdge 66)=independentCachedBranchMembers10412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10412
def independentCachedBranchMembers10414 : Finset ℕ := ([18,66,132,250,1596,1626,1644,1692,1706,1714,1740,1748,1762,2618,2652,2666,2674,2732,2762,2770,2788,3130,3164,3178,3186,3226,3244,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10414 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10414 3300 4
  · have he : independentCachedBranchMembers10414.erase 3300=independentCachedBranchMembers10410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10410
  · have he : independentCachedBranchMembers10414.filter (independentCachedEdge 3300)=independentCachedBranchMembers10413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10413
def independentCachedBranchMembers10415 : Finset ℕ := ([66,132,1596,1740,1748,1762,2618,2762,2770,2788,3164,3178,3186,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10415 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10415 4 (fun x => (if x<2770 then (if x<1748 then (if x<1596 then (if x<132 then 0 else 0) else (if x<1740 then 1 else 1)) else (if x<2618 then (if x<1762 then 2 else 2) else (if x<2762 then 1 else 1))) else (if x<3186 then (if x<3164 then (if x<2788 then 2 else 2) else (if x<3178 then 3 else 0)) else (if x<3244 then (if x<3226 then 3 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10416 : Finset ℕ := ([18,66,132,250,1596,1626,1644,1692,1706,1714,1740,1748,1762,2618,2652,2666,2674,2714,2732,2762,2770,2788,3130,3164,3178,3186,3226,3244,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10416 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10416 2714 4
  · have he : independentCachedBranchMembers10416.erase 2714=independentCachedBranchMembers10414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10414
  · have he : independentCachedBranchMembers10416.filter (independentCachedEdge 2714)=independentCachedBranchMembers10415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10415
def independentCachedBranchMembers10417 : Finset ℕ := ([250,1692,1706,1714,1740,1748,1762,2618,2652,2666,2674,3130,3164,3178,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10417 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10417 4 (fun x => (if x<2618 then (if x<1714 then (if x<1692 then 0 else (if x<1706 then 1 else 0)) else (if x<1748 then (if x<1740 then 1 else 2) else (if x<1762 then 3 else 2))) else (if x<3130 then (if x<2666 then (if x<2652 then 0 else 1) else (if x<2674 then 3 else 1)) else (if x<3178 then (if x<3164 then 3 else 2) else (if x<3186 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10418 : Finset ℕ := ([250,1706,1714,1762,2652,3164] : List ℕ).toFinset
theorem independentCachedBranchBound10418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10418 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10418 3 (fun x => (if x<1762 then (if x<1706 then 0 else (if x<1714 then 0 else 1)) else (if x<2652 then 2 else (if x<3164 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10419 : Finset ℕ := ([132,250,1692,1706,1714,1740,1748,1762,2618,2652,2666,2674,3130,3164,3178,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10419 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10419 132 3
  · have he : independentCachedBranchMembers10419.erase 132=independentCachedBranchMembers10417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10417
  · have he : independentCachedBranchMembers10419.filter (independentCachedEdge 132)=independentCachedBranchMembers10418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10418
def independentCachedBranchMembers10420 : Finset ℕ := ([18,36,66,132,250,1596,1626,1644,1692,1706,1714,1740,1748,1762,2618,2652,2666,2674,2714,2732,2762,2770,2788,3130,3164,3178,3186,3226,3244,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10420 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10420 36 4
  · have he : independentCachedBranchMembers10420.erase 36=independentCachedBranchMembers10416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10416
  · have he : independentCachedBranchMembers10420.filter (independentCachedEdge 36)=independentCachedBranchMembers10419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10419
def independentCachedBranchMembers10421 : Finset ℕ := ([12,18,36,66,130,132,250,252,1596,1626,1628,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10421 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10421 1628 5
  · have he : independentCachedBranchMembers10421.erase 1628=independentCachedBranchMembers10405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10405
  · have he : independentCachedBranchMembers10421.filter (independentCachedEdge 1628)=independentCachedBranchMembers10420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10420
def independentCachedBranchMembers10422 : Finset ℕ := ([12,36,130,252,1596,1626,1650,1690,1706,1714,1740,1748,1764,2618,2652,2668,2676,2716,2732,2762,2770,3130,3164,3180,3188,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10422 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10422 5 (fun x => (if x<2652 then (if x<1690 then (if x<252 then (if x<36 then 0 else (if x<130 then 1 else 0)) else (if x<1626 then (if x<1596 then 1 else 0) else (if x<1650 then 2 else 3))) else (if x<1740 then (if x<1706 then 3 else (if x<1714 then 2 else 0)) else (if x<1764 then (if x<1748 then 2 else 3) else (if x<2618 then 1 else 2)))) else (if x<3130 then (if x<2716 then (if x<2668 then 0 else (if x<2676 then 1 else 3)) else (if x<2762 then (if x<2732 then 3 else 2) else (if x<2770 then 2 else 0))) else (if x<3244 then (if x<3180 then (if x<3164 then 4 else 4) else (if x<3188 then 0 else 1)) else (if x<3282 then (if x<3252 then 1 else 4) else (if x<3298 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10423 : Finset ℕ := ([130,1626,1706,1714,1764,2618,2668,2676,2716,2762,2770,3164,3244,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10423 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10423 4 (fun x => (if x<2676 then (if x<1714 then (if x<1626 then 0 else (if x<1706 then 1 else 0)) else (if x<2618 then (if x<1764 then 1 else 2) else (if x<2668 then 1 else 2))) else (if x<3164 then (if x<2762 then (if x<2716 then 0 else 3) else (if x<2770 then 3 else 1)) else (if x<3252 then (if x<3244 then 0 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10424 : Finset ℕ := ([1706,1714,2618,2716,3164,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10424 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10424 3 (fun x => (if x<2716 then (if x<1714 then 0 else (if x<2618 then 1 else 0)) else (if x<3164 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10425 : Finset ℕ := ([36,130,1626,1706,1714,1764,2618,2668,2676,2716,2762,2770,3164,3244,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10425 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10425 36 3
  · have he : independentCachedBranchMembers10425.erase 36=independentCachedBranchMembers10423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10423
  · have he : independentCachedBranchMembers10425.filter (independentCachedEdge 36)=independentCachedBranchMembers10424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10424
def independentCachedBranchMembers10426 : Finset ℕ := ([12,36,130,252,1596,1626,1650,1690,1706,1714,1740,1748,1764,2618,2652,2668,2676,2716,2732,2762,2770,3130,3164,3180,3188,3228,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10426 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10426 3228 4
  · have he : independentCachedBranchMembers10426.erase 3228=independentCachedBranchMembers10422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10422
  · have he : independentCachedBranchMembers10426.filter (independentCachedEdge 3228)=independentCachedBranchMembers10425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10425
def independentCachedBranchMembers10427 : Finset ℕ := ([36,252,1626,1690,1740,1748,2652,2716,2762,2770,3130,3180,3188,3244,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10427 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10427 4 (fun x => (if x<2762 then (if x<1740 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1690 then 1 else 2)) else (if x<2652 then (if x<1748 then 1 else 2) else (if x<2716 then 1 else 2))) else (if x<3188 then (if x<3130 then (if x<2770 then 1 else 2) else (if x<3180 then 3 else 0)) else (if x<3252 then (if x<3244 then 3 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10428 : Finset ℕ := ([12,36,130,252,1596,1626,1650,1690,1706,1714,1740,1748,1764,2618,2652,2668,2676,2716,2732,2762,2770,2786,3130,3164,3180,3188,3228,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10428 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10428 2786 4
  · have he : independentCachedBranchMembers10428.erase 2786=independentCachedBranchMembers10426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10426
  · have he : independentCachedBranchMembers10428.filter (independentCachedEdge 2786)=independentCachedBranchMembers10427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10427
def independentCachedBranchMembers10429 : Finset ℕ := ([130,252,1690,1706,1714,1740,1748,1764,2618,2652,2668,2676,3130,3164,3180,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10429 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10429 4 (fun x => (if x<2618 then (if x<1714 then (if x<1690 then (if x<252 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<1748 then (if x<1740 then 3 else 1) else (if x<1764 then 3 else 2))) else (if x<3130 then (if x<2668 then (if x<2652 then 2 else 1) else (if x<2676 then 0 else 2)) else (if x<3180 then (if x<3164 then 3 else 3) else (if x<3188 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10430 : Finset ℕ := ([12,36,66,130,252,1596,1626,1650,1690,1706,1714,1740,1748,1764,2618,2652,2668,2676,2716,2732,2762,2770,2786,3130,3164,3180,3188,3228,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10430 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10430 66 4
  · have he : independentCachedBranchMembers10430.erase 66=independentCachedBranchMembers10428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10428
  · have he : independentCachedBranchMembers10430.filter (independentCachedEdge 66)=independentCachedBranchMembers10429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10429
def independentCachedBranchMembers10431 : Finset ℕ := ([12,18,36,66,130,132,250,252,1594,1596,1626,1628,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10431 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10431 1594 5
  · have he : independentCachedBranchMembers10431.erase 1594=independentCachedBranchMembers10421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10421
  · have he : independentCachedBranchMembers10431.filter (independentCachedEdge 1594)=independentCachedBranchMembers10430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10430
end EntropyDesigns.QuadraticRefinement
