/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch238
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10432 : Finset ℕ := ([36,66,132,250,1626,1650,1692,1708,1716,1738,1746,1762,2620,2650,2666,2674,2716,2732,2762,2770,3132,3162,3178,3186,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10432 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10432 5 (fun x => (if x<2666 then (if x<1708 then (if x<250 then (if x<66 then 0 else (if x<132 then 0 else 1)) else (if x<1650 then (if x<1626 then 2 else 0) else (if x<1692 then 1 else 3))) else (if x<1746 then (if x<1716 then 4 else (if x<1738 then 1 else 2)) else (if x<2620 then (if x<1762 then 3 else 4) else (if x<2650 then 3 else 1)))) else (if x<3162 then (if x<2732 then (if x<2674 then 2 else (if x<2716 then 3 else 1)) else (if x<2770 then (if x<2762 then 0 else 0) else (if x<3132 then 2 else 4))) else (if x<3244 then (if x<3178 then 2 else (if x<3186 then 1 else 4)) else (if x<3282 then (if x<3252 then 1 else 0) else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10433 : Finset ℕ := ([36,132,250,1626,1716,1738,2650,2666,2762,3162,3178,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10433 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10433 4 (fun x => (if x<2650 then (if x<1626 then (if x<132 then 0 else (if x<250 then 1 else 2)) else (if x<1716 then 0 else (if x<1738 then 1 else 2))) else (if x<3162 then (if x<2666 then 1 else (if x<2762 then 2 else 0)) else (if x<3178 then 2 else (if x<3252 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10434 : Finset ℕ := ([12,36,66,132,250,1626,1650,1692,1708,1716,1738,1746,1762,2620,2650,2666,2674,2716,2732,2762,2770,3132,3162,3178,3186,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10434 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10434 12 4
  · have he : independentCachedBranchMembers10434.erase 12=independentCachedBranchMembers10432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10432
  · have he : independentCachedBranchMembers10434.filter (independentCachedEdge 12)=independentCachedBranchMembers10433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10433
def independentCachedBranchMembers10435 : Finset ℕ := ([36,250,1626,1692,1738,1746,2650,2716,2762,2770,3132,3178,3186,3244,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10435 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10435 4 (fun x => (if x<2762 then (if x<1738 then (if x<1626 then (if x<250 then 0 else 1) else (if x<1692 then 0 else 2)) else (if x<2650 then (if x<1746 then 1 else 2) else (if x<2716 then 1 else 3))) else (if x<3186 then (if x<3132 then (if x<2770 then 0 else 3) else (if x<3178 then 2 else 1)) else (if x<3252 then (if x<3244 then 2 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10436 : Finset ℕ := ([12,36,66,132,250,1626,1650,1692,1708,1716,1738,1746,1762,2620,2650,2666,2674,2716,2732,2762,2770,3132,3162,3178,3186,3228,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10436 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10436 3228 4
  · have he : independentCachedBranchMembers10436.erase 3228=independentCachedBranchMembers10434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10434
  · have he : independentCachedBranchMembers10436.filter (independentCachedEdge 3228)=independentCachedBranchMembers10435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10435
def independentCachedBranchMembers10437 : Finset ℕ := ([36,132,1626,1708,1716,1762,2620,2666,2674,2716,2762,2770,3162,3244,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10437 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10437 4 (fun x => (if x<2674 then (if x<1716 then (if x<1626 then (if x<132 then 0 else 1) else (if x<1708 then 0 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2666 then 2 else 2))) else (if x<3162 then (if x<2762 then (if x<2716 then 1 else 3) else (if x<2770 then 0 else 3)) else (if x<3252 then (if x<3244 then 1 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10438 : Finset ℕ := ([12,36,66,132,250,1626,1650,1692,1708,1716,1738,1746,1762,2620,2650,2666,2674,2716,2732,2762,2770,2786,3132,3162,3178,3186,3228,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10438 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10438 2786 4
  · have he : independentCachedBranchMembers10438.erase 2786=independentCachedBranchMembers10436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10436
  · have he : independentCachedBranchMembers10438.filter (independentCachedEdge 2786)=independentCachedBranchMembers10437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10437
def independentCachedBranchMembers10439 : Finset ℕ := ([132,250,1692,1708,1716,1738,1746,1762,2620,2650,2666,2674,3132,3162,3178,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10439 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10439 4 (fun x => (if x<2620 then (if x<1716 then (if x<1692 then (if x<250 then 0 else 1) else (if x<1708 then 0 else 2)) else (if x<1746 then (if x<1738 then 3 else 1) else (if x<1762 then 3 else 2))) else (if x<3132 then (if x<2666 then (if x<2650 then 2 else 1) else (if x<2674 then 0 else 2)) else (if x<3178 then (if x<3162 then 3 else 3) else (if x<3186 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10440 : Finset ℕ := ([12,36,66,132,250,1596,1626,1650,1692,1708,1716,1738,1746,1762,2620,2650,2666,2674,2716,2732,2762,2770,2786,3132,3162,3178,3186,3228,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10440 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10440 1596 4
  · have he : independentCachedBranchMembers10440.erase 1596=independentCachedBranchMembers10438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10438
  · have he : independentCachedBranchMembers10440.filter (independentCachedEdge 1596)=independentCachedBranchMembers10439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10439
def independentCachedBranchMembers10441 : Finset ℕ := ([12,18,36,66,68,130,132,250,252,1594,1596,1626,1628,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10441 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10441 68 5
  · have he : independentCachedBranchMembers10441.erase 68=independentCachedBranchMembers10431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10431
  · have he : independentCachedBranchMembers10441.filter (independentCachedEdge 68)=independentCachedBranchMembers10440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10440
def independentCachedBranchMembers10442 : Finset ℕ := ([36,130,252,1596,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,2762,2770,2788,3132,3162,3180,3188,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10442 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10442 5 (fun x => (if x<2668 then (if x<1716 then (if x<1596 then (if x<130 then 0 else (if x<252 then 0 else 1)) else (if x<1690 then 0 else (if x<1708 then 0 else 1))) else (if x<1764 then (if x<1738 then 2 else (if x<1746 then 3 else 2)) else (if x<2620 then 3 else (if x<2650 then 1 else 2)))) else (if x<3162 then (if x<2770 then (if x<2676 then 0 else (if x<2762 then 3 else 0)) else (if x<2788 then 4 else (if x<3132 then 1 else 4))) else (if x<3226 then (if x<3180 then 4 else (if x<3188 then 1 else 0)) else (if x<3244 then 3 else (if x<3252 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10443 : Finset ℕ := ([130,252,1690,1764,2668,2676,2788,3180,3188,3226] : List ℕ).toFinset
theorem independentCachedBranchBound10443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10443 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10443 4 (fun x => (if x<2676 then (if x<1690 then (if x<252 then 0 else 1) else (if x<1764 then 0 else (if x<2668 then 1 else 0))) else (if x<3180 then (if x<2788 then 1 else 2) else (if x<3188 then 1 else (if x<3226 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10444 : Finset ℕ := ([36,66,130,252,1596,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,2762,2770,2788,3132,3162,3180,3188,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10444 66 4
  · have he : independentCachedBranchMembers10444.erase 66=independentCachedBranchMembers10442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10442
  · have he : independentCachedBranchMembers10444.filter (independentCachedEdge 66)=independentCachedBranchMembers10443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10443
def independentCachedBranchMembers10445 : Finset ℕ := ([252,1716,1746,1764,2676,2770,2788,3132,3162,3180,3226,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10445 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10445 4 (fun x => (if x<2788 then (if x<1764 then (if x<1716 then 0 else (if x<1746 then 0 else 1)) else (if x<2676 then 1 else (if x<2770 then 0 else 2))) else (if x<3180 then (if x<3132 then 2 else (if x<3162 then 0 else 1)) else (if x<3226 then 1 else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10446 : Finset ℕ := ([36,66,130,252,1596,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,2762,2770,2788,3132,3162,3180,3188,3226,3244,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10446 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10446 3282 4
  · have he : independentCachedBranchMembers10446.erase 3282=independentCachedBranchMembers10444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10444
  · have he : independentCachedBranchMembers10446.filter (independentCachedEdge 3282)=independentCachedBranchMembers10445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10445
def independentCachedBranchMembers10447 : Finset ℕ := ([130,1690,1708,1738,2620,2650,2668,2770,2788,3188,3226,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10447 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10447 4 (fun x => (if x<2668 then (if x<1738 then (if x<1690 then 0 else (if x<1708 then 0 else 1)) else (if x<2620 then 1 else (if x<2650 then 1 else 1))) else (if x<3188 then (if x<2770 then 0 else (if x<2788 then 2 else 2)) else (if x<3226 then 0 else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10448 : Finset ℕ := ([36,66,130,252,1596,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,2732,2762,2770,2788,3132,3162,3180,3188,3226,3244,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10448 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10448 2732 4
  · have he : independentCachedBranchMembers10448.erase 2732=independentCachedBranchMembers10446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10446
  · have he : independentCachedBranchMembers10448.filter (independentCachedEdge 2732)=independentCachedBranchMembers10447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10447
def independentCachedBranchMembers10449 : Finset ℕ := ([66,1596,1690,1708,1746,1764,2650,2668,2762,3162,3180,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10449 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10449 4 (fun x => (if x<2650 then (if x<1708 then (if x<1596 then 0 else (if x<1690 then 0 else 1)) else (if x<1746 then 1 else (if x<1764 then 2 else 2))) else (if x<3162 then (if x<2668 then 1 else (if x<2762 then 1 else 0)) else (if x<3180 then 2 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10450 : Finset ℕ := ([36,66,130,252,1596,1644,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,2732,2762,2770,2788,3132,3162,3180,3188,3226,3244,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10450 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10450 1644 4
  · have he : independentCachedBranchMembers10450.erase 1644=independentCachedBranchMembers10448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10448
  · have he : independentCachedBranchMembers10450.filter (independentCachedEdge 1644)=independentCachedBranchMembers10449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10449
def independentCachedBranchMembers10451 : Finset ℕ := ([66,130,252,1596,1716,1738,2620,2676,2762,3132,3188,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10451 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10451 4 (fun x => (if x<2620 then (if x<1596 then (if x<130 then 0 else (if x<252 then 1 else 2)) else (if x<1716 then 0 else (if x<1738 then 2 else 1))) else (if x<3132 then (if x<2676 then 1 else (if x<2762 then 2 else 0)) else (if x<3188 then 2 else (if x<3252 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10452 : Finset ℕ := ([18,36,66,130,252,1596,1644,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,2732,2762,2770,2788,3132,3162,3180,3188,3226,3244,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10452 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10452 18 4
  · have he : independentCachedBranchMembers10452.erase 18=independentCachedBranchMembers10450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10450
  · have he : independentCachedBranchMembers10452.filter (independentCachedEdge 18)=independentCachedBranchMembers10451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10451
def independentCachedBranchMembers10453 : Finset ℕ := ([66,130,1596,1738,1746,1764,2620,2762,2770,2788,3162,3180,3188,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10453 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10453 4 (fun x => (if x<2770 then (if x<1746 then (if x<1596 then (if x<130 then 0 else 1) else (if x<1738 then 0 else 1)) else (if x<2620 then (if x<1764 then 2 else 2) else (if x<2762 then 1 else 0))) else (if x<3188 then (if x<3162 then (if x<2788 then 3 else 3) else (if x<3180 then 2 else 2)) else (if x<3244 then (if x<3226 then 1 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10454 : Finset ℕ := ([18,36,66,130,252,1596,1644,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,2732,2762,2770,2788,3132,3162,3180,3188,3226,3244,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10454 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10454 3300 4
  · have he : independentCachedBranchMembers10454.erase 3300=independentCachedBranchMembers10452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10452
  · have he : independentCachedBranchMembers10454.filter (independentCachedEdge 3300)=independentCachedBranchMembers10453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10453
def independentCachedBranchMembers10455 : Finset ℕ := ([66,252,1596,1690,1708,1716,2650,2668,2676,2762,2770,2788,3132,3226,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10455 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10455 4 (fun x => (if x<2676 then (if x<1708 then (if x<1596 then (if x<252 then 0 else 1) else (if x<1690 then 0 else 2)) else (if x<2650 then (if x<1716 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3132 then (if x<2770 then (if x<2762 then 2 else 0) else (if x<2788 then 3 else 3)) else (if x<3244 then (if x<3226 then 1 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10456 : Finset ℕ := ([18,36,66,130,252,1596,1644,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,2714,2732,2762,2770,2788,3132,3162,3180,3188,3226,3244,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10456 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10456 2714 4
  · have he : independentCachedBranchMembers10456.erase 2714=independentCachedBranchMembers10454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10454
  · have he : independentCachedBranchMembers10456.filter (independentCachedEdge 2714)=independentCachedBranchMembers10455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10455
def independentCachedBranchMembers10457 : Finset ℕ := ([252,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,3132,3162,3180,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10457 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10457 4 (fun x => (if x<2620 then (if x<1716 then (if x<1690 then 0 else (if x<1708 then 1 else 0)) else (if x<1746 then (if x<1738 then 1 else 2) else (if x<1764 then 3 else 2))) else (if x<3132 then (if x<2668 then (if x<2650 then 0 else 1) else (if x<2676 then 3 else 1)) else (if x<3180 then (if x<3162 then 3 else 2) else (if x<3188 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10458 : Finset ℕ := ([252,1708,1716,1764,2650,3162] : List ℕ).toFinset
theorem independentCachedBranchBound10458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10458 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10458 3 (fun x => (if x<1764 then (if x<1708 then 0 else (if x<1716 then 0 else 1)) else (if x<2650 then 2 else (if x<3162 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10459 : Finset ℕ := ([130,252,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,3132,3162,3180,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10459 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10459 130 3
  · have he : independentCachedBranchMembers10459.erase 130=independentCachedBranchMembers10457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10457
  · have he : independentCachedBranchMembers10459.filter (independentCachedEdge 130)=independentCachedBranchMembers10458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10458
def independentCachedBranchMembers10460 : Finset ℕ := ([18,36,66,130,252,1596,1626,1644,1690,1708,1716,1738,1746,1764,2620,2650,2668,2676,2714,2732,2762,2770,2788,3132,3162,3180,3188,3226,3244,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10460 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10460 1626 4
  · have he : independentCachedBranchMembers10460.erase 1626=independentCachedBranchMembers10456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10456
  · have he : independentCachedBranchMembers10460.filter (independentCachedEdge 1626)=independentCachedBranchMembers10459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10459
def independentCachedBranchMembers10461 : Finset ℕ := ([12,18,34,36,66,68,130,132,250,252,1594,1596,1626,1628,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3276,3282,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10461 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10461 34 5
  · have he : independentCachedBranchMembers10461.erase 34=independentCachedBranchMembers10441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10441
  · have he : independentCachedBranchMembers10461.filter (independentCachedEdge 34)=independentCachedBranchMembers10460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10460
def independentCachedBranchMembers10462 : Finset ℕ := ([66,130,250,1596,1626,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2714,2762,2772,2786,3130,3164,3178,3188,3228,3242,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10462 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10462 5 (fun x => (if x<2674 then (if x<1714 then (if x<1596 then (if x<130 then 0 else (if x<250 then 1 else 0)) else (if x<1690 then (if x<1626 then 1 else 0) else (if x<1708 then 1 else 2))) else (if x<1762 then (if x<1738 then 2 else (if x<1748 then 2 else 2)) else (if x<2650 then (if x<2620 then 0 else 3) else (if x<2668 then 3 else 1)))) else (if x<3178 then (if x<2772 then (if x<2714 then 0 else (if x<2762 then 4 else 0)) else (if x<3130 then (if x<2786 then 3 else 4) else (if x<3164 then 3 else 3))) else (if x<3242 then (if x<3188 then 0 else (if x<3228 then 1 else 4)) else (if x<3282 then (if x<3252 then 2 else 2) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10463 : Finset ℕ := ([250,1714,1748,1762,2674,2772,2786,3130,3164,3178,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound10463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10463 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10463 4 (fun x => (if x<2786 then (if x<1762 then (if x<1714 then 0 else (if x<1748 then 0 else 1)) else (if x<2674 then 1 else (if x<2772 then 0 else 2))) else (if x<3178 then (if x<3130 then 2 else (if x<3164 then 0 else 1)) else (if x<3228 then 1 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
