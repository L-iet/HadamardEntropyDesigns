/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch239
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10464 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2714,2762,2772,2786,3130,3164,3178,3188,3228,3242,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10464 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10464 36 4
  · have he : independentCachedBranchMembers10464.erase 36=independentCachedBranchMembers10462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10462
  · have he : independentCachedBranchMembers10464.filter (independentCachedEdge 36)=independentCachedBranchMembers10463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10463
def independentCachedBranchMembers10465 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1762,2620,2650,2714,2786,3130,3164,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10465 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10465 4 (fun x => (if x<2620 then (if x<1596 then (if x<130 then (if x<66 then 0 else 0) else (if x<250 then 1 else 1)) else (if x<1690 then (if x<1626 then 0 else 0) else (if x<1762 then 1 else 1))) else (if x<3130 then (if x<2714 then (if x<2650 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3164 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10466 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2714,2762,2772,2786,3130,3164,3178,3188,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10466 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10466 3276 4
  · have he : independentCachedBranchMembers10466.erase 3276=independentCachedBranchMembers10464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10464
  · have he : independentCachedBranchMembers10466.filter (independentCachedEdge 3276)=independentCachedBranchMembers10465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10465
def independentCachedBranchMembers10467 : Finset ℕ := ([36,66,1596,1626,1708,1714,1738,1748,2668,2674,2714,2786,3178,3188,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10467 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10467 4 (fun x => (if x<2668 then (if x<1708 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1626 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2714 then (if x<2674 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3188 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10468 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2714,2738,2762,2772,2786,3130,3164,3178,3188,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10468 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10468 2738 4
  · have he : independentCachedBranchMembers10468.erase 2738=independentCachedBranchMembers10466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10466
  · have he : independentCachedBranchMembers10468.filter (independentCachedEdge 2738)=independentCachedBranchMembers10467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10467
def independentCachedBranchMembers10469 : Finset ℕ := ([130,250,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,3130,3164,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10469 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10469 4 (fun x => (if x<2620 then (if x<1714 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3130 then (if x<2668 then (if x<2650 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3178 then (if x<3164 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10470 : Finset ℕ := ([36,66,130,250,1596,1626,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2714,2732,2738,2762,2772,2786,3130,3164,3178,3188,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10470 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10470 2732 4
  · have he : independentCachedBranchMembers10470.erase 2732=independentCachedBranchMembers10468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10468
  · have he : independentCachedBranchMembers10470.filter (independentCachedEdge 2732)=independentCachedBranchMembers10469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10469
def independentCachedBranchMembers10471 : Finset ℕ := ([130,1626,1708,1714,1762,2620,2668,2674,2714,2762,2772,3164,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10471 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10471 4 (fun x => (if x<2674 then (if x<1714 then (if x<1626 then 0 else (if x<1708 then 1 else 2)) else (if x<2620 then (if x<1762 then 0 else 1) else (if x<2668 then 2 else 0))) else (if x<3164 then (if x<2762 then (if x<2714 then 1 else 3) else (if x<2772 then 1 else 3)) else (if x<3252 then (if x<3242 then 0 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10472 : Finset ℕ := ([1714,1762,2674,2772,3164,3242] : List ℕ).toFinset
theorem independentCachedBranchBound10472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10472 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10472 3 (fun x => (if x<2772 then (if x<1762 then 0 else (if x<2674 then 1 else 0)) else (if x<3164 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10473 : Finset ℕ := ([36,130,1626,1708,1714,1762,2620,2668,2674,2714,2762,2772,3164,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10473 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10473 36 3
  · have he : independentCachedBranchMembers10473.erase 36=independentCachedBranchMembers10471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10471
  · have he : independentCachedBranchMembers10473.filter (independentCachedEdge 36)=independentCachedBranchMembers10472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10472
def independentCachedBranchMembers10474 : Finset ℕ := ([36,66,130,250,1596,1626,1650,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2714,2732,2738,2762,2772,2786,3130,3164,3178,3188,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10474 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10474 1650 4
  · have he : independentCachedBranchMembers10474.erase 1650=independentCachedBranchMembers10470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10470
  · have he : independentCachedBranchMembers10474.filter (independentCachedEdge 1650)=independentCachedBranchMembers10473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10473
def independentCachedBranchMembers10475 : Finset ℕ := ([250,1596,1690,1708,1714,2650,2668,2674,2762,2772,2786,3130,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10475 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10475 4 (fun x => (if x<2674 then (if x<1708 then (if x<1596 then 0 else (if x<1690 then 1 else 0)) else (if x<2650 then (if x<1714 then 2 else 1) else (if x<2668 then 0 else 1))) else (if x<3130 then (if x<2772 then (if x<2762 then 2 else 3) else (if x<2786 then 3 else 1)) else (if x<3242 then (if x<3228 then 0 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10476 : Finset ℕ := ([1690,1714,2668,2772,3130,3242] : List ℕ).toFinset
theorem independentCachedBranchBound10476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10476 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10476 3 (fun x => (if x<2772 then (if x<1714 then 0 else (if x<2668 then 1 else 0)) else (if x<3130 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10477 : Finset ℕ := ([66,250,1596,1690,1708,1714,2650,2668,2674,2762,2772,2786,3130,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10477 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10477 66 3
  · have he : independentCachedBranchMembers10477.erase 66=independentCachedBranchMembers10475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10475
  · have he : independentCachedBranchMembers10477.filter (independentCachedEdge 66)=independentCachedBranchMembers10476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10476
def independentCachedBranchMembers10478 : Finset ℕ := ([36,66,130,250,1596,1626,1644,1650,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2714,2732,2738,2762,2772,2786,3130,3164,3178,3188,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10478 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10478 1644 4
  · have he : independentCachedBranchMembers10478.erase 1644=independentCachedBranchMembers10474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10474
  · have he : independentCachedBranchMembers10478.filter (independentCachedEdge 1644)=independentCachedBranchMembers10477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10477
def independentCachedBranchMembers10479 : Finset ℕ := ([66,130,1596,1738,1748,1762,2620,2762,2772,2786,3164,3178,3188,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10479 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10479 4 (fun x => (if x<2772 then (if x<1748 then (if x<1596 then (if x<130 then 0 else 1) else (if x<1738 then 0 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2762 then 1 else 0))) else (if x<3188 then (if x<3164 then (if x<2786 then 3 else 3) else (if x<3178 then 2 else 2)) else (if x<3242 then (if x<3228 then 1 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10480 : Finset ℕ := ([18,36,66,130,250,1596,1626,1644,1650,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2714,2732,2738,2762,2772,2786,3130,3164,3178,3188,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10480 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10480 18 4
  · have he : independentCachedBranchMembers10480.erase 18=independentCachedBranchMembers10478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10478
  · have he : independentCachedBranchMembers10480.filter (independentCachedEdge 18)=independentCachedBranchMembers10479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10479
def independentCachedBranchMembers10481 : Finset ℕ := ([36,250,1626,1690,1738,1748,2650,2714,2762,2772,3130,3178,3188,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10481 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10481 4 (fun x => (if x<2762 then (if x<1738 then (if x<1626 then (if x<250 then 0 else 1) else (if x<1690 then 0 else 1)) else (if x<2650 then (if x<1748 then 2 else 2) else (if x<2714 then 1 else 0))) else (if x<3188 then (if x<3130 then (if x<2772 then 3 else 3) else (if x<3178 then 1 else 2)) else (if x<3252 then (if x<3242 then 2 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10482 : Finset ℕ := ([12,18,36,66,130,250,1596,1626,1644,1650,1690,1708,1714,1738,1748,1762,2620,2650,2668,2674,2714,2732,2738,2762,2772,2786,3130,3164,3178,3188,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10482 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10482 12 4
  · have he : independentCachedBranchMembers10482.erase 12=independentCachedBranchMembers10480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10480
  · have he : independentCachedBranchMembers10482.filter (independentCachedEdge 12)=independentCachedBranchMembers10481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10481
def independentCachedBranchMembers10483 : Finset ℕ := ([12,18,34,36,66,68,130,132,250,252,1594,1596,1626,1628,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10483 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10483 3284 5
  · have he : independentCachedBranchMembers10483.erase 3284=independentCachedBranchMembers10461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10461
  · have he : independentCachedBranchMembers10483.filter (independentCachedEdge 3284)=independentCachedBranchMembers10482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10482
def independentCachedBranchMembers10484 : Finset ℕ := ([68,132,252,1594,1628,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2716,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10484 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10484 5 (fun x => (if x<2674 then (if x<1714 then (if x<1594 then (if x<132 then 0 else (if x<252 then 1 else 0)) else (if x<1692 then (if x<1628 then 1 else 0) else (if x<1708 then 1 else 2))) else (if x<1764 then (if x<1738 then 2 else (if x<1748 then 2 else 2)) else (if x<2652 then (if x<2618 then 0 else 3) else (if x<2668 then 3 else 0)))) else (if x<3178 then (if x<2772 then (if x<2716 then 1 else (if x<2762 then 4 else 3)) else (if x<3132 then (if x<2788 then 0 else 4) else (if x<3162 then 3 else 3))) else (if x<3242 then (if x<3188 then 1 else (if x<3226 then 0 else 4)) else (if x<3276 then (if x<3252 then 2 else 2) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10485 : Finset ℕ := ([252,1708,1738,1764,2668,2762,2788,3132,3162,3188,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10485 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10485 4 (fun x => (if x<2788 then (if x<1764 then (if x<1708 then 0 else (if x<1738 then 0 else 1)) else (if x<2668 then 1 else (if x<2762 then 0 else 2))) else (if x<3188 then (if x<3132 then 2 else (if x<3162 then 0 else 1)) else (if x<3226 then 1 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10486 : Finset ℕ := ([34,68,132,252,1594,1628,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2716,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10486 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10486 34 4
  · have he : independentCachedBranchMembers10486.erase 34=independentCachedBranchMembers10484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10484
  · have he : independentCachedBranchMembers10486.filter (independentCachedEdge 34)=independentCachedBranchMembers10485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10485
def independentCachedBranchMembers10487 : Finset ℕ := ([34,68,132,252,1594,1628,1692,1764,2618,2652,2716,2788,3132,3162,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10487 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10487 4 (fun x => (if x<2618 then (if x<1594 then (if x<132 then (if x<68 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1692 then (if x<1628 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2652 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3162 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10488 : Finset ℕ := ([34,68,132,252,1594,1628,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2716,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10488 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10488 3282 4
  · have he : independentCachedBranchMembers10488.erase 3282=independentCachedBranchMembers10486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10486
  · have he : independentCachedBranchMembers10488.filter (independentCachedEdge 3282)=independentCachedBranchMembers10487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10487
def independentCachedBranchMembers10489 : Finset ℕ := ([132,252,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,3132,3162,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10489 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10489 4 (fun x => (if x<2618 then (if x<1714 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3132 then (if x<2668 then (if x<2652 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3178 then (if x<3162 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10490 : Finset ℕ := ([34,68,132,252,1594,1628,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2716,2738,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10490 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10490 2738 4
  · have he : independentCachedBranchMembers10490.erase 2738=independentCachedBranchMembers10488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10488
  · have he : independentCachedBranchMembers10490.filter (independentCachedEdge 2738)=independentCachedBranchMembers10489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10489
def independentCachedBranchMembers10491 : Finset ℕ := ([34,68,1594,1628,1708,1714,1738,1748,2668,2674,2716,2788,3178,3188,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10491 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10491 4 (fun x => (if x<2668 then (if x<1708 then (if x<1594 then (if x<68 then 0 else 0) else (if x<1628 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2716 then (if x<2674 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3188 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10492 : Finset ℕ := ([34,68,132,252,1594,1628,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2716,2732,2738,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10492 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10492 2732 4
  · have he : independentCachedBranchMembers10492.erase 2732=independentCachedBranchMembers10490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10490
  · have he : independentCachedBranchMembers10492.filter (independentCachedEdge 2732)=independentCachedBranchMembers10491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10491
def independentCachedBranchMembers10493 : Finset ℕ := ([252,1594,1692,1708,1714,2652,2668,2674,2762,2772,2788,3132,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10493 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10493 4 (fun x => (if x<2674 then (if x<1708 then (if x<1594 then 0 else (if x<1692 then 1 else 0)) else (if x<2652 then (if x<1714 then 1 else 2) else (if x<2668 then 0 else 2))) else (if x<3132 then (if x<2772 then (if x<2762 then 1 else 3) else (if x<2788 then 3 else 1)) else (if x<3242 then (if x<3226 then 0 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10494 : Finset ℕ := ([1692,1708,2674,2762,3132,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10494 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10494 3 (fun x => (if x<2762 then (if x<1708 then 0 else (if x<2674 then 1 else 0)) else (if x<3132 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10495 : Finset ℕ := ([68,252,1594,1692,1708,1714,2652,2668,2674,2762,2772,2788,3132,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10495 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10495 68 3
  · have he : independentCachedBranchMembers10495.erase 68=independentCachedBranchMembers10493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10493
  · have he : independentCachedBranchMembers10495.filter (independentCachedEdge 68)=independentCachedBranchMembers10494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10494
end EntropyDesigns.QuadraticRefinement
