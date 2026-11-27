/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch240
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10496 : Finset ℕ := ([34,68,132,252,1594,1628,1650,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2716,2732,2738,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10496 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10496 1650 4
  · have he : independentCachedBranchMembers10496.erase 1650=independentCachedBranchMembers10492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10492
  · have he : independentCachedBranchMembers10496.filter (independentCachedEdge 1650)=independentCachedBranchMembers10495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10495
def independentCachedBranchMembers10497 : Finset ℕ := ([132,1628,1708,1714,1764,2618,2668,2674,2716,2762,2772,3162,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10497 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10497 4 (fun x => (if x<2674 then (if x<1714 then (if x<1628 then 0 else (if x<1708 then 1 else 0)) else (if x<2618 then (if x<1764 then 2 else 1) else (if x<2668 then 2 else 1))) else (if x<3162 then (if x<2762 then (if x<2716 then 0 else 3) else (if x<2772 then 3 else 1)) else (if x<3252 then (if x<3242 then 0 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10498 : Finset ℕ := ([1708,1764,2668,2762,3162,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10498 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10498 3 (fun x => (if x<2762 then (if x<1764 then 0 else (if x<2668 then 1 else 0)) else (if x<3162 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10499 : Finset ℕ := ([34,132,1628,1708,1714,1764,2618,2668,2674,2716,2762,2772,3162,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10499 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10499 34 3
  · have he : independentCachedBranchMembers10499.erase 34=independentCachedBranchMembers10497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10497
  · have he : independentCachedBranchMembers10499.filter (independentCachedEdge 34)=independentCachedBranchMembers10498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10498
def independentCachedBranchMembers10500 : Finset ℕ := ([34,68,132,252,1594,1628,1644,1650,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2716,2732,2738,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10500 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10500 1644 4
  · have he : independentCachedBranchMembers10500.erase 1644=independentCachedBranchMembers10496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10496
  · have he : independentCachedBranchMembers10500.filter (independentCachedEdge 1644)=independentCachedBranchMembers10499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10499
def independentCachedBranchMembers10501 : Finset ℕ := ([34,252,1628,1692,1738,1748,2652,2716,2762,2772,3132,3178,3188,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10501 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10501 4 (fun x => (if x<2762 then (if x<1738 then (if x<1628 then (if x<252 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<2652 then (if x<1748 then 2 else 2) else (if x<2716 then 1 else 0))) else (if x<3188 then (if x<3132 then (if x<2772 then 3 else 3) else (if x<3178 then 1 else 2)) else (if x<3252 then (if x<3242 then 2 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10502 : Finset ℕ := ([18,34,68,132,252,1594,1628,1644,1650,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2716,2732,2738,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10502 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10502 18 4
  · have he : independentCachedBranchMembers10502.erase 18=independentCachedBranchMembers10500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10500
  · have he : independentCachedBranchMembers10502.filter (independentCachedEdge 18)=independentCachedBranchMembers10501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10501
def independentCachedBranchMembers10503 : Finset ℕ := ([68,132,1594,1738,1748,1764,2618,2762,2772,2788,3162,3178,3188,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10503 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10503 4 (fun x => (if x<2772 then (if x<1748 then (if x<1594 then (if x<132 then 0 else 1) else (if x<1738 then 0 else 2)) else (if x<2618 then (if x<1764 then 1 else 2) else (if x<2762 then 1 else 3))) else (if x<3188 then (if x<3162 then (if x<2788 then 0 else 3) else (if x<3178 then 2 else 1)) else (if x<3242 then (if x<3226 then 2 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10504 : Finset ℕ := ([12,18,34,68,132,252,1594,1628,1644,1650,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2716,2732,2738,2762,2772,2788,3132,3162,3178,3188,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10504 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10504 12 4
  · have he : independentCachedBranchMembers10504.erase 12=independentCachedBranchMembers10502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10502
  · have he : independentCachedBranchMembers10504.filter (independentCachedEdge 12)=independentCachedBranchMembers10503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10503
def independentCachedBranchMembers10505 : Finset ℕ := ([12,18,34,36,66,68,130,132,250,252,1594,1596,1626,1628,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10505 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10505 3274 5
  · have he : independentCachedBranchMembers10505.erase 3274=independentCachedBranchMembers10483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10483
  · have he : independentCachedBranchMembers10505.filter (independentCachedEdge 3274)=independentCachedBranchMembers10504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10504
def independentCachedBranchMembers10506 : Finset ℕ := ([130,250,1594,1628,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10506 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10506 5 (fun x => (if x<2676 then (if x<1716 then (if x<1628 then (if x<250 then 0 else (if x<1594 then 0 else 1)) else (if x<1690 then 1 else (if x<1706 then 0 else 2))) else (if x<1762 then (if x<1740 then 1 else (if x<1746 then 2 else 1)) else (if x<2650 then (if x<2620 then 0 else 1) else (if x<2666 then 1 else 3)))) else (if x<3164 then (if x<2762 then (if x<2716 then 3 else (if x<2738 then 4 else 0)) else (if x<2788 then (if x<2772 then 0 else 1) else (if x<3130 then 4 else 2))) else (if x<3226 then (if x<3180 then 2 else (if x<3186 then 3 else 3)) else (if x<3252 then (if x<3242 then 4 else 0) else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10507 : Finset ℕ := ([250,1716,1746,1762,2620,2650,2666,2716,2762,3186,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10507 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10507 4 (fun x => (if x<2666 then (if x<1762 then (if x<1716 then 0 else (if x<1746 then 1 else 0)) else (if x<2620 then 1 else (if x<2650 then 1 else 0))) else (if x<3186 then (if x<2716 then 1 else (if x<2762 then 2 else 2)) else (if x<3252 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10508 : Finset ℕ := ([68,130,250,1594,1628,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10508 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10508 68 4
  · have he : independentCachedBranchMembers10508.erase 68=independentCachedBranchMembers10506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10506
  · have he : independentCachedBranchMembers10508.filter (independentCachedEdge 68)=independentCachedBranchMembers10507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10507
def independentCachedBranchMembers10509 : Finset ℕ := ([130,1690,1716,1746,2620,2650,2676,2762,2788,3180,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10509 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10509 4 (fun x => (if x<2676 then (if x<1746 then (if x<1690 then 0 else (if x<1716 then 0 else 1)) else (if x<2620 then 1 else (if x<2650 then 1 else 1))) else (if x<3180 then (if x<2762 then 0 else (if x<2788 then 2 else 2)) else (if x<3226 then 0 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10510 : Finset ℕ := ([34,68,130,250,1594,1628,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10510 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10510 34 4
  · have he : independentCachedBranchMembers10510.erase 34=independentCachedBranchMembers10508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10508
  · have he : independentCachedBranchMembers10510.filter (independentCachedEdge 34)=independentCachedBranchMembers10509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10509
def independentCachedBranchMembers10511 : Finset ℕ := ([34,68,1594,1628,1706,1716,1740,1746,2666,2676,2716,2788,3180,3186,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10511 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10511 4 (fun x => (if x<2666 then (if x<1706 then (if x<1594 then (if x<68 then 0 else 0) else (if x<1628 then 0 else 0)) else (if x<1740 then (if x<1716 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3180 then (if x<2716 then (if x<2676 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3186 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10512 : Finset ℕ := ([34,68,130,250,1594,1628,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10512 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10512 3282 4
  · have he : independentCachedBranchMembers10512.erase 3282=independentCachedBranchMembers10510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10510
  · have he : independentCachedBranchMembers10512.filter (independentCachedEdge 3282)=independentCachedBranchMembers10511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10511
def independentCachedBranchMembers10513 : Finset ℕ := ([130,250,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,3130,3164,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10513 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10513 4 (fun x => (if x<2620 then (if x<1716 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3130 then (if x<2666 then (if x<2650 then 2 else 2) else (if x<2676 then 3 else 3)) else (if x<3180 then (if x<3164 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10514 : Finset ℕ := ([34,68,130,250,1594,1628,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10514 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10514 3276 4
  · have he : independentCachedBranchMembers10514.erase 3276=independentCachedBranchMembers10512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10512
  · have he : independentCachedBranchMembers10514.filter (independentCachedEdge 3276)=independentCachedBranchMembers10513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10513
def independentCachedBranchMembers10515 : Finset ℕ := ([34,68,130,250,1594,1628,1690,1762,2620,2650,2716,2788,3130,3164,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10515 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10515 4 (fun x => (if x<2620 then (if x<1594 then (if x<130 then (if x<68 then 0 else 0) else (if x<250 then 1 else 1)) else (if x<1690 then (if x<1628 then 0 else 0) else (if x<1762 then 1 else 1))) else (if x<3130 then (if x<2716 then (if x<2650 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3164 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10516 : Finset ℕ := ([34,68,130,250,1594,1628,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2732,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10516 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10516 2732 4
  · have he : independentCachedBranchMembers10516.erase 2732=independentCachedBranchMembers10514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10514
  · have he : independentCachedBranchMembers10516.filter (independentCachedEdge 2732)=independentCachedBranchMembers10515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10515
def independentCachedBranchMembers10517 : Finset ℕ := ([68,130,1594,1740,1746,1762,2620,2762,2772,2788,3164,3180,3186,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10517 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10517 4 (fun x => (if x<2772 then (if x<1746 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1740 then 1 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2762 then 1 else 2))) else (if x<3186 then (if x<3164 then (if x<2788 then 1 else 2) else (if x<3180 then 0 else 3)) else (if x<3242 then (if x<3226 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10518 : Finset ℕ := ([34,68,130,250,1594,1628,1650,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2732,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10518 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10518 1650 4
  · have he : independentCachedBranchMembers10518.erase 1650=independentCachedBranchMembers10516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10516
  · have he : independentCachedBranchMembers10518.filter (independentCachedEdge 1650)=independentCachedBranchMembers10517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10517
def independentCachedBranchMembers10519 : Finset ℕ := ([34,250,1628,1690,1740,1746,2650,2716,2762,2772,3130,3180,3186,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10519 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10519 4 (fun x => (if x<2762 then (if x<1740 then (if x<1628 then (if x<250 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1746 then 2 else 2) else (if x<2716 then 1 else 1))) else (if x<3186 then (if x<3130 then (if x<2772 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10520 : Finset ℕ := ([34,68,130,250,1594,1628,1644,1650,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2732,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10520 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10520 1644 4
  · have he : independentCachedBranchMembers10520.erase 1644=independentCachedBranchMembers10518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10518
  · have he : independentCachedBranchMembers10520.filter (independentCachedEdge 1644)=independentCachedBranchMembers10519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10519
def independentCachedBranchMembers10521 : Finset ℕ := ([34,130,1628,1706,1716,1762,2620,2666,2676,2716,2762,2772,3164,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10521 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10521 4 (fun x => (if x<2676 then (if x<1716 then (if x<1628 then (if x<130 then 0 else 1) else (if x<1706 then 0 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2666 then 2 else 2))) else (if x<3164 then (if x<2762 then (if x<2716 then 1 else 0) else (if x<2772 then 3 else 3)) else (if x<3252 then (if x<3242 then 1 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10522 : Finset ℕ := ([18,34,68,130,250,1594,1628,1644,1650,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2732,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10522 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10522 18 4
  · have he : independentCachedBranchMembers10522.erase 18=independentCachedBranchMembers10520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10520
  · have he : independentCachedBranchMembers10522.filter (independentCachedEdge 18)=independentCachedBranchMembers10521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10521
def independentCachedBranchMembers10523 : Finset ℕ := ([68,250,1594,1690,1706,1716,2650,2666,2676,2762,2772,2788,3130,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10523 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10523 4 (fun x => (if x<2676 then (if x<1706 then (if x<1594 then (if x<250 then 0 else 1) else (if x<1690 then 0 else 1)) else (if x<2650 then (if x<1716 then 2 else 2) else (if x<2666 then 1 else 2))) else (if x<3130 then (if x<2772 then (if x<2762 then 2 else 3) else (if x<2788 then 0 else 3)) else (if x<3242 then (if x<3226 then 1 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10524 : Finset ℕ := ([12,18,34,68,130,250,1594,1628,1644,1650,1690,1706,1716,1740,1746,1762,2620,2650,2666,2676,2716,2732,2738,2762,2772,2788,3130,3164,3180,3186,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10524 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10524 12 4
  · have he : independentCachedBranchMembers10524.erase 12=independentCachedBranchMembers10522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10522
  · have he : independentCachedBranchMembers10524.filter (independentCachedEdge 12)=independentCachedBranchMembers10523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10523
def independentCachedBranchMembers10525 : Finset ℕ := ([12,18,34,36,66,68,130,132,250,252,1594,1596,1626,1628,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2732,2738,2740,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10525 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10525 2740 5
  · have he : independentCachedBranchMembers10525.erase 2740=independentCachedBranchMembers10505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10505
  · have he : independentCachedBranchMembers10525.filter (independentCachedEdge 2740)=independentCachedBranchMembers10524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10524
def independentCachedBranchMembers10526 : Finset ℕ := ([132,252,1596,1626,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10526 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10526 5 (fun x => (if x<2676 then (if x<1716 then (if x<1626 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1706 then 0 else 1))) else (if x<1764 then (if x<1740 then 2 else (if x<1746 then 1 else 2)) else (if x<2652 then (if x<2618 then 0 else 1) else (if x<2666 then 1 else 3)))) else (if x<3162 then (if x<2762 then (if x<2714 then 3 else (if x<2732 then 4 else 0)) else (if x<2786 then (if x<2772 then 1 else 0) else (if x<3132 then 4 else 2))) else (if x<3228 then (if x<3180 then 2 else (if x<3186 then 3 else 3)) else (if x<3252 then (if x<3242 then 4 else 3) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10527 : Finset ℕ := ([252,1706,1740,1764,2618,2652,2676,2714,2772,3180,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10527 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10527 4 (fun x => (if x<2676 then (if x<1764 then (if x<1706 then 0 else (if x<1740 then 1 else 0)) else (if x<2618 then 1 else (if x<2652 then 1 else 0))) else (if x<3180 then (if x<2714 then 1 else (if x<2772 then 2 else 2)) else (if x<3242 then 0 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
