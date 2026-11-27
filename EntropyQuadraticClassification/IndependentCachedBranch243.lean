/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch242
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10560 : Finset ℕ := ([34,66,132,250,1596,1628,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2738,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10560 2738 4
  · have he : independentCachedBranchMembers10560.erase 2738=independentCachedBranchMembers10558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10558
  · have he : independentCachedBranchMembers10560.filter (independentCachedEdge 2738)=independentCachedBranchMembers10559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10559
def independentCachedBranchMembers10561 : Finset ℕ := ([34,250,1628,1690,1738,1748,2650,2716,2764,2770,3130,3178,3188,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10561 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10561 4 (fun x => (if x<2764 then (if x<1738 then (if x<1628 then (if x<250 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1748 then 2 else 2) else (if x<2716 then 1 else 1))) else (if x<3188 then (if x<3130 then (if x<2770 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3250 then (if x<3244 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10562 : Finset ℕ := ([34,66,132,250,1596,1628,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2732,2738,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10562 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10562 2732 4
  · have he : independentCachedBranchMembers10562.erase 2732=independentCachedBranchMembers10560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10560
  · have he : independentCachedBranchMembers10562.filter (independentCachedEdge 2732)=independentCachedBranchMembers10561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10561
def independentCachedBranchMembers10563 : Finset ℕ := ([34,66,132,250,1596,1628,1690,1764,2618,2650,2716,2786,3130,3162,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10563 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10563 4 (fun x => (if x<2618 then (if x<1596 then (if x<132 then (if x<66 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1690 then (if x<1628 then 2 else 3) else (if x<1764 then 2 else 3))) else (if x<3130 then (if x<2716 then (if x<2650 then 0 else 1) else (if x<2786 then 0 else 1)) else (if x<3228 then (if x<3162 then 2 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10564 : Finset ℕ := ([34,66,132,250,1596,1628,1644,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2732,2738,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10564 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10564 1644 4
  · have he : independentCachedBranchMembers10564.erase 1644=independentCachedBranchMembers10562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10562
  · have he : independentCachedBranchMembers10564.filter (independentCachedEdge 1644)=independentCachedBranchMembers10563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10563
def independentCachedBranchMembers10565 : Finset ℕ := ([34,66,1596,1628,1706,1716,1738,1748,2666,2676,2716,2786,3178,3188,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10565 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10565 4 (fun x => (if x<2666 then (if x<1706 then (if x<1596 then (if x<66 then 0 else 1) else (if x<1628 then 1 else 0)) else (if x<1738 then (if x<1716 then 2 else 2) else (if x<1748 then 3 else 3))) else (if x<3178 then (if x<2716 then (if x<2676 then 2 else 2) else (if x<2786 then 0 else 1)) else (if x<3228 then (if x<3188 then 3 else 3) else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10566 : Finset ℕ := ([18,34,66,132,250,1596,1628,1644,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2732,2738,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10566 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10566 18 4
  · have he : independentCachedBranchMembers10566.erase 18=independentCachedBranchMembers10564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10564
  · have he : independentCachedBranchMembers10566.filter (independentCachedEdge 18)=independentCachedBranchMembers10565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10565
def independentCachedBranchMembers10567 : Finset ℕ := ([250,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,3130,3162,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10567 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10567 4 (fun x => (if x<2618 then (if x<1716 then (if x<1690 then 0 else (if x<1706 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 2) else (if x<1764 then 2 else 3))) else (if x<3130 then (if x<2666 then (if x<2650 then 0 else 3) else (if x<2676 then 1 else 1)) else (if x<3178 then (if x<3162 then 3 else 0) else (if x<3188 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10568 : Finset ℕ := ([250,1690,1706,1738,2676,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10568 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10568 3 (fun x => (if x<1738 then (if x<1690 then 0 else (if x<1706 then 0 else 1)) else (if x<2676 then 2 else (if x<3188 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10569 : Finset ℕ := ([132,250,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,3130,3162,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10569 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10569 132 3
  · have he : independentCachedBranchMembers10569.erase 132=independentCachedBranchMembers10567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10567
  · have he : independentCachedBranchMembers10569.filter (independentCachedEdge 132)=independentCachedBranchMembers10568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10568
def independentCachedBranchMembers10570 : Finset ℕ := ([12,18,34,66,132,250,1596,1628,1644,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2732,2738,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10570 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10570 12 4
  · have he : independentCachedBranchMembers10570.erase 12=independentCachedBranchMembers10566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10566
  · have he : independentCachedBranchMembers10570.filter (independentCachedEdge 12)=independentCachedBranchMembers10569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10569
def independentCachedBranchMembers10571 : Finset ℕ := ([12,18,34,36,66,68,130,132,250,252,1594,1596,1626,1628,1644,1650,1652,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10571 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10571 1652 5
  · have he : independentCachedBranchMembers10571.erase 1652=independentCachedBranchMembers10545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10545
  · have he : independentCachedBranchMembers10571.filter (independentCachedEdge 1652)=independentCachedBranchMembers10570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10570
def independentCachedBranchMembers10572 : Finset ℕ := ([68,252,1594,1626,1644,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10572 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10572 5 (fun x => (if x<2666 then (if x<1706 then (if x<1626 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 2 else (if x<1692 then 0 else 1))) else (if x<1748 then (if x<1716 then 2 else (if x<1738 then 3 else 1)) else (if x<2620 then (if x<1762 then 0 else 3) else (if x<2652 then 1 else 0)))) else (if x<3164 then (if x<2764 then (if x<2676 then 1 else (if x<2714 then 4 else 1)) else (if x<2788 then (if x<2770 then 1 else 4) else (if x<3132 then 0 else 3))) else (if x<3226 then (if x<3178 then 2 else (if x<3188 then 2 else 0)) else (if x<3250 then (if x<3244 then 2 else 2) else (if x<3300 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10573 : Finset ℕ := ([252,1594,1626,1692,1716,1748,2666,2764,2788,3178,3244,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10573 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10573 4 (fun x => (if x<2666 then (if x<1692 then (if x<1594 then 0 else (if x<1626 then 1 else 2)) else (if x<1716 then 0 else (if x<1748 then 1 else 2))) else (if x<3178 then (if x<2764 then 1 else (if x<2788 then 0 else 1)) else (if x<3244 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10574 : Finset ℕ := ([68,130,252,1594,1626,1644,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10574 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10574 130 4
  · have he : independentCachedBranchMembers10574.erase 130=independentCachedBranchMembers10572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10572
  · have he : independentCachedBranchMembers10574.filter (independentCachedEdge 130)=independentCachedBranchMembers10573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10573
def independentCachedBranchMembers10575 : Finset ℕ := ([68,1594,1692,1706,1748,1762,2652,2666,2764,3164,3178,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10575 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10575 4 (fun x => (if x<2652 then (if x<1706 then (if x<1594 then 0 else (if x<1692 then 0 else 1)) else (if x<1748 then 1 else (if x<1762 then 2 else 2))) else (if x<3164 then (if x<2666 then 1 else (if x<2764 then 1 else 0)) else (if x<3178 then 2 else (if x<3250 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10576 : Finset ℕ := ([36,68,130,252,1594,1626,1644,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10576 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10576 36 4
  · have he : independentCachedBranchMembers10576.erase 36=independentCachedBranchMembers10574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10574
  · have he : independentCachedBranchMembers10576.filter (independentCachedEdge 36)=independentCachedBranchMembers10575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10575
def independentCachedBranchMembers10577 : Finset ℕ := ([252,1594,1692,1706,1716,2652,2666,2676,2764,2770,2788,3132,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10577 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10577 4 (fun x => (if x<2676 then (if x<1706 then (if x<1594 then 0 else (if x<1692 then 1 else 0)) else (if x<2652 then (if x<1716 then 2 else 1) else (if x<2666 then 0 else 1))) else (if x<3132 then (if x<2770 then (if x<2764 then 2 else 3) else (if x<2788 then 3 else 1)) else (if x<3244 then (if x<3226 then 0 else 2) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10578 : Finset ℕ := ([1692,1716,2666,2770,3132,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10578 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10578 3 (fun x => (if x<2770 then (if x<1716 then 0 else (if x<2666 then 1 else 0)) else (if x<3132 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10579 : Finset ℕ := ([68,252,1594,1692,1706,1716,2652,2666,2676,2764,2770,2788,3132,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10579 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10579 68 3
  · have he : independentCachedBranchMembers10579.erase 68=independentCachedBranchMembers10577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10577
  · have he : independentCachedBranchMembers10579.filter (independentCachedEdge 68)=independentCachedBranchMembers10578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10578
def independentCachedBranchMembers10580 : Finset ℕ := ([36,68,130,252,1594,1626,1644,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10580 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10580 3282 4
  · have he : independentCachedBranchMembers10580.erase 3282=independentCachedBranchMembers10576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10576
  · have he : independentCachedBranchMembers10580.filter (independentCachedEdge 3282)=independentCachedBranchMembers10579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10579
def independentCachedBranchMembers10581 : Finset ℕ := ([130,1626,1706,1716,1762,2620,2666,2676,2714,2764,2770,3164,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10581 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10581 4 (fun x => (if x<2676 then (if x<1716 then (if x<1626 then 0 else (if x<1706 then 1 else 0)) else (if x<2620 then (if x<1762 then 2 else 1) else (if x<2666 then 2 else 1))) else (if x<3164 then (if x<2764 then (if x<2714 then 0 else 3) else (if x<2770 then 3 else 1)) else (if x<3250 then (if x<3244 then 0 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10582 : Finset ℕ := ([1706,1762,2666,2764,3164,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10582 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10582 3 (fun x => (if x<2764 then (if x<1762 then 0 else (if x<2666 then 1 else 0)) else (if x<3164 then 2 else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10583 : Finset ℕ := ([36,130,1626,1706,1716,1762,2620,2666,2676,2714,2764,2770,3164,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10583 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10583 36 3
  · have he : independentCachedBranchMembers10583.erase 36=independentCachedBranchMembers10581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10581
  · have he : independentCachedBranchMembers10583.filter (independentCachedEdge 36)=independentCachedBranchMembers10582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10582
def independentCachedBranchMembers10584 : Finset ℕ := ([36,68,130,252,1594,1626,1644,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10584 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10584 3276 4
  · have he : independentCachedBranchMembers10584.erase 3276=independentCachedBranchMembers10580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10580
  · have he : independentCachedBranchMembers10584.filter (independentCachedEdge 3276)=independentCachedBranchMembers10583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10583
def independentCachedBranchMembers10585 : Finset ℕ := ([36,252,1626,1692,1738,1748,2652,2714,2764,2770,3132,3178,3188,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10585 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10585 4 (fun x => (if x<2764 then (if x<1738 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1748 then 2 else 2) else (if x<2714 then 1 else 1))) else (if x<3188 then (if x<3132 then (if x<2770 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3250 then (if x<3244 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10586 : Finset ℕ := ([36,68,130,252,1594,1626,1644,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2738,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10586 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10586 2738 4
  · have he : independentCachedBranchMembers10586.erase 2738=independentCachedBranchMembers10584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10584
  · have he : independentCachedBranchMembers10586.filter (independentCachedEdge 2738)=independentCachedBranchMembers10585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10585
def independentCachedBranchMembers10587 : Finset ℕ := ([68,130,1594,1738,1748,1762,2620,2764,2770,2788,3164,3178,3188,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10587 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10587 4 (fun x => (if x<2770 then (if x<1748 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1738 then 1 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2764 then 1 else 1))) else (if x<3188 then (if x<3164 then (if x<2788 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3244 then (if x<3226 then 3 else 0) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10588 : Finset ℕ := ([36,68,130,252,1594,1626,1644,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2732,2738,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10588 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10588 2732 4
  · have he : independentCachedBranchMembers10588.erase 2732=independentCachedBranchMembers10586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10586
  · have he : independentCachedBranchMembers10588.filter (independentCachedEdge 2732)=independentCachedBranchMembers10587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10587
def independentCachedBranchMembers10589 : Finset ℕ := ([36,68,130,252,1594,1626,1692,1762,2620,2652,2714,2788,3132,3164,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10589 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10589 4 (fun x => (if x<2620 then (if x<1594 then (if x<130 then (if x<68 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1692 then (if x<1626 then 2 else 3) else (if x<1762 then 2 else 3))) else (if x<3132 then (if x<2714 then (if x<2652 then 0 else 1) else (if x<2788 then 0 else 1)) else (if x<3226 then (if x<3164 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10590 : Finset ℕ := ([36,68,130,252,1594,1626,1644,1650,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2732,2738,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10590 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10590 1650 4
  · have he : independentCachedBranchMembers10590.erase 1650=independentCachedBranchMembers10588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10588
  · have he : independentCachedBranchMembers10590.filter (independentCachedEdge 1650)=independentCachedBranchMembers10589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10589
def independentCachedBranchMembers10591 : Finset ℕ := ([252,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,3132,3164,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10591 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10591 4 (fun x => (if x<2620 then (if x<1716 then (if x<1692 then 0 else (if x<1706 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 2) else (if x<1762 then 2 else 3))) else (if x<3132 then (if x<2666 then (if x<2652 then 0 else 3) else (if x<2676 then 1 else 1)) else (if x<3178 then (if x<3164 then 3 else 0) else (if x<3188 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
