/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch243
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10592 : Finset ℕ := ([252,1692,1716,1748,2666,3178] : List ℕ).toFinset
theorem independentCachedBranchBound10592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10592 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10592 3 (fun x => (if x<1748 then (if x<1692 then 0 else (if x<1716 then 0 else 1)) else (if x<2666 then 2 else (if x<3178 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10593 : Finset ℕ := ([130,252,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,3132,3164,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10593 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10593 130 3
  · have he : independentCachedBranchMembers10593.erase 130=independentCachedBranchMembers10591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10591
  · have he : independentCachedBranchMembers10593.filter (independentCachedEdge 130)=independentCachedBranchMembers10592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10592
def independentCachedBranchMembers10594 : Finset ℕ := ([18,36,68,130,252,1594,1626,1644,1650,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2732,2738,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10594 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10594 18 4
  · have he : independentCachedBranchMembers10594.erase 18=independentCachedBranchMembers10590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10590
  · have he : independentCachedBranchMembers10594.filter (independentCachedEdge 18)=independentCachedBranchMembers10593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10593
def independentCachedBranchMembers10595 : Finset ℕ := ([36,68,1594,1626,1706,1716,1738,1748,2666,2676,2714,2788,3178,3188,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10595 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10595 4 (fun x => (if x<2666 then (if x<1706 then (if x<1594 then (if x<68 then 0 else 1) else (if x<1626 then 1 else 0)) else (if x<1738 then (if x<1716 then 2 else 2) else (if x<1748 then 3 else 3))) else (if x<3178 then (if x<2714 then (if x<2676 then 2 else 2) else (if x<2788 then 0 else 1)) else (if x<3226 then (if x<3188 then 3 else 3) else (if x<3300 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10596 : Finset ℕ := ([12,18,36,68,130,252,1594,1626,1644,1650,1692,1706,1716,1738,1748,1762,2620,2652,2666,2676,2714,2732,2738,2764,2770,2788,3132,3164,3178,3188,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10596 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10596 12 4
  · have he : independentCachedBranchMembers10596.erase 12=independentCachedBranchMembers10594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10594
  · have he : independentCachedBranchMembers10596.filter (independentCachedEdge 12)=independentCachedBranchMembers10595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10595
def independentCachedBranchMembers10597 : Finset ℕ := ([12,18,34,36,66,68,130,132,250,252,1594,1596,1626,1628,1642,1644,1650,1652,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10597 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10597 1642 5
  · have he : independentCachedBranchMembers10597.erase 1642=independentCachedBranchMembers10571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10571
  · have he : independentCachedBranchMembers10597.filter (independentCachedEdge 1642)=independentCachedBranchMembers10596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10596
def independentCachedBranchMembers10598 : Finset ℕ := ([18,132,250,1594,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10598 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10598 5 (fun x => (if x<2668 then (if x<1714 then (if x<1594 then (if x<132 then 0 else (if x<250 then 0 else 1)) else (if x<1690 then 0 else (if x<1708 then 1 else 0))) else (if x<1764 then (if x<1740 then 2 else (if x<1746 then 3 else 3)) else (if x<2618 then 2 else (if x<2650 then 1 else 0)))) else (if x<3162 then (if x<2770 then (if x<2674 then 2 else (if x<2764 then 3 else 0)) else (if x<2788 then 1 else (if x<3130 then 4 else 4))) else (if x<3226 then (if x<3180 then 1 else (if x<3186 then 4 else 0)) else (if x<3244 then 2 else (if x<3250 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10599 : Finset ℕ := ([132,250,1708,1746,2650,2674,2770,3162,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10599 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10599 4 (fun x => (if x<2674 then (if x<1708 then (if x<250 then 0 else 1) else (if x<1746 then 0 else (if x<2650 then 1 else 0))) else (if x<3162 then (if x<2770 then 1 else 2) else (if x<3186 then 1 else (if x<3244 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10600 : Finset ℕ := ([18,68,132,250,1594,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10600 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10600 68 4
  · have he : independentCachedBranchMembers10600.erase 68=independentCachedBranchMembers10598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10598
  · have he : independentCachedBranchMembers10600.filter (independentCachedEdge 68)=independentCachedBranchMembers10599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10599
def independentCachedBranchMembers10601 : Finset ℕ := ([250,1714,1746,1764,2674,2770,2788,3130,3162,3180,3226,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10601 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10601 4 (fun x => (if x<2788 then (if x<1764 then (if x<1714 then 0 else (if x<1746 then 0 else 1)) else (if x<2674 then 1 else (if x<2770 then 0 else 2))) else (if x<3180 then (if x<3130 then 2 else (if x<3162 then 0 else 1)) else (if x<3226 then 1 else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10602 : Finset ℕ := ([18,68,132,250,1594,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10602 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10602 3300 4
  · have he : independentCachedBranchMembers10602.erase 3300=independentCachedBranchMembers10600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10600
  · have he : independentCachedBranchMembers10602.filter (independentCachedEdge 3300)=independentCachedBranchMembers10601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10601
def independentCachedBranchMembers10603 : Finset ℕ := ([132,1690,1708,1740,2618,2650,2668,2770,2788,3186,3226,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10603 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10603 4 (fun x => (if x<2668 then (if x<1740 then (if x<1690 then 0 else (if x<1708 then 1 else 0)) else (if x<2618 then 1 else (if x<2650 then 1 else 0))) else (if x<3186 then (if x<2770 then 1 else (if x<2788 then 2 else 2)) else (if x<3226 then 0 else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10604 : Finset ℕ := ([18,68,132,250,1594,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10604 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10604 2714 4
  · have he : independentCachedBranchMembers10604.erase 2714=independentCachedBranchMembers10602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10602
  · have he : independentCachedBranchMembers10604.filter (independentCachedEdge 2714)=independentCachedBranchMembers10603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10603
def independentCachedBranchMembers10605 : Finset ℕ := ([68,1594,1690,1708,1746,1764,2650,2668,2764,3162,3180,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10605 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10605 4 (fun x => (if x<2650 then (if x<1708 then (if x<1594 then 0 else (if x<1690 then 0 else 1)) else (if x<1746 then 1 else (if x<1764 then 2 else 2))) else (if x<3162 then (if x<2668 then 1 else (if x<2764 then 1 else 0)) else (if x<3180 then 2 else (if x<3250 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10606 : Finset ℕ := ([18,68,132,250,1594,1626,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10606 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10606 1626 4
  · have he : independentCachedBranchMembers10606.erase 1626=independentCachedBranchMembers10604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10604
  · have he : independentCachedBranchMembers10606.filter (independentCachedEdge 1626)=independentCachedBranchMembers10605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10605
def independentCachedBranchMembers10607 : Finset ℕ := ([68,132,250,1594,1714,1740,2618,2674,2764,3130,3186,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10607 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10607 4 (fun x => (if x<2618 then (if x<1594 then (if x<132 then 0 else (if x<250 then 1 else 2)) else (if x<1714 then 0 else (if x<1740 then 2 else 1))) else (if x<3130 then (if x<2674 then 1 else (if x<2764 then 2 else 0)) else (if x<3186 then 2 else (if x<3250 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10608 : Finset ℕ := ([18,36,68,132,250,1594,1626,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10608 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10608 36 4
  · have he : independentCachedBranchMembers10608.erase 36=independentCachedBranchMembers10606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10606
  · have he : independentCachedBranchMembers10608.filter (independentCachedEdge 36)=independentCachedBranchMembers10607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10607
def independentCachedBranchMembers10609 : Finset ℕ := ([68,132,1594,1740,1746,1764,2618,2764,2770,2788,3162,3180,3186,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10609 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10609 4 (fun x => (if x<2770 then (if x<1746 then (if x<1594 then (if x<132 then 0 else 1) else (if x<1740 then 0 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2764 then 1 else 0))) else (if x<3186 then (if x<3162 then (if x<2788 then 3 else 3) else (if x<3180 then 2 else 2)) else (if x<3244 then (if x<3226 then 1 else 3) else (if x<3250 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10610 : Finset ℕ := ([18,36,68,132,250,1594,1626,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10610 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10610 3282 4
  · have he : independentCachedBranchMembers10610.erase 3282=independentCachedBranchMembers10608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10608
  · have he : independentCachedBranchMembers10610.filter (independentCachedEdge 3282)=independentCachedBranchMembers10609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10609
def independentCachedBranchMembers10611 : Finset ℕ := ([36,250,1626,1690,1740,1746,2650,2714,2764,2770,3130,3180,3186,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10611 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10611 4 (fun x => (if x<2764 then (if x<1740 then (if x<1626 then (if x<250 then 0 else 1) else (if x<1690 then 0 else 1)) else (if x<2650 then (if x<1746 then 2 else 2) else (if x<2714 then 1 else 0))) else (if x<3186 then (if x<3130 then (if x<2770 then 3 else 3) else (if x<3180 then 1 else 2)) else (if x<3250 then (if x<3244 then 2 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10612 : Finset ℕ := ([18,36,68,132,250,1594,1626,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10612 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10612 3276 4
  · have he : independentCachedBranchMembers10612.erase 3276=independentCachedBranchMembers10610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10610
  · have he : independentCachedBranchMembers10612.filter (independentCachedEdge 3276)=independentCachedBranchMembers10611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10611
def independentCachedBranchMembers10613 : Finset ℕ := ([36,132,1626,1708,1714,1764,2618,2668,2674,2714,2764,2770,3162,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10613 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10613 4 (fun x => (if x<2674 then (if x<1714 then (if x<1626 then (if x<132 then 0 else 1) else (if x<1708 then 0 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2668 then 2 else 2))) else (if x<3162 then (if x<2764 then (if x<2714 then 1 else 0) else (if x<2770 then 3 else 3)) else (if x<3250 then (if x<3244 then 1 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10614 : Finset ℕ := ([18,36,68,132,250,1594,1626,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2738,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10614 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10614 2738 4
  · have he : independentCachedBranchMembers10614.erase 2738=independentCachedBranchMembers10612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10612
  · have he : independentCachedBranchMembers10614.filter (independentCachedEdge 2738)=independentCachedBranchMembers10613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10613
def independentCachedBranchMembers10615 : Finset ℕ := ([68,250,1594,1690,1708,1714,2650,2668,2674,2764,2770,2788,3130,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10615 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10615 4 (fun x => (if x<2674 then (if x<1708 then (if x<1594 then (if x<250 then 0 else 1) else (if x<1690 then 0 else 1)) else (if x<2650 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3130 then (if x<2770 then (if x<2764 then 2 else 0) else (if x<2788 then 3 else 3)) else (if x<3244 then (if x<3226 then 1 else 3) else (if x<3250 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10616 : Finset ℕ := ([18,36,68,132,250,1594,1626,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2732,2738,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10616 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10616 2732 4
  · have he : independentCachedBranchMembers10616.erase 2732=independentCachedBranchMembers10614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10614
  · have he : independentCachedBranchMembers10616.filter (independentCachedEdge 2732)=independentCachedBranchMembers10615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10615
def independentCachedBranchMembers10617 : Finset ℕ := ([36,68,1594,1626,1708,1714,1740,1746,2668,2674,2714,2788,3180,3186,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10617 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10617 4 (fun x => (if x<2668 then (if x<1708 then (if x<1594 then (if x<68 then 0 else 1) else (if x<1626 then 1 else 0)) else (if x<1740 then (if x<1714 then 2 else 2) else (if x<1746 then 3 else 3))) else (if x<3180 then (if x<2714 then (if x<2674 then 2 else 2) else (if x<2788 then 0 else 1)) else (if x<3226 then (if x<3186 then 3 else 3) else (if x<3300 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10618 : Finset ℕ := ([18,36,68,132,250,1594,1626,1650,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2732,2738,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10618 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10618 1650 4
  · have he : independentCachedBranchMembers10618.erase 1650=independentCachedBranchMembers10616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10616
  · have he : independentCachedBranchMembers10618.filter (independentCachedEdge 1650)=independentCachedBranchMembers10617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10617
def independentCachedBranchMembers10619 : Finset ℕ := ([250,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,3130,3162,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10619 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10619 4 (fun x => (if x<2618 then (if x<1714 then (if x<1690 then 0 else (if x<1708 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 2) else (if x<1764 then 2 else 3))) else (if x<3130 then (if x<2668 then (if x<2650 then 0 else 3) else (if x<2674 then 1 else 1)) else (if x<3180 then (if x<3162 then 3 else 0) else (if x<3186 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10620 : Finset ℕ := ([250,1690,1714,1746,2668,3180] : List ℕ).toFinset
theorem independentCachedBranchBound10620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10620 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10620 3 (fun x => (if x<1746 then (if x<1690 then 0 else (if x<1714 then 0 else 1)) else (if x<2668 then 2 else (if x<3180 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10621 : Finset ℕ := ([132,250,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,3130,3162,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10621 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10621 132 3
  · have he : independentCachedBranchMembers10621.erase 132=independentCachedBranchMembers10619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10619
  · have he : independentCachedBranchMembers10621.filter (independentCachedEdge 132)=independentCachedBranchMembers10620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10620
def independentCachedBranchMembers10622 : Finset ℕ := ([18,36,68,132,250,1594,1626,1644,1650,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2732,2738,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10622 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10622 1644 4
  · have he : independentCachedBranchMembers10622.erase 1644=independentCachedBranchMembers10618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10618
  · have he : independentCachedBranchMembers10622.filter (independentCachedEdge 1644)=independentCachedBranchMembers10621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10621
def independentCachedBranchMembers10623 : Finset ℕ := ([36,68,132,250,1594,1626,1690,1764,2618,2650,2714,2788,3130,3162,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10623 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10623 4 (fun x => (if x<2618 then (if x<1594 then (if x<132 then (if x<68 then 0 else 1) else (if x<250 then 2 else 3)) else (if x<1690 then (if x<1626 then 1 else 0) else (if x<1764 then 3 else 2))) else (if x<3130 then (if x<2714 then (if x<2650 then 2 else 3) else (if x<2788 then 0 else 1)) else (if x<3226 then (if x<3162 then 3 else 2) else (if x<3300 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
