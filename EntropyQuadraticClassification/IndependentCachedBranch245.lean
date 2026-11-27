/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch244
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10624 : Finset ℕ := ([12,18,36,68,132,250,1594,1626,1644,1650,1690,1708,1714,1740,1746,1764,2618,2650,2668,2674,2714,2732,2738,2764,2770,2788,3130,3162,3180,3186,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10624 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10624 12 4
  · have he : independentCachedBranchMembers10624.erase 12=independentCachedBranchMembers10622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10622
  · have he : independentCachedBranchMembers10624.filter (independentCachedEdge 12)=independentCachedBranchMembers10623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10623
def independentCachedBranchMembers10625 : Finset ℕ := ([12,18,20,34,36,66,68,130,132,250,252,1594,1596,1626,1628,1642,1644,1650,1652,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10625 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10625 20 5
  · have he : independentCachedBranchMembers10625.erase 20=independentCachedBranchMembers10597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10597
  · have he : independentCachedBranchMembers10625.filter (independentCachedEdge 20)=independentCachedBranchMembers10624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10624
def independentCachedBranchMembers10626 : Finset ℕ := ([12,130,252,1596,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10626 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10626 5 (fun x => (if x<2668 then (if x<1714 then (if x<1596 then (if x<130 then 0 else (if x<252 then 0 else 1)) else (if x<1692 then 0 else (if x<1708 then 1 else 2))) else (if x<1762 then (if x<1740 then 0 else (if x<1746 then 3 else 3)) else (if x<2620 then 2 else (if x<2652 then 1 else 0)))) else (if x<3164 then (if x<2770 then (if x<2674 then 3 else (if x<2764 then 2 else 1)) else (if x<2786 then 0 else (if x<3132 then 4 else 4))) else (if x<3228 then (if x<3180 then 1 else (if x<3186 then 0 else 4)) else (if x<3244 then 2 else (if x<3250 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10627 : Finset ℕ := ([130,252,1714,1740,2652,2668,2764,3164,3180,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10627 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10627 4 (fun x => (if x<2668 then (if x<1714 then (if x<252 then 0 else 1) else (if x<1740 then 0 else (if x<2652 then 1 else 0))) else (if x<3164 then (if x<2764 then 1 else 2) else (if x<3180 then 1 else (if x<3250 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10628 : Finset ℕ := ([12,66,130,252,1596,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10628 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10628 66 4
  · have he : independentCachedBranchMembers10628.erase 66=independentCachedBranchMembers10626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10626
  · have he : independentCachedBranchMembers10628.filter (independentCachedEdge 66)=independentCachedBranchMembers10627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10627
def independentCachedBranchMembers10629 : Finset ℕ := ([252,1708,1740,1762,2668,2764,2786,3132,3164,3186,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10629 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10629 4 (fun x => (if x<2786 then (if x<1762 then (if x<1708 then 0 else (if x<1740 then 0 else 1)) else (if x<2668 then 1 else (if x<2764 then 0 else 2))) else (if x<3186 then (if x<3132 then 2 else (if x<3164 then 0 else 1)) else (if x<3228 then 1 else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10630 : Finset ℕ := ([12,66,130,252,1596,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10630 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10630 3298 4
  · have he : independentCachedBranchMembers10630.erase 3298=independentCachedBranchMembers10628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10628
  · have he : independentCachedBranchMembers10630.filter (independentCachedEdge 3298)=independentCachedBranchMembers10629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10629
def independentCachedBranchMembers10631 : Finset ℕ := ([130,1692,1714,1746,2620,2652,2674,2764,2786,3180,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10631 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10631 4 (fun x => (if x<2674 then (if x<1746 then (if x<1692 then 0 else (if x<1714 then 1 else 0)) else (if x<2620 then 1 else (if x<2652 then 1 else 0))) else (if x<3180 then (if x<2764 then 1 else (if x<2786 then 2 else 2)) else (if x<3228 then 0 else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10632 : Finset ℕ := ([12,66,130,252,1596,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10632 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10632 2716 4
  · have he : independentCachedBranchMembers10632.erase 2716=independentCachedBranchMembers10630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10630
  · have he : independentCachedBranchMembers10632.filter (independentCachedEdge 2716)=independentCachedBranchMembers10631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10631
def independentCachedBranchMembers10633 : Finset ℕ := ([66,1596,1692,1714,1740,1762,2652,2674,2770,3164,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10633 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10633 4 (fun x => (if x<2652 then (if x<1714 then (if x<1596 then 0 else (if x<1692 then 0 else 1)) else (if x<1740 then 1 else (if x<1762 then 2 else 2))) else (if x<3164 then (if x<2674 then 1 else (if x<2770 then 1 else 0)) else (if x<3186 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10634 : Finset ℕ := ([12,66,130,252,1596,1628,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10634 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10634 1628 4
  · have he : independentCachedBranchMembers10634.erase 1628=independentCachedBranchMembers10632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10632
  · have he : independentCachedBranchMembers10634.filter (independentCachedEdge 1628)=independentCachedBranchMembers10633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10633
def independentCachedBranchMembers10635 : Finset ℕ := ([66,130,252,1596,1708,1746,2620,2668,2770,3132,3180,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10635 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10635 4 (fun x => (if x<2620 then (if x<1596 then (if x<130 then 0 else (if x<252 then 1 else 2)) else (if x<1708 then 0 else (if x<1746 then 2 else 1))) else (if x<3132 then (if x<2668 then 1 else (if x<2770 then 2 else 0)) else (if x<3180 then 2 else (if x<3244 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10636 : Finset ℕ := ([12,34,66,130,252,1596,1628,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10636 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10636 34 4
  · have he : independentCachedBranchMembers10636.erase 34=independentCachedBranchMembers10634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10634
  · have he : independentCachedBranchMembers10636.filter (independentCachedEdge 34)=independentCachedBranchMembers10635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10635
def independentCachedBranchMembers10637 : Finset ℕ := ([34,252,1628,1692,1740,1746,2652,2716,2764,2770,3132,3180,3186,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10637 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10637 4 (fun x => (if x<2764 then (if x<1740 then (if x<1628 then (if x<252 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<2652 then (if x<1746 then 2 else 2) else (if x<2716 then 1 else 0))) else (if x<3186 then (if x<3132 then (if x<2770 then 3 else 3) else (if x<3180 then 1 else 2)) else (if x<3250 then (if x<3244 then 2 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10638 : Finset ℕ := ([12,34,66,130,252,1596,1628,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10638 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10638 3282 4
  · have he : independentCachedBranchMembers10638.erase 3282=independentCachedBranchMembers10636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10636
  · have he : independentCachedBranchMembers10638.filter (independentCachedEdge 3282)=independentCachedBranchMembers10637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10637
def independentCachedBranchMembers10639 : Finset ℕ := ([66,130,1596,1740,1746,1762,2620,2764,2770,2786,3164,3180,3186,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10639 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10639 4 (fun x => (if x<2770 then (if x<1746 then (if x<1596 then (if x<130 then 0 else 1) else (if x<1740 then 0 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2764 then 1 else 3))) else (if x<3186 then (if x<3164 then (if x<2786 then 0 else 3) else (if x<3180 then 2 else 1)) else (if x<3244 then (if x<3228 then 2 else 3) else (if x<3250 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10640 : Finset ℕ := ([12,34,66,130,252,1596,1628,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10640 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10640 3276 4
  · have he : independentCachedBranchMembers10640.erase 3276=independentCachedBranchMembers10638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10638
  · have he : independentCachedBranchMembers10640.filter (independentCachedEdge 3276)=independentCachedBranchMembers10639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10639
def independentCachedBranchMembers10641 : Finset ℕ := ([66,252,1596,1692,1708,1714,2652,2668,2674,2764,2770,2786,3132,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10641 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10641 4 (fun x => (if x<2674 then (if x<1708 then (if x<1596 then (if x<252 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<2652 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3132 then (if x<2770 then (if x<2764 then 2 else 3) else (if x<2786 then 0 else 3)) else (if x<3244 then (if x<3228 then 1 else 3) else (if x<3250 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10642 : Finset ℕ := ([12,34,66,130,252,1596,1628,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2738,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10642 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10642 2738 4
  · have he : independentCachedBranchMembers10642.erase 2738=independentCachedBranchMembers10640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10640
  · have he : independentCachedBranchMembers10642.filter (independentCachedEdge 2738)=independentCachedBranchMembers10641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10641
def independentCachedBranchMembers10643 : Finset ℕ := ([34,130,1628,1708,1714,1762,2620,2668,2674,2716,2764,2770,3164,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10643 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10643 4 (fun x => (if x<2674 then (if x<1714 then (if x<1628 then (if x<130 then 0 else 1) else (if x<1708 then 0 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3164 then (if x<2764 then (if x<2716 then 2 else 0) else (if x<2770 then 3 else 3)) else (if x<3250 then (if x<3244 then 1 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10644 : Finset ℕ := ([12,34,66,130,252,1596,1628,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2732,2738,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10644 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10644 2732 4
  · have he : independentCachedBranchMembers10644.erase 2732=independentCachedBranchMembers10642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10642
  · have he : independentCachedBranchMembers10644.filter (independentCachedEdge 2732)=independentCachedBranchMembers10643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10643
def independentCachedBranchMembers10645 : Finset ℕ := ([252,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,3132,3164,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10645 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10645 4 (fun x => (if x<2620 then (if x<1714 then (if x<1692 then 0 else (if x<1708 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 2) else (if x<1762 then 2 else 3))) else (if x<3132 then (if x<2668 then (if x<2652 then 0 else 3) else (if x<2674 then 1 else 1)) else (if x<3180 then (if x<3164 then 3 else 0) else (if x<3186 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10646 : Finset ℕ := ([252,1692,1708,1740,2674,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10646 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10646 3 (fun x => (if x<1740 then (if x<1692 then 0 else (if x<1708 then 0 else 1)) else (if x<2674 then 2 else (if x<3186 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10647 : Finset ℕ := ([130,252,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,3132,3164,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10647 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10647 130 3
  · have he : independentCachedBranchMembers10647.erase 130=independentCachedBranchMembers10645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10645
  · have he : independentCachedBranchMembers10647.filter (independentCachedEdge 130)=independentCachedBranchMembers10646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10646
def independentCachedBranchMembers10648 : Finset ℕ := ([12,34,66,130,252,1596,1628,1650,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2732,2738,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10648 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10648 1650 4
  · have he : independentCachedBranchMembers10648.erase 1650=independentCachedBranchMembers10644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10644
  · have he : independentCachedBranchMembers10648.filter (independentCachedEdge 1650)=independentCachedBranchMembers10647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10647
def independentCachedBranchMembers10649 : Finset ℕ := ([34,66,1596,1628,1708,1714,1740,1746,2668,2674,2716,2786,3180,3186,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10649 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10649 4 (fun x => (if x<2668 then (if x<1708 then (if x<1596 then (if x<66 then 0 else 1) else (if x<1628 then 1 else 0)) else (if x<1740 then (if x<1714 then 2 else 2) else (if x<1746 then 3 else 3))) else (if x<3180 then (if x<2716 then (if x<2674 then 2 else 2) else (if x<2786 then 0 else 1)) else (if x<3228 then (if x<3186 then 3 else 3) else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10650 : Finset ℕ := ([12,34,66,130,252,1596,1628,1644,1650,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2732,2738,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10650 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10650 1644 4
  · have he : independentCachedBranchMembers10650.erase 1644=independentCachedBranchMembers10648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10648
  · have he : independentCachedBranchMembers10650.filter (independentCachedEdge 1644)=independentCachedBranchMembers10649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10649
def independentCachedBranchMembers10651 : Finset ℕ := ([34,66,130,252,1596,1628,1692,1762,2620,2652,2716,2786,3132,3164,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10651 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10651 4 (fun x => (if x<2620 then (if x<1596 then (if x<130 then (if x<66 then 0 else 1) else (if x<252 then 2 else 3)) else (if x<1692 then (if x<1628 then 1 else 0) else (if x<1762 then 3 else 2))) else (if x<3132 then (if x<2716 then (if x<2652 then 2 else 3) else (if x<2786 then 0 else 1)) else (if x<3228 then (if x<3164 then 3 else 2) else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10652 : Finset ℕ := ([12,18,34,66,130,252,1596,1628,1644,1650,1692,1708,1714,1740,1746,1762,2620,2652,2668,2674,2716,2732,2738,2764,2770,2786,3132,3164,3180,3186,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10652 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10652 18 4
  · have he : independentCachedBranchMembers10652.erase 18=independentCachedBranchMembers10650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10650
  · have he : independentCachedBranchMembers10652.filter (independentCachedEdge 18)=independentCachedBranchMembers10651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10651
def independentCachedBranchMembers10653 : Finset ℕ := ([10,12,18,20,34,36,66,68,130,132,250,252,1594,1596,1626,1628,1642,1644,1650,1652,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10653 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10653 10 5
  · have he : independentCachedBranchMembers10653.erase 10=independentCachedBranchMembers10625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10625
  · have he : independentCachedBranchMembers10653.filter (independentCachedEdge 10)=independentCachedBranchMembers10652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10652
def independentCachedBranchMembers10654 : Finset ℕ := ([6,10,12,18,20,24,34,36,40,48,66,68,72,80,96,126,130,132,136,144,160,190,192,222,238,246,250,252,1536,1566,1582,1590,1594,1596,1614,1622,1626,1628,1638,1642,1644,1650,1652,1656,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10654 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10654 6 6
  · have he : independentCachedBranchMembers10654.erase 6=independentCachedBranchMembers10296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10296
  · have he : independentCachedBranchMembers10654.filter (independentCachedEdge 6)=independentCachedBranchMembers10653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10653
end EntropyDesigns.QuadraticRefinement
