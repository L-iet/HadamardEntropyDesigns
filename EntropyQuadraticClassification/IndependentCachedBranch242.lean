/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch241
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10528 : Finset ℕ := ([66,132,252,1596,1626,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10528 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10528 66 4
  · have he : independentCachedBranchMembers10528.erase 66=independentCachedBranchMembers10526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10526
  · have he : independentCachedBranchMembers10528.filter (independentCachedEdge 66)=independentCachedBranchMembers10527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10527
def independentCachedBranchMembers10529 : Finset ℕ := ([132,1692,1706,1740,2618,2652,2666,2772,2786,3186,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound10529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10529 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10529 4 (fun x => (if x<2666 then (if x<1740 then (if x<1692 then 0 else (if x<1706 then 0 else 1)) else (if x<2618 then 1 else (if x<2652 then 1 else 1))) else (if x<3186 then (if x<2772 then 0 else (if x<2786 then 2 else 2)) else (if x<3228 then 0 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10530 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10530 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10530 36 4
  · have he : independentCachedBranchMembers10530.erase 36=independentCachedBranchMembers10528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10528
  · have he : independentCachedBranchMembers10530.filter (independentCachedEdge 36)=independentCachedBranchMembers10529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10529
def independentCachedBranchMembers10531 : Finset ℕ := ([132,252,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,3132,3162,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10531 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10531 4 (fun x => (if x<2618 then (if x<1716 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3132 then (if x<2666 then (if x<2652 then 2 else 2) else (if x<2676 then 3 else 3)) else (if x<3180 then (if x<3162 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10532 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10532 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10532 3282 4
  · have he : independentCachedBranchMembers10532.erase 3282=independentCachedBranchMembers10530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10530
  · have he : independentCachedBranchMembers10532.filter (independentCachedEdge 3282)=independentCachedBranchMembers10531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10531
def independentCachedBranchMembers10533 : Finset ℕ := ([36,66,1596,1626,1706,1716,1740,1746,2666,2676,2714,2786,3180,3186,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10533 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10533 4 (fun x => (if x<2666 then (if x<1706 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1626 then 0 else 0)) else (if x<1740 then (if x<1716 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3180 then (if x<2714 then (if x<2676 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3186 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10534 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10534 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10534 3276 4
  · have he : independentCachedBranchMembers10534.erase 3276=independentCachedBranchMembers10532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10532
  · have he : independentCachedBranchMembers10534.filter (independentCachedEdge 3276)=independentCachedBranchMembers10533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10533
def independentCachedBranchMembers10535 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1764,2618,2652,2714,2786,3132,3162,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10535 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10535 4 (fun x => (if x<2618 then (if x<1596 then (if x<132 then (if x<66 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1692 then (if x<1626 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3132 then (if x<2714 then (if x<2652 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3162 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10536 : Finset ℕ := ([36,66,132,252,1596,1626,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2738,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10536 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10536 2738 4
  · have he : independentCachedBranchMembers10536.erase 2738=independentCachedBranchMembers10534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10534
  · have he : independentCachedBranchMembers10536.filter (independentCachedEdge 2738)=independentCachedBranchMembers10535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10535
def independentCachedBranchMembers10537 : Finset ℕ := ([36,252,1626,1692,1740,1746,2652,2714,2762,2772,3132,3180,3186,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10537 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10537 4 (fun x => (if x<2762 then (if x<1740 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1746 then 2 else 2) else (if x<2714 then 1 else 1))) else (if x<3186 then (if x<3132 then (if x<2772 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10538 : Finset ℕ := ([36,66,132,252,1596,1626,1650,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2738,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10538 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10538 1650 4
  · have he : independentCachedBranchMembers10538.erase 1650=independentCachedBranchMembers10536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10536
  · have he : independentCachedBranchMembers10538.filter (independentCachedEdge 1650)=independentCachedBranchMembers10537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10537
def independentCachedBranchMembers10539 : Finset ℕ := ([66,132,1596,1740,1746,1764,2618,2762,2772,2786,3162,3180,3186,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10539 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10539 4 (fun x => (if x<2772 then (if x<1746 then (if x<1596 then (if x<132 then 0 else 0) else (if x<1740 then 1 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2762 then 1 else 1))) else (if x<3186 then (if x<3162 then (if x<2786 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3242 then (if x<3228 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10540 : Finset ℕ := ([36,66,132,252,1596,1626,1644,1650,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2738,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10540 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10540 1644 4
  · have he : independentCachedBranchMembers10540.erase 1644=independentCachedBranchMembers10538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10538
  · have he : independentCachedBranchMembers10540.filter (independentCachedEdge 1644)=independentCachedBranchMembers10539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10539
def independentCachedBranchMembers10541 : Finset ℕ := ([66,252,1596,1692,1706,1716,2652,2666,2676,2762,2772,2786,3132,3228,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10541 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10541 4 (fun x => (if x<2676 then (if x<1706 then (if x<1596 then (if x<252 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<2652 then (if x<1716 then 2 else 2) else (if x<2666 then 1 else 2))) else (if x<3132 then (if x<2772 then (if x<2762 then 2 else 0) else (if x<2786 then 3 else 3)) else (if x<3242 then (if x<3228 then 1 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10542 : Finset ℕ := ([18,36,66,132,252,1596,1626,1644,1650,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2738,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10542 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10542 18 4
  · have he : independentCachedBranchMembers10542.erase 18=independentCachedBranchMembers10540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10540
  · have he : independentCachedBranchMembers10542.filter (independentCachedEdge 18)=independentCachedBranchMembers10541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10541
def independentCachedBranchMembers10543 : Finset ℕ := ([36,132,1626,1706,1716,1764,2618,2666,2676,2714,2762,2772,3162,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10543 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10543 4 (fun x => (if x<2676 then (if x<1716 then (if x<1626 then (if x<132 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<2618 then (if x<1764 then 1 else 2) else (if x<2666 then 2 else 1))) else (if x<3162 then (if x<2762 then (if x<2714 then 2 else 0) else (if x<2772 then 3 else 3)) else (if x<3252 then (if x<3242 then 1 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10544 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1706,1716,1740,1746,1764,2618,2652,2666,2676,2714,2732,2738,2762,2772,2786,3132,3162,3180,3186,3228,3242,3252,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10544 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10544 12 4
  · have he : independentCachedBranchMembers10544.erase 12=independentCachedBranchMembers10542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10542
  · have he : independentCachedBranchMembers10544.filter (independentCachedEdge 12)=independentCachedBranchMembers10543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10543
def independentCachedBranchMembers10545 : Finset ℕ := ([12,18,34,36,66,68,130,132,250,252,1594,1596,1626,1628,1644,1650,1690,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound10545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10545 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10545 2730 5
  · have he : independentCachedBranchMembers10545.erase 2730=independentCachedBranchMembers10525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10525
  · have he : independentCachedBranchMembers10545.filter (independentCachedEdge 2730)=independentCachedBranchMembers10544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10544
def independentCachedBranchMembers10546 : Finset ℕ := ([66,250,1596,1628,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10546 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10546 5 (fun x => (if x<2666 then (if x<1706 then (if x<1628 then (if x<250 then 0 else (if x<1596 then 0 else 1)) else (if x<1650 then 2 else (if x<1690 then 0 else 1))) else (if x<1748 then (if x<1716 then 3 else (if x<1738 then 2 else 0)) else (if x<2618 then (if x<1764 then 1 else 3) else (if x<2650 then 1 else 0)))) else (if x<3162 then (if x<2764 then (if x<2676 then 4 else (if x<2716 then 1 else 1)) else (if x<2786 then (if x<2770 then 4 else 1) else (if x<3130 then 0 else 3))) else (if x<3228 then (if x<3178 then 2 else (if x<3188 then 0 else 2)) else (if x<3250 then (if x<3244 then 2 else 3) else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10547 : Finset ℕ := ([250,1596,1628,1690,1706,1738,2676,2770,2786,3188,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10547 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10547 4 (fun x => (if x<2676 then (if x<1690 then (if x<1596 then 0 else (if x<1628 then 1 else 2)) else (if x<1706 then 0 else (if x<1738 then 1 else 2))) else (if x<3188 then (if x<2770 then 1 else (if x<2786 then 0 else 1)) else (if x<3250 then 2 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10548 : Finset ℕ := ([66,132,250,1596,1628,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10548 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10548 132 4
  · have he : independentCachedBranchMembers10548.erase 132=independentCachedBranchMembers10546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10546
  · have he : independentCachedBranchMembers10548.filter (independentCachedEdge 132)=independentCachedBranchMembers10547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10547
def independentCachedBranchMembers10549 : Finset ℕ := ([66,1596,1690,1716,1738,1764,2650,2676,2770,3162,3188,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10549 4 (fun x => (if x<2650 then (if x<1716 then (if x<1596 then 0 else (if x<1690 then 0 else 1)) else (if x<1738 then 1 else (if x<1764 then 2 else 2))) else (if x<3162 then (if x<2676 then 1 else (if x<2770 then 1 else 0)) else (if x<3188 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10550 : Finset ℕ := ([34,66,132,250,1596,1628,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10550 34 4
  · have he : independentCachedBranchMembers10550.erase 34=independentCachedBranchMembers10548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10548
  · have he : independentCachedBranchMembers10550.filter (independentCachedEdge 34)=independentCachedBranchMembers10549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10549
def independentCachedBranchMembers10551 : Finset ℕ := ([132,1628,1706,1716,1764,2618,2666,2676,2716,2764,2770,3162,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10551 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10551 4 (fun x => (if x<2676 then (if x<1716 then (if x<1628 then 0 else (if x<1706 then 1 else 2)) else (if x<2618 then (if x<1764 then 0 else 1) else (if x<2666 then 2 else 0))) else (if x<3162 then (if x<2764 then (if x<2716 then 1 else 3) else (if x<2770 then 1 else 3)) else (if x<3250 then (if x<3244 then 0 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10552 : Finset ℕ := ([1716,1764,2676,2770,3162,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10552 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10552 3 (fun x => (if x<2770 then (if x<1764 then 0 else (if x<2676 then 1 else 0)) else (if x<3162 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10553 : Finset ℕ := ([34,132,1628,1706,1716,1764,2618,2666,2676,2716,2764,2770,3162,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10553 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10553 34 3
  · have he : independentCachedBranchMembers10553.erase 34=independentCachedBranchMembers10551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10551
  · have he : independentCachedBranchMembers10553.filter (independentCachedEdge 34)=independentCachedBranchMembers10552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10552
def independentCachedBranchMembers10554 : Finset ℕ := ([34,66,132,250,1596,1628,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10554 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10554 3282 4
  · have he : independentCachedBranchMembers10554.erase 3282=independentCachedBranchMembers10550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10550
  · have he : independentCachedBranchMembers10554.filter (independentCachedEdge 3282)=independentCachedBranchMembers10553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10553
def independentCachedBranchMembers10555 : Finset ℕ := ([250,1596,1690,1706,1716,2650,2666,2676,2764,2770,2786,3130,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10555 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10555 4 (fun x => (if x<2676 then (if x<1706 then (if x<1596 then 0 else (if x<1690 then 1 else 0)) else (if x<2650 then (if x<1716 then 1 else 2) else (if x<2666 then 0 else 2))) else (if x<3130 then (if x<2770 then (if x<2764 then 1 else 3) else (if x<2786 then 3 else 1)) else (if x<3244 then (if x<3228 then 0 else 2) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10556 : Finset ℕ := ([1690,1706,2676,2764,3130,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10556 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10556 3 (fun x => (if x<2764 then (if x<1706 then 0 else (if x<2676 then 1 else 0)) else (if x<3130 then 2 else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10557 : Finset ℕ := ([66,250,1596,1690,1706,1716,2650,2666,2676,2764,2770,2786,3130,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10557 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10557 66 3
  · have he : independentCachedBranchMembers10557.erase 66=independentCachedBranchMembers10555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10555
  · have he : independentCachedBranchMembers10557.filter (independentCachedEdge 66)=independentCachedBranchMembers10556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10556
def independentCachedBranchMembers10558 : Finset ℕ := ([34,66,132,250,1596,1628,1650,1690,1706,1716,1738,1748,1764,2618,2650,2666,2676,2716,2764,2770,2786,3130,3162,3178,3188,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10558 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10558 3276 4
  · have he : independentCachedBranchMembers10558.erase 3276=independentCachedBranchMembers10554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10554
  · have he : independentCachedBranchMembers10558.filter (independentCachedEdge 3276)=independentCachedBranchMembers10557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10557
def independentCachedBranchMembers10559 : Finset ℕ := ([66,132,1596,1738,1748,1764,2618,2764,2770,2786,3162,3178,3188,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10559 4 (fun x => (if x<2770 then (if x<1748 then (if x<1596 then (if x<132 then 0 else 0) else (if x<1738 then 1 else 2)) else (if x<2618 then (if x<1764 then 1 else 2) else (if x<2764 then 1 else 2))) else (if x<3188 then (if x<3162 then (if x<2786 then 1 else 2) else (if x<3178 then 0 else 3)) else (if x<3244 then (if x<3228 then 3 else 0) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
