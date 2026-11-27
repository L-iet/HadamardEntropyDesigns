/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch88
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5632 : Finset ℕ := ([72,132,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3102,3178,3188,3192,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5632 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5632 72 4
  · have he : independentCachedBranchMembers5632.erase 72=independentCachedBranchMembers5630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5630
  · have he : independentCachedBranchMembers5632.filter (independentCachedEdge 72)=independentCachedBranchMembers5631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5631
def independentCachedBranchMembers5633 : Finset ℕ := ([1644,1708,1748,1752,2652,2716,2788,2792,3102,3178,3238,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5633 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5633 4 (fun x => (if x<2788 then (if x<1752 then (if x<1708 then 0 else (if x<1748 then 1 else 0)) else (if x<2652 then 1 else (if x<2716 then 0 else 1))) else (if x<3178 then (if x<2792 then 0 else (if x<3102 then 1 else 2)) else (if x<3238 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5634 : Finset ℕ := ([48,72,132,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3102,3178,3188,3192,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5634 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5634 48 4
  · have he : independentCachedBranchMembers5634.erase 48=independentCachedBranchMembers5632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5632
  · have he : independentCachedBranchMembers5634.filter (independentCachedEdge 48)=independentCachedBranchMembers5633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5633
def independentCachedBranchMembers5635 : Finset ℕ := ([48,72,132,252,1644,1650,1734,1752,2614,2638,2716,2788,3178,3188,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5635 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5635 4 (fun x => (if x<2614 then (if x<1644 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3178 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3238 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5636 : Finset ℕ := ([48,72,132,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3102,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5636 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5636 3242 4
  · have he : independentCachedBranchMembers5636.erase 3242=independentCachedBranchMembers5634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5634
  · have he : independentCachedBranchMembers5636.filter (independentCachedEdge 3242)=independentCachedBranchMembers5635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5635
def independentCachedBranchMembers5637 : Finset ℕ := ([48,72,132,252,1708,1714,1738,1748,2618,2652,2702,2792,3178,3188,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5637 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5637 4 (fun x => (if x<2618 then (if x<1708 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3238 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5638 : Finset ℕ := ([48,72,132,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5638 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5638 3174 4
  · have he : independentCachedBranchMembers5638.erase 3174=independentCachedBranchMembers5636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5636
  · have he : independentCachedBranchMembers5638.filter (independentCachedEdge 3174)=independentCachedBranchMembers5637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5637
def independentCachedBranchMembers5639 : Finset ℕ := ([1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792] : List ℕ).toFinset
theorem independentCachedBranchBound5639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5639 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5639 4 (fun x => (if x<2614 then (if x<1734 then (if x<1708 then (if x<1650 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<2702 then (if x<2638 then (if x<2618 then 2 else 3) else (if x<2652 then 2 else 3)) else (if x<2788 then (if x<2716 then 3 else 2) else (if x<2792 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5640 : Finset ℕ := ([48,72,132,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5640 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5640 3072 4
  · have he : independentCachedBranchMembers5640.erase 3072=independentCachedBranchMembers5638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5638
  · have he : independentCachedBranchMembers5640.filter (independentCachedEdge 3072)=independentCachedBranchMembers5639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5639
def independentCachedBranchMembers5641 : Finset ℕ := ([48,252,1650,1714,1748,1752,2614,2618,2652,2716,3102,3188,3192,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5641 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5641 4 (fun x => (if x<2652 then (if x<1748 then (if x<1650 then (if x<252 then 0 else 0) else (if x<1714 then 1 else 2)) else (if x<2614 then (if x<1752 then 1 else 2) else (if x<2618 then 2 else 1))) else (if x<3192 then (if x<3102 then (if x<2716 then 2 else 1) else (if x<3188 then 3 else 0)) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3282 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5642 : Finset ℕ := ([48,72,132,238,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5642 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5642 238 4
  · have he : independentCachedBranchMembers5642.erase 238=independentCachedBranchMembers5640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5640
  · have he : independentCachedBranchMembers5642.filter (independentCachedEdge 238)=independentCachedBranchMembers5641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5641
def independentCachedBranchMembers5643 : Finset ℕ := ([72,132,1644,1714,1734,1748,2618,2638,2652,2788,3102,3178,3192,3238,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5643 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5643 4 (fun x => (if x<2652 then (if x<1734 then (if x<1644 then (if x<132 then 0 else 0) else (if x<1714 then 1 else 2)) else (if x<2618 then (if x<1748 then 1 else 2) else (if x<2638 then 2 else 1))) else (if x<3192 then (if x<3102 then (if x<2788 then 2 else 1) else (if x<3178 then 3 else 0)) else (if x<3252 then (if x<3238 then 3 else 0) else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5644 : Finset ℕ := ([48,72,132,136,238,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5644 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5644 136 4
  · have he : independentCachedBranchMembers5644.erase 136=independentCachedBranchMembers5642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5642
  · have he : independentCachedBranchMembers5644.filter (independentCachedEdge 136)=independentCachedBranchMembers5643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5643
def independentCachedBranchMembers5645 : Finset ℕ := ([72,132,1650,1708,1738,1752,2614,2702,2716,2792,3102,3178,3192,3238,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5645 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5645 4 (fun x => (if x<2716 then (if x<1738 then (if x<1650 then (if x<132 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2614 then (if x<1752 then 1 else 2) else (if x<2702 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2792 then 2 else 2) else (if x<3178 then 3 else 0)) else (if x<3252 then (if x<3238 then 3 else 0) else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5646 : Finset ℕ := ([48,68,72,132,136,238,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5646 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5646 68 4
  · have he : independentCachedBranchMembers5646.erase 68=independentCachedBranchMembers5644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5644
  · have he : independentCachedBranchMembers5646.filter (independentCachedEdge 68)=independentCachedBranchMembers5645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5645
def independentCachedBranchMembers5647 : Finset ℕ := ([48,252,1644,1708,1734,1738,2638,2702,2788,2792,3102,3188,3192,3252,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5647 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5647 4 (fun x => (if x<2788 then (if x<1734 then (if x<1644 then (if x<252 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2638 then (if x<1738 then 1 else 2) else (if x<2702 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2792 then 1 else 2) else (if x<3188 then 3 else 0)) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3282 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5648 : Finset ℕ := ([34,48,68,72,132,136,238,252,1644,1650,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2702,2716,2788,2792,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5648 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5648 34 4
  · have he : independentCachedBranchMembers5648.erase 34=independentCachedBranchMembers5646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5646
  · have he : independentCachedBranchMembers5648.filter (independentCachedEdge 34)=independentCachedBranchMembers5647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5647
def independentCachedBranchMembers5649 : Finset ℕ := ([34,36,40,48,66,68,72,80,130,132,136,144,238,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5649 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5649 1746 5
  · have he : independentCachedBranchMembers5649.erase 1746=independentCachedBranchMembers5629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5629
  · have he : independentCachedBranchMembers5649.filter (independentCachedEdge 1746)=independentCachedBranchMembers5648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5648
def independentCachedBranchMembers5650 : Finset ℕ := ([130,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3102,3178,3188,3192,3238,3242,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5650 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5650 5 (fun x => (if x<2650 then (if x<1734 then (if x<1650 then (if x<250 then 0 else (if x<1644 then 0 else 1)) else (if x<1708 then 1 else (if x<1714 then 2 else 0))) else (if x<1752 then (if x<1738 then 1 else (if x<1748 then 0 else 2)) else (if x<2620 then (if x<2606 then 1 else 2) else (if x<2646 then 3 else 2)))) else (if x<3188 then (if x<2786 then (if x<2710 then 3 else (if x<2714 then 3 else 0)) else (if x<3102 then (if x<2800 then 0 else 3) else (if x<3178 then 3 else 4))) else (if x<3242 then (if x<3192 then 4 else (if x<3238 then 1 else 4)) else (if x<3276 then (if x<3256 then 0 else 4) else (if x<3282 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5651 : Finset ℕ := ([1644,1714,1734,1738,2620,2710,2714,2786,3102,3178,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5651 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5651 4 (fun x => (if x<2714 then (if x<1738 then (if x<1714 then 0 else (if x<1734 then 1 else 0)) else (if x<2620 then 1 else (if x<2710 then 0 else 0))) else (if x<3178 then (if x<2786 then 1 else (if x<3102 then 1 else 2)) else (if x<3256 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5652 : Finset ℕ := ([80,130,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3102,3178,3188,3192,3238,3242,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5652 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5652 80 4
  · have he : independentCachedBranchMembers5652.erase 80=independentCachedBranchMembers5650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5650
  · have he : independentCachedBranchMembers5652.filter (independentCachedEdge 80)=independentCachedBranchMembers5651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5651
def independentCachedBranchMembers5653 : Finset ℕ := ([1650,1714,1738,1752,2650,2714,2786,2800,3102,3188,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5653 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5653 4 (fun x => (if x<2786 then (if x<1752 then (if x<1714 then 0 else (if x<1738 then 1 else 0)) else (if x<2650 then 1 else (if x<2714 then 0 else 1))) else (if x<3188 then (if x<2800 then 0 else (if x<3102 then 1 else 2)) else (if x<3238 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5654 : Finset ℕ := ([40,80,130,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3102,3178,3188,3192,3238,3242,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5654 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5654 40 4
  · have he : independentCachedBranchMembers5654.erase 40=independentCachedBranchMembers5652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5652
  · have he : independentCachedBranchMembers5654.filter (independentCachedEdge 40)=independentCachedBranchMembers5653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5653
def independentCachedBranchMembers5655 : Finset ℕ := ([40,80,130,250,1644,1650,1734,1752,2606,2646,2714,2786,3178,3188,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5655 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5655 4 (fun x => (if x<2606 then (if x<1644 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1734 then (if x<1650 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3178 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3238 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5656 : Finset ℕ := ([40,80,130,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3102,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5656 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5656 3252 4
  · have he : independentCachedBranchMembers5656.erase 3252=independentCachedBranchMembers5654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5654
  · have he : independentCachedBranchMembers5656.filter (independentCachedEdge 3252)=independentCachedBranchMembers5655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5655
def independentCachedBranchMembers5657 : Finset ℕ := ([40,80,130,250,1708,1714,1738,1748,2620,2650,2710,2800,3178,3188,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5657 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5657 4 (fun x => (if x<2620 then (if x<1708 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3238 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5658 : Finset ℕ := ([40,80,130,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5658 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5658 3174 4
  · have he : independentCachedBranchMembers5658.erase 3174=independentCachedBranchMembers5656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5656
  · have he : independentCachedBranchMembers5658.filter (independentCachedEdge 3174)=independentCachedBranchMembers5657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5657
def independentCachedBranchMembers5659 : Finset ℕ := ([1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5659 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5659 4 (fun x => (if x<2606 then (if x<1734 then (if x<1708 then (if x<1650 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<2710 then (if x<2646 then (if x<2620 then 2 else 3) else (if x<2650 then 2 else 3)) else (if x<2786 then (if x<2714 then 3 else 2) else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5660 : Finset ℕ := ([40,80,130,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5660 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5660 3072 4
  · have he : independentCachedBranchMembers5660.erase 3072=independentCachedBranchMembers5658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5658
  · have he : independentCachedBranchMembers5660.filter (independentCachedEdge 3072)=independentCachedBranchMembers5659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5659
def independentCachedBranchMembers5661 : Finset ℕ := ([40,250,1644,1708,1738,1752,2606,2620,2650,2714,3102,3178,3192,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5661 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5661 4 (fun x => (if x<2650 then (if x<1738 then (if x<1644 then (if x<250 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2620 then 2 else 1))) else (if x<3192 then (if x<3102 then (if x<2714 then 2 else 1) else (if x<3178 then 3 else 0)) else (if x<3256 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5662 : Finset ℕ := ([40,80,130,246,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5662 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5662 246 4
  · have he : independentCachedBranchMembers5662.erase 246=independentCachedBranchMembers5660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5660
  · have he : independentCachedBranchMembers5662.filter (independentCachedEdge 246)=independentCachedBranchMembers5661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5661
def independentCachedBranchMembers5663 : Finset ℕ := ([80,130,1650,1708,1734,1738,2620,2646,2650,2786,3102,3188,3192,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5663 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5663 4 (fun x => (if x<2650 then (if x<1734 then (if x<1650 then (if x<130 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2620 then (if x<1738 then 1 else 2) else (if x<2646 then 2 else 1))) else (if x<3192 then (if x<3102 then (if x<2786 then 2 else 1) else (if x<3188 then 3 else 0)) else (if x<3242 then (if x<3238 then 3 else 0) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
