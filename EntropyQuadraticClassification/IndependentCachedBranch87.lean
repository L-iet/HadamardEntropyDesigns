/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch86
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5568 : Finset ℕ := ([132,252,1644,1652,1702,1708,1734,1748,2606,2620,2646,2652,2702,2710,2716,2788,3102,3174,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5568 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5568 1644 4
  · have he : independentCachedBranchMembers5568.erase 1644=independentCachedBranchMembers5566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5566
  · have he : independentCachedBranchMembers5568.filter (independentCachedEdge 1644)=independentCachedBranchMembers5567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5567
def independentCachedBranchMembers5569 : Finset ℕ := ([132,252,1652,1702,1708,1748,2606,2646,2652,2702,3188,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5569 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5569 4 (fun x => (if x<2646 then (if x<1702 then (if x<252 then 0 else (if x<1652 then 0 else 1)) else (if x<1748 then (if x<1708 then 1 else 0) else (if x<2606 then 0 else 2))) else (if x<3188 then (if x<2652 then 2 else (if x<2702 then 1 else 1)) else (if x<3244 then (if x<3238 then 3 else 3) else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5570 : Finset ℕ := ([132,252,1644,1652,1702,1708,1734,1748,2606,2620,2638,2646,2652,2702,2710,2716,2788,3102,3174,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5570 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5570 2638 4
  · have he : independentCachedBranchMembers5570.erase 2638=independentCachedBranchMembers5568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5568
  · have he : independentCachedBranchMembers5570.filter (independentCachedEdge 2638)=independentCachedBranchMembers5569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5569
def independentCachedBranchMembers5571 : Finset ℕ := ([132,252,1644,1708,1734,1748,2606,2620,2646,2710,3180,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5571 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5571 4 (fun x => (if x<2620 then (if x<1708 then (if x<252 then 0 else (if x<1644 then 0 else 1)) else (if x<1748 then (if x<1734 then 0 else 1) else (if x<2606 then 0 else 2))) else (if x<3180 then (if x<2646 then 1 else (if x<2710 then 2 else 1)) else (if x<3270 then (if x<3244 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5572 : Finset ℕ := ([132,252,1644,1652,1702,1708,1734,1748,2606,2614,2620,2638,2646,2652,2702,2710,2716,2788,3102,3174,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5572 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5572 2614 4
  · have he : independentCachedBranchMembers5572.erase 2614=independentCachedBranchMembers5570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5570
  · have he : independentCachedBranchMembers5572.filter (independentCachedEdge 2614)=independentCachedBranchMembers5571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5571
def independentCachedBranchMembers5573 : Finset ℕ := ([48,72,132,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5573 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5573 250 5
  · have he : independentCachedBranchMembers5573.erase 250=independentCachedBranchMembers5563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5563
  · have he : independentCachedBranchMembers5573.filter (independentCachedEdge 250)=independentCachedBranchMembers5572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5572
def independentCachedBranchMembers5574 : Finset ℕ := ([132,252,1650,1708,1748,1752,2606,2618,2646,2650,2716,2788,2792,2800,3102,3174,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5574 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5574 5 (fun x => (if x<2792 then (if x<2606 then (if x<1708 then (if x<252 then 0 else (if x<1650 then 0 else 1)) else (if x<1748 then 0 else (if x<1752 then 0 else 1))) else (if x<2650 then (if x<2618 then 2 else (if x<2646 then 3 else 2)) else (if x<2716 then 1 else (if x<2788 then 0 else 0)))) else (if x<3244 then (if x<3174 then (if x<2800 then 3 else (if x<3102 then 1 else 2)) else (if x<3178 then 2 else (if x<3186 then 3 else 4))) else (if x<3276 then (if x<3252 then 2 else (if x<3256 then 0 else 3)) else (if x<3284 then 0 else (if x<3288 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5575 : Finset ℕ := ([132,1708,1752,2606,2650,2788,3102,3178,3186,3256,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5575 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5575 4 (fun x => (if x<3102 then (if x<2606 then (if x<1708 then 0 else (if x<1752 then 0 else 1)) else (if x<2650 then 1 else (if x<2788 then 0 else 2))) else (if x<3256 then (if x<3178 then 2 else (if x<3186 then 3 else 0)) else (if x<3276 then 3 else (if x<3284 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5576 : Finset ℕ := ([132,252,1650,1708,1720,1748,1752,2606,2618,2646,2650,2716,2788,2792,2800,3102,3174,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5576 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5576 1720 4
  · have he : independentCachedBranchMembers5576.erase 1720=independentCachedBranchMembers5574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5574
  · have he : independentCachedBranchMembers5576.filter (independentCachedEdge 1720)=independentCachedBranchMembers5575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5575
def independentCachedBranchMembers5577 : Finset ℕ := ([252,1650,1748,2646,2788,2800,3102,3178,3244,3256,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5577 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5577 4 (fun x => (if x<3102 then (if x<2646 then (if x<1650 then 0 else (if x<1748 then 1 else 0)) else (if x<2788 then 1 else (if x<2800 then 0 else 1))) else (if x<3256 then (if x<3178 then 2 else (if x<3244 then 2 else 2)) else (if x<3276 then 3 else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5578 : Finset ℕ := ([132,252,1642,1650,1708,1720,1748,1752,2606,2618,2646,2650,2716,2788,2792,2800,3102,3174,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5578 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5578 1642 4
  · have he : independentCachedBranchMembers5578.erase 1642=independentCachedBranchMembers5576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5576
  · have he : independentCachedBranchMembers5578.filter (independentCachedEdge 1642)=independentCachedBranchMembers5577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5577
def independentCachedBranchMembers5579 : Finset ℕ := ([132,252,1650,1708,1748,1752,2606,2646,2650,2800,3186,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5579 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5579 4 (fun x => (if x<2646 then (if x<1708 then (if x<252 then 0 else (if x<1650 then 0 else 1)) else (if x<1752 then (if x<1748 then 0 else 0) else (if x<2606 then 1 else 2))) else (if x<3186 then (if x<2650 then 2 else (if x<2800 then 1 else 1)) else (if x<3284 then (if x<3244 then 3 else 2) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5580 : Finset ℕ := ([132,252,1642,1650,1708,1720,1748,1752,2606,2618,2638,2646,2650,2716,2788,2792,2800,3102,3174,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5580 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5580 2638 4
  · have he : independentCachedBranchMembers5580.erase 2638=independentCachedBranchMembers5578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5578
  · have he : independentCachedBranchMembers5580.filter (independentCachedEdge 2638)=independentCachedBranchMembers5579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5579
def independentCachedBranchMembers5581 : Finset ℕ := ([132,252,1642,1708,1720,1748,2606,2618,2646,2792,3178,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5581 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5581 4 (fun x => (if x<2618 then (if x<1708 then (if x<252 then 0 else (if x<1642 then 0 else 1)) else (if x<1748 then (if x<1720 then 0 else 1) else (if x<2606 then 0 else 2))) else (if x<3178 then (if x<2646 then 1 else (if x<2792 then 2 else 1)) else (if x<3256 then (if x<3244 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5582 : Finset ℕ := ([132,252,1642,1650,1708,1720,1748,1752,2606,2614,2618,2638,2646,2650,2716,2788,2792,2800,3102,3174,3178,3186,3244,3252,3256,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5582 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5582 2614 4
  · have he : independentCachedBranchMembers5582.erase 2614=independentCachedBranchMembers5580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5580
  · have he : independentCachedBranchMembers5582.filter (independentCachedEdge 2614)=independentCachedBranchMembers5581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5581
def independentCachedBranchMembers5583 : Finset ℕ := ([48,72,130,132,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5583 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5583 130 5
  · have he : independentCachedBranchMembers5583.erase 130=independentCachedBranchMembers5573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5573
  · have he : independentCachedBranchMembers5583.filter (independentCachedEdge 130)=independentCachedBranchMembers5582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5582
def independentCachedBranchMembers5584 : Finset ℕ := ([48,72,1644,1714,1734,1738,2614,2618,2620,2638,2710,2714,2786,2792,3102,3174,3178,3180,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5584 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5584 5 (fun x => (if x<2786 then (if x<2614 then (if x<1714 then (if x<72 then 0 else (if x<1644 then 0 else 1)) else (if x<1734 then 0 else (if x<1738 then 1 else 0))) else (if x<2638 then (if x<2618 then 0 else (if x<2620 then 2 else 1)) else (if x<2710 then 0 else (if x<2714 then 1 else 3)))) else (if x<3250 then (if x<3174 then (if x<2792 then 2 else (if x<3102 then 3 else 2)) else (if x<3178 then 4 else (if x<3180 then 2 else 3))) else (if x<3270 then (if x<3252 then 2 else (if x<3256 then 0 else 3)) else (if x<3274 then 2 else (if x<3276 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5585 : Finset ℕ := ([72,1714,1734,2614,2710,2786,3102,3178,3180,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5585 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5585 4 (fun x => (if x<3102 then (if x<2614 then (if x<1714 then 0 else (if x<1734 then 0 else 1)) else (if x<2710 then 0 else (if x<2786 then 1 else 1))) else (if x<3256 then (if x<3178 then 2 else (if x<3180 then 2 else 3)) else (if x<3274 then 2 else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5586 : Finset ℕ := ([48,72,1644,1714,1720,1734,1738,2614,2618,2620,2638,2710,2714,2786,2792,3102,3174,3178,3180,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5586 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5586 1720 4
  · have he : independentCachedBranchMembers5586.erase 1720=independentCachedBranchMembers5584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5584
  · have he : independentCachedBranchMembers5586.filter (independentCachedEdge 1720)=independentCachedBranchMembers5585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5585
def independentCachedBranchMembers5587 : Finset ℕ := ([48,1644,1738,2614,2620,2714,3102,3178,3250,3256,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5587 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5587 4 (fun x => (if x<3102 then (if x<2614 then (if x<1644 then 0 else (if x<1738 then 1 else 0)) else (if x<2620 then 0 else (if x<2714 then 1 else 1))) else (if x<3256 then (if x<3178 then 2 else (if x<3250 then 2 else 2)) else (if x<3270 then 3 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5588 : Finset ℕ := ([48,72,1642,1644,1714,1720,1734,1738,2614,2618,2620,2638,2710,2714,2786,2792,3102,3174,3178,3180,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5588 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5588 1642 4
  · have he : independentCachedBranchMembers5588.erase 1642=independentCachedBranchMembers5586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5586
  · have he : independentCachedBranchMembers5588.filter (independentCachedEdge 1642)=independentCachedBranchMembers5587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5587
def independentCachedBranchMembers5589 : Finset ℕ := ([48,72,1642,1714,1720,1738,2618,2714,2786,2792,3178,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5589 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5589 4 (fun x => (if x<2714 then (if x<1714 then (if x<72 then 0 else (if x<1642 then 0 else 1)) else (if x<1738 then (if x<1720 then 0 else 1) else (if x<2618 then 0 else 1))) else (if x<3178 then (if x<2786 then 2 else (if x<2792 then 2 else 1)) else (if x<3256 then (if x<3250 then 3 else 2) else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5590 : Finset ℕ := ([48,72,1642,1644,1714,1720,1734,1738,2614,2618,2620,2638,2710,2714,2786,2788,2792,3102,3174,3178,3180,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5590 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5590 2788 4
  · have he : independentCachedBranchMembers5590.erase 2788=independentCachedBranchMembers5588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5588
  · have he : independentCachedBranchMembers5590.filter (independentCachedEdge 2788)=independentCachedBranchMembers5589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5589
def independentCachedBranchMembers5591 : Finset ℕ := ([48,72,1644,1714,1734,1738,2620,2710,2714,2786,3180,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5591 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5591 4 (fun x => (if x<2710 then (if x<1714 then (if x<72 then 0 else (if x<1644 then 0 else 1)) else (if x<1738 then (if x<1734 then 0 else 1) else (if x<2620 then 0 else 1))) else (if x<3180 then (if x<2714 then 1 else (if x<2786 then 2 else 2)) else (if x<3270 then (if x<3250 then 3 else 2) else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5592 : Finset ℕ := ([48,72,1642,1644,1714,1720,1734,1738,2614,2618,2620,2638,2710,2714,2716,2786,2788,2792,3102,3174,3178,3180,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5592 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5592 2716 4
  · have he : independentCachedBranchMembers5592.erase 2716=independentCachedBranchMembers5590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5590
  · have he : independentCachedBranchMembers5592.filter (independentCachedEdge 2716)=independentCachedBranchMembers5591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5591
def independentCachedBranchMembers5593 : Finset ℕ := ([48,72,80,130,132,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5593 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5593 80 5
  · have he : independentCachedBranchMembers5593.erase 80=independentCachedBranchMembers5583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5583
  · have he : independentCachedBranchMembers5593.filter (independentCachedEdge 80)=independentCachedBranchMembers5592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5592
def independentCachedBranchMembers5594 : Finset ℕ := ([48,72,1652,1714,1738,1752,2614,2638,2650,2652,2702,2714,2786,2800,3102,3174,3186,3188,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5594 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5594 5 (fun x => (if x<2786 then (if x<2614 then (if x<1714 then (if x<72 then 0 else (if x<1652 then 0 else 1)) else (if x<1738 then 0 else (if x<1752 then 0 else 1))) else (if x<2652 then (if x<2638 then 0 else (if x<2650 then 0 else 2)) else (if x<2702 then 1 else (if x<2714 then 2 else 1)))) else (if x<3238 then (if x<3174 then (if x<2800 then 2 else (if x<3102 then 1 else 2)) else (if x<3186 then 3 else (if x<3188 then 2 else 4))) else (if x<3274 then (if x<3250 then 2 else (if x<3252 then 3 else 0)) else (if x<3276 then 2 else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5595 : Finset ℕ := ([48,1714,1752,2638,2714,2800,3102,3186,3188,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5595 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5595 4 (fun x => (if x<3102 then (if x<2638 then (if x<1714 then 0 else (if x<1752 then 0 else 1)) else (if x<2714 then 0 else (if x<2800 then 1 else 1))) else (if x<3238 then (if x<3186 then 2 else (if x<3188 then 2 else 3)) else (if x<3274 then 2 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5596 : Finset ℕ := ([48,72,1652,1702,1714,1738,1752,2614,2638,2650,2652,2702,2714,2786,2800,3102,3174,3186,3188,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5596 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5596 1702 4
  · have he : independentCachedBranchMembers5596.erase 1702=independentCachedBranchMembers5594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5594
  · have he : independentCachedBranchMembers5596.filter (independentCachedEdge 1702)=independentCachedBranchMembers5595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5595
def independentCachedBranchMembers5597 : Finset ℕ := ([72,1652,1714,2638,2652,2714,3102,3186,3238,3252,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5597 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5597 4 (fun x => (if x<3102 then (if x<2638 then (if x<1652 then 0 else (if x<1714 then 1 else 0)) else (if x<2652 then 0 else (if x<2714 then 1 else 1))) else (if x<3252 then (if x<3186 then 2 else (if x<3238 then 2 else 2)) else (if x<3274 then 0 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5598 : Finset ℕ := ([48,72,1650,1652,1702,1714,1738,1752,2614,2638,2650,2652,2702,2714,2786,2800,3102,3174,3186,3188,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5598 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5598 1650 4
  · have he : independentCachedBranchMembers5598.erase 1650=independentCachedBranchMembers5596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5596
  · have he : independentCachedBranchMembers5598.filter (independentCachedEdge 1650)=independentCachedBranchMembers5597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5597
def independentCachedBranchMembers5599 : Finset ℕ := ([48,72,1650,1714,1738,1752,2650,2714,2786,2800,3186,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5599 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5599 4 (fun x => (if x<2714 then (if x<1714 then (if x<72 then 0 else (if x<1650 then 0 else 1)) else (if x<1752 then (if x<1738 then 0 else 0) else (if x<2650 then 1 else 1))) else (if x<3186 then (if x<2786 then 2 else (if x<2800 then 2 else 1)) else (if x<3274 then (if x<3250 then 3 else 2) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
