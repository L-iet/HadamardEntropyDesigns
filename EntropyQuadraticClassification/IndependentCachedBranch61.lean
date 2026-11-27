/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch60
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4736 : Finset ℕ := ([1594,1596,1614,1644,1702,1748,1776,2606,2650,2652,2680,2710,2738,2740,2758,2786,2788,3130,3132,3150,3178,3238,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4736 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4736 2710 4
  · have he : independentCachedBranchMembers4736.erase 2710=independentCachedBranchMembers4734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4734
  · have he : independentCachedBranchMembers4736.filter (independentCachedEdge 2710)=independentCachedBranchMembers4735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4735
def independentCachedBranchMembers4737 : Finset ℕ := ([136,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4737 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4737 136 5
  · have he : independentCachedBranchMembers4737.erase 136=independentCachedBranchMembers4733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4733
  · have he : independentCachedBranchMembers4737.filter (independentCachedEdge 136)=independentCachedBranchMembers4736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4736
def independentCachedBranchMembers4738 : Finset ℕ := ([1596,1650,1692,1702,1738,1768,1776,2606,2614,2650,2680,2702,2710,2732,2740,2776,2786,3132,3178,3228,3238,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4738 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4738 5 (fun x => (if x<2710 then (if x<1776 then (if x<1702 then (if x<1650 then 0 else (if x<1692 then 0 else 1)) else (if x<1738 then 0 else (if x<1768 then 1 else 0))) else (if x<2650 then (if x<2606 then 1 else (if x<2614 then 2 else 0)) else (if x<2680 then 2 else (if x<2702 then 0 else 1)))) else (if x<3178 then (if x<2776 then (if x<2732 then 2 else (if x<2740 then 0 else 1)) else (if x<2786 then 1 else (if x<3132 then 0 else 3))) else (if x<3282 then (if x<3228 then 2 else (if x<3238 then 4 else 2)) else (if x<3304 then 2 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4739 : Finset ℕ := ([68,136,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4739 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4739 68 5
  · have he : independentCachedBranchMembers4739.erase 68=independentCachedBranchMembers4737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4737
  · have he : independentCachedBranchMembers4739.filter (independentCachedEdge 68)=independentCachedBranchMembers4738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4738
def independentCachedBranchMembers4740 : Finset ℕ := ([1622,1644,1690,1692,1702,1748,1768,2606,2650,2652,2662,2710,2730,2732,2776,2786,2788,3158,3178,3226,3228,3238,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4740 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4740 5 (fun x => (if x<2730 then (if x<1768 then (if x<1692 then (if x<1644 then 0 else (if x<1690 then 0 else 1)) else (if x<1702 then 0 else (if x<1748 then 0 else 1))) else (if x<2652 then (if x<2606 then 1 else (if x<2650 then 2 else 2)) else (if x<2662 then 0 else (if x<2710 then 0 else 0)))) else (if x<3178 then (if x<2786 then (if x<2732 then 1 else (if x<2776 then 0 else 1)) else (if x<2788 then 2 else (if x<3158 then 1 else 3))) else (if x<3238 then (if x<3226 then 2 else (if x<3228 then 3 else 4)) else (if x<3282 then 2 else (if x<3304 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4741 : Finset ℕ := ([48,68,136,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4741 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4741 48 5
  · have he : independentCachedBranchMembers4741.erase 48=independentCachedBranchMembers4739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4739
  · have he : independentCachedBranchMembers4741.filter (independentCachedEdge 48)=independentCachedBranchMembers4740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4740
def independentCachedBranchMembers4742 : Finset ℕ := ([1596,1614,1622,1644,1692,1702,1748,2606,2614,2652,2662,2702,2710,2732,2740,2758,2788,3132,3150,3158,3188,3228,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4742 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4742 5 (fun x => (if x<2710 then (if x<1748 then (if x<1644 then (if x<1614 then 0 else (if x<1622 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 1 else 0))) else (if x<2652 then (if x<2606 then 0 else (if x<2614 then 0 else 2)) else (if x<2662 then 0 else (if x<2702 then 1 else 2)))) else (if x<3150 then (if x<2758 then (if x<2732 then 1 else (if x<2740 then 1 else 0)) else (if x<2788 then 0 else (if x<3132 then 2 else 3))) else (if x<3228 then (if x<3158 then 3 else (if x<3188 then 4 else 2)) else (if x<3238 then 4 else (if x<3276 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4743 : Finset ℕ := ([1614,1622,1702,2606,2614,2662,2702,2710,2758,3150,3158,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4743 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4743 4 (fun x => (if x<2702 then (if x<2606 then (if x<1622 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then 0 else (if x<2662 then 1 else 2))) else (if x<3150 then (if x<2710 then 2 else (if x<2758 then 3 else 0)) else (if x<3158 then 2 else (if x<3238 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4744 : Finset ℕ := ([252,1596,1614,1622,1644,1692,1702,1748,2606,2614,2652,2662,2702,2710,2732,2740,2758,2788,3132,3150,3158,3188,3228,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4744 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4744 252 4
  · have he : independentCachedBranchMembers4744.erase 252=independentCachedBranchMembers4742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4742
  · have he : independentCachedBranchMembers4744.filter (independentCachedEdge 252)=independentCachedBranchMembers4743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4743
def independentCachedBranchMembers4745 : Finset ℕ := ([1596,1692,1702,2606,2614,2702,2710,2732,2740,3132,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4745 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4745 4 (fun x => (if x<2710 then (if x<2606 then (if x<1692 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then 0 else (if x<2702 then 2 else 1))) else (if x<3132 then (if x<2732 then 3 else (if x<2740 then 2 else 0)) else (if x<3228 then 2 else (if x<3238 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4746 : Finset ℕ := ([68,252,1596,1614,1622,1644,1692,1702,1748,2606,2614,2652,2662,2702,2710,2732,2740,2758,2788,3132,3150,3158,3188,3228,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4746 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4746 68 4
  · have he : independentCachedBranchMembers4746.erase 68=independentCachedBranchMembers4744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4744
  · have he : independentCachedBranchMembers4746.filter (independentCachedEdge 68)=independentCachedBranchMembers4745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4745
def independentCachedBranchMembers4747 : Finset ℕ := ([48,68,136,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4747 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4747 250 5
  · have he : independentCachedBranchMembers4747.erase 250=independentCachedBranchMembers4741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4741
  · have he : independentCachedBranchMembers4747.filter (independentCachedEdge 250)=independentCachedBranchMembers4746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4746
def independentCachedBranchMembers4748 : Finset ℕ := ([1594,1596,1622,1650,1702,1738,1768,2614,2650,2652,2680,2702,2730,2732,2758,2786,2788,3130,3132,3158,3188,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4748 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4748 5 (fun x => (if x<2730 then (if x<1768 then (if x<1650 then (if x<1596 then 0 else (if x<1622 then 1 else 0)) else (if x<1702 then 1 else (if x<1738 then 0 else 0))) else (if x<2652 then (if x<2614 then 1 else (if x<2650 then 0 else 0)) else (if x<2680 then 2 else (if x<2702 then 1 else 2)))) else (if x<3132 then (if x<2786 then (if x<2732 then 0 else (if x<2758 then 1 else 0)) else (if x<2788 then 1 else (if x<3130 then 2 else 3))) else (if x<3238 then (if x<3158 then 4 else (if x<3188 then 3 else 2)) else (if x<3276 then 2 else (if x<3304 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4749 : Finset ℕ := ([1594,1596,1702,2650,2652,2680,2758,2786,2788,3130,3132,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4749 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4749 4 (fun x => (if x<2758 then (if x<2650 then (if x<1596 then 0 else (if x<1702 then 1 else 0)) else (if x<2652 then 0 else (if x<2680 then 1 else 2))) else (if x<3130 then (if x<2786 then 0 else (if x<2788 then 2 else 3)) else (if x<3132 then 3 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4750 : Finset ℕ := ([136,1594,1596,1622,1650,1702,1738,1768,2614,2650,2652,2680,2702,2730,2732,2758,2786,2788,3130,3132,3158,3188,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4750 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4750 136 4
  · have he : independentCachedBranchMembers4750.erase 136=independentCachedBranchMembers4748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4748
  · have he : independentCachedBranchMembers4750.filter (independentCachedEdge 136)=independentCachedBranchMembers4749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4749
def independentCachedBranchMembers4751 : Finset ℕ := ([1702,1768,2650,2652,2730,2732,2786,2788,3158,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4751 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4751 4 (fun x => (if x<2732 then (if x<2650 then (if x<1768 then 0 else 0) else (if x<2652 then 1 else (if x<2730 then 2 else 0))) else (if x<3158 then (if x<2786 then 2 else (if x<2788 then 1 else 0)) else (if x<3238 then 2 else (if x<3304 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4752 : Finset ℕ := ([1768,2786,2788,3158,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4752 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4752 3 (fun x => (if x<2788 then (if x<2786 then 0 else 0) else (if x<3158 then 1 else (if x<3238 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4753 : Finset ℕ := ([1622,1702,1768,2650,2652,2730,2732,2786,2788,3158,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4753 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4753 1622 3
  · have he : independentCachedBranchMembers4753.erase 1622=independentCachedBranchMembers4751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4751
  · have he : independentCachedBranchMembers4753.filter (independentCachedEdge 1622)=independentCachedBranchMembers4752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4752
def independentCachedBranchMembers4754 : Finset ℕ := ([48,136,1594,1596,1622,1650,1702,1738,1768,2614,2650,2652,2680,2702,2730,2732,2758,2786,2788,3130,3132,3158,3188,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4754 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4754 48 4
  · have he : independentCachedBranchMembers4754.erase 48=independentCachedBranchMembers4750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4750
  · have he : independentCachedBranchMembers4754.filter (independentCachedEdge 48)=independentCachedBranchMembers4753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4753
def independentCachedBranchMembers4755 : Finset ℕ := ([48,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4755 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4755 144 5
  · have he : independentCachedBranchMembers4755.erase 144=independentCachedBranchMembers4747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4747
  · have he : independentCachedBranchMembers4755.filter (independentCachedEdge 144)=independentCachedBranchMembers4754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4754
def independentCachedBranchMembers4756 : Finset ℕ := ([1594,1644,1690,1702,1748,1768,1776,2606,2614,2652,2680,2702,2710,2730,2738,2776,2788,3130,3188,3226,3238,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4756 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4756 5 (fun x => (if x<2710 then (if x<1776 then (if x<1702 then (if x<1644 then 0 else (if x<1690 then 0 else 1)) else (if x<1748 then 0 else (if x<1768 then 1 else 1))) else (if x<2652 then (if x<2606 then 0 else (if x<2614 then 0 else 2)) else (if x<2680 then 2 else (if x<2702 then 0 else 2)))) else (if x<3188 then (if x<2776 then (if x<2730 then 1 else (if x<2738 then 1 else 0)) else (if x<2788 then 1 else (if x<3130 then 0 else 3))) else (if x<3276 then (if x<3226 then 2 else (if x<3238 then 4 else 2)) else (if x<3304 then 2 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4757 : Finset ℕ := ([1594,1690,1702,2606,2614,2702,2710,2730,2738,3130,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4757 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4757 4 (fun x => (if x<2710 then (if x<2606 then (if x<1690 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then 0 else (if x<2702 then 2 else 1))) else (if x<3130 then (if x<2730 then 3 else (if x<2738 then 2 else 0)) else (if x<3226 then 2 else (if x<3238 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4758 : Finset ℕ := ([252,1594,1644,1690,1702,1748,1768,1776,2606,2614,2652,2680,2702,2710,2730,2738,2776,2788,3130,3188,3226,3238,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4758 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4758 252 4
  · have he : independentCachedBranchMembers4758.erase 252=independentCachedBranchMembers4756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4756
  · have he : independentCachedBranchMembers4758.filter (independentCachedEdge 252)=independentCachedBranchMembers4757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4757
def independentCachedBranchMembers4759 : Finset ℕ := ([1702,1768,1776,2606,2614,2680,2702,2710,2776,3238,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4759 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4759 4 (fun x => (if x<2702 then (if x<2606 then (if x<1768 then 0 else (if x<1776 then 0 else 1)) else (if x<2614 then 1 else (if x<2680 then 0 else 0))) else (if x<3238 then (if x<2710 then 2 else (if x<2776 then 3 else 2)) else (if x<3304 then 2 else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4760 : Finset ℕ := ([68,252,1594,1644,1690,1702,1748,1768,1776,2606,2614,2652,2680,2702,2710,2730,2738,2776,2788,3130,3188,3226,3238,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4760 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4760 68 4
  · have he : independentCachedBranchMembers4760.erase 68=independentCachedBranchMembers4758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4758
  · have he : independentCachedBranchMembers4760.filter (independentCachedEdge 68)=independentCachedBranchMembers4759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4759
def independentCachedBranchMembers4761 : Finset ℕ := ([48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4761 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4761 66 5
  · have he : independentCachedBranchMembers4761.erase 66=independentCachedBranchMembers4755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4755
  · have he : independentCachedBranchMembers4761.filter (independentCachedEdge 66)=independentCachedBranchMembers4760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4760
def independentCachedBranchMembers4762 : Finset ℕ := ([1614,1650,1690,1692,1702,1738,1776,2614,2650,2652,2662,2702,2738,2740,2776,2786,2788,3150,3188,3226,3228,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4762 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4762 5 (fun x => (if x<2738 then (if x<1776 then (if x<1692 then (if x<1650 then 0 else (if x<1690 then 0 else 0)) else (if x<1702 then 1 else (if x<1738 then 0 else 1))) else (if x<2652 then (if x<2614 then 1 else (if x<2650 then 2 else 0)) else (if x<2662 then 2 else (if x<2702 then 0 else 0)))) else (if x<3188 then (if x<2786 then (if x<2740 then 0 else (if x<2776 then 1 else 1)) else (if x<2788 then 1 else (if x<3150 then 2 else 3))) else (if x<3238 then (if x<3226 then 2 else (if x<3228 then 3 else 4)) else (if x<3276 then 2 else (if x<3312 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4763 : Finset ℕ := ([1702,1776,2650,2652,2738,2740,2786,2788,3150,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4763 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4763 4 (fun x => (if x<2740 then (if x<2650 then (if x<1776 then 0 else 0) else (if x<2652 then 1 else (if x<2738 then 2 else 0))) else (if x<3150 then (if x<2786 then 2 else (if x<2788 then 1 else 0)) else (if x<3238 then 2 else (if x<3312 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4764 : Finset ℕ := ([1776,2786,2788,3150,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4764 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4764 3 (fun x => (if x<2788 then (if x<2786 then 0 else 0) else (if x<3150 then 1 else (if x<3238 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4765 : Finset ℕ := ([1614,1702,1776,2650,2652,2738,2740,2786,2788,3150,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4765 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4765 1614 3
  · have he : independentCachedBranchMembers4765.erase 1614=independentCachedBranchMembers4763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4763
  · have he : independentCachedBranchMembers4765.filter (independentCachedEdge 1614)=independentCachedBranchMembers4764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4764
def independentCachedBranchMembers4766 : Finset ℕ := ([136,1614,1650,1690,1692,1702,1738,1776,2614,2650,2652,2662,2702,2738,2740,2776,2786,2788,3150,3188,3226,3228,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4766 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4766 136 4
  · have he : independentCachedBranchMembers4766.erase 136=independentCachedBranchMembers4762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4762
  · have he : independentCachedBranchMembers4766.filter (independentCachedEdge 136)=independentCachedBranchMembers4765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4765
def independentCachedBranchMembers4767 : Finset ℕ := ([1690,1692,1702,2650,2652,2662,2776,2786,2788,3226,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4767 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4767 4 (fun x => (if x<2776 then (if x<2650 then (if x<1692 then 0 else (if x<1702 then 1 else 0)) else (if x<2652 then 0 else (if x<2662 then 1 else 0))) else (if x<3226 then (if x<2786 then 2 else (if x<2788 then 2 else 3)) else (if x<3228 then 3 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
