/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch61
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4768 : Finset ℕ := ([48,136,1614,1650,1690,1692,1702,1738,1776,2614,2650,2652,2662,2702,2738,2740,2776,2786,2788,3150,3188,3226,3228,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4768 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4768 48 4
  · have he : independentCachedBranchMembers4768.erase 48=independentCachedBranchMembers4766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4766
  · have he : independentCachedBranchMembers4768.filter (independentCachedEdge 48)=independentCachedBranchMembers4767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4767
def independentCachedBranchMembers4769 : Finset ℕ := ([40,48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4769 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4769 40 5
  · have he : independentCachedBranchMembers4769.erase 40=independentCachedBranchMembers4761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4761
  · have he : independentCachedBranchMembers4769.filter (independentCachedEdge 40)=independentCachedBranchMembers4768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4768
def independentCachedBranchMembers4770 : Finset ℕ := ([1596,1614,1650,1690,1702,1738,1748,1768,2614,2650,2662,2680,2702,2732,2738,2786,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4770 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4770 5 (fun x => (if x<2702 then (if x<1748 then (if x<1690 then (if x<1614 then 0 else (if x<1650 then 0 else 0)) else (if x<1702 then 0 else (if x<1738 then 0 else 1))) else (if x<2650 then (if x<1768 then 0 else (if x<2614 then 0 else 1)) else (if x<2662 then 1 else (if x<2680 then 2 else 2)))) else (if x<3178 then (if x<2786 then (if x<2732 then 1 else (if x<2738 then 2 else 2)) else (if x<3130 then 1 else (if x<3158 then 3 else 3))) else (if x<3276 then (if x<3188 then 4 else (if x<3228 then 4 else 3)) else (if x<3282 then 4 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4771 : Finset ℕ := ([1596,1614,1690,1768,2614,2650,2702,2786,3178,3188,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4771 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4771 4 (fun x => (if x<2702 then (if x<1768 then (if x<1614 then 0 else (if x<1690 then 0 else 0)) else (if x<2614 then 0 else (if x<2650 then 1 else 1))) else (if x<3188 then (if x<2786 then 1 else (if x<3178 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4772 : Finset ℕ := ([1596,1614,1650,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2702,2732,2738,2786,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4772 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4772 1720 4
  · have he : independentCachedBranchMembers4772.erase 1720=independentCachedBranchMembers4770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4770
  · have he : independentCachedBranchMembers4772.filter (independentCachedEdge 1720)=independentCachedBranchMembers4771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4771
def independentCachedBranchMembers4773 : Finset ℕ := ([1596,1614,1702,1748,2614,2662,2702,2732,3158,3188,3228,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4773 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4773 4 (fun x => (if x<2702 then (if x<1748 then (if x<1614 then 0 else (if x<1702 then 0 else 0)) else (if x<2614 then 0 else (if x<2662 then 1 else 2))) else (if x<3188 then (if x<2732 then 1 else (if x<3158 then 2 else 2)) else (if x<3228 then 1 else (if x<3276 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4774 : Finset ℕ := ([250,1596,1614,1650,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2702,2732,2738,2786,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4774 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4774 250 4
  · have he : independentCachedBranchMembers4774.erase 250=independentCachedBranchMembers4772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4772
  · have he : independentCachedBranchMembers4774.filter (independentCachedEdge 250)=independentCachedBranchMembers4773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4773
def independentCachedBranchMembers4775 : Finset ℕ := ([1596,1614,1702,1748,2650,2680,2738,2786,3130,3178,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4775 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4775 4 (fun x => (if x<2738 then (if x<1748 then (if x<1614 then 0 else (if x<1702 then 0 else 0)) else (if x<2650 then 0 else (if x<2680 then 1 else 2))) else (if x<3178 then (if x<2786 then 1 else (if x<3130 then 2 else 1)) else (if x<3282 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4776 : Finset ℕ := ([136,250,1596,1614,1650,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2702,2732,2738,2786,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4776 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4776 136 4
  · have he : independentCachedBranchMembers4776.erase 136=independentCachedBranchMembers4774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4774
  · have he : independentCachedBranchMembers4776.filter (independentCachedEdge 136)=independentCachedBranchMembers4775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4775
def independentCachedBranchMembers4777 : Finset ℕ := ([1690,1702,1748,1768,2614,2680,2702,2738,3130,3188,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4777 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4777 4 (fun x => (if x<2702 then (if x<1768 then (if x<1702 then 0 else (if x<1748 then 0 else 0)) else (if x<2614 then 0 else (if x<2680 then 1 else 1))) else (if x<3188 then (if x<2738 then 2 else (if x<3130 then 2 else 1)) else (if x<3276 then 1 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4778 : Finset ℕ := ([66,136,250,1596,1614,1650,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2702,2732,2738,2786,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4778 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4778 66 4
  · have he : independentCachedBranchMembers4778.erase 66=independentCachedBranchMembers4776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4776
  · have he : independentCachedBranchMembers4778.filter (independentCachedEdge 66)=independentCachedBranchMembers4777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4777
def independentCachedBranchMembers4779 : Finset ℕ := ([1690,1702,1748,1768,2650,2662,2732,2786,3158,3178,3228,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4779 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4779 4 (fun x => (if x<2732 then (if x<1768 then (if x<1702 then 0 else (if x<1748 then 0 else 0)) else (if x<2650 then 0 else (if x<2662 then 1 else 1))) else (if x<3178 then (if x<2786 then 2 else (if x<3158 then 2 else 1)) else (if x<3228 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4780 : Finset ℕ := ([48,66,136,250,1596,1614,1650,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2702,2732,2738,2786,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4780 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4780 48 4
  · have he : independentCachedBranchMembers4780.erase 48=independentCachedBranchMembers4778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4778
  · have he : independentCachedBranchMembers4780.filter (independentCachedEdge 48)=independentCachedBranchMembers4779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4779
def independentCachedBranchMembers4781 : Finset ℕ := ([48,66,136,250,1596,1614,1690,1768,2614,2650,2702,2786,3130,3158,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4781 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4781 4 (fun x => (if x<2614 then (if x<1596 then (if x<136 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1614 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3130 then (if x<2702 then (if x<2650 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3228 then (if x<3158 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4782 : Finset ℕ := ([48,66,136,250,1596,1614,1644,1650,1690,1702,1720,1738,1748,1768,2614,2650,2662,2680,2702,2732,2738,2786,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4782 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4782 1644 4
  · have he : independentCachedBranchMembers4782.erase 1644=independentCachedBranchMembers4780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4780
  · have he : independentCachedBranchMembers4782.filter (independentCachedEdge 1644)=independentCachedBranchMembers4781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4781
def independentCachedBranchMembers4783 : Finset ℕ := ([40,48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4783 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4783 3284 5
  · have he : independentCachedBranchMembers4783.erase 3284=independentCachedBranchMembers4769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4769
  · have he : independentCachedBranchMembers4783.filter (independentCachedEdge 3284)=independentCachedBranchMembers4782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4782
def independentCachedBranchMembers4784 : Finset ℕ := ([1594,1622,1644,1692,1702,1738,1748,1776,2606,2652,2662,2680,2710,2732,2738,2788,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4784 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4784 5 (fun x => (if x<2710 then (if x<1748 then (if x<1692 then (if x<1622 then 0 else (if x<1644 then 0 else 0)) else (if x<1702 then 0 else (if x<1738 then 0 else 0))) else (if x<2652 then (if x<1776 then 1 else (if x<2606 then 0 else 1)) else (if x<2662 then 1 else (if x<2680 then 2 else 2)))) else (if x<3178 then (if x<2788 then (if x<2732 then 1 else (if x<2738 then 2 else 2)) else (if x<3132 then 1 else (if x<3150 then 3 else 3))) else (if x<3276 then (if x<3188 then 4 else (if x<3226 then 4 else 3)) else (if x<3282 then 4 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4785 : Finset ℕ := ([1594,1622,1692,1776,2606,2652,2710,2788,3178,3188,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4785 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4785 4 (fun x => (if x<2710 then (if x<1776 then (if x<1622 then 0 else (if x<1692 then 0 else 0)) else (if x<2606 then 0 else (if x<2652 then 1 else 1))) else (if x<3188 then (if x<2788 then 1 else (if x<3178 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4786 : Finset ℕ := ([1594,1622,1644,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2710,2732,2738,2788,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4786 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4786 1720 4
  · have he : independentCachedBranchMembers4786.erase 1720=independentCachedBranchMembers4784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4784
  · have he : independentCachedBranchMembers4786.filter (independentCachedEdge 1720)=independentCachedBranchMembers4785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4785
def independentCachedBranchMembers4787 : Finset ℕ := ([1594,1622,1702,1738,2606,2662,2710,2738,3150,3178,3226,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4787 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4787 4 (fun x => (if x<2710 then (if x<1738 then (if x<1622 then 0 else (if x<1702 then 0 else 0)) else (if x<2606 then 0 else (if x<2662 then 1 else 2))) else (if x<3178 then (if x<2738 then 1 else (if x<3150 then 2 else 2)) else (if x<3226 then 1 else (if x<3282 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4788 : Finset ℕ := ([252,1594,1622,1644,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2710,2732,2738,2788,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4788 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4788 252 4
  · have he : independentCachedBranchMembers4788.erase 252=independentCachedBranchMembers4786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4786
  · have he : independentCachedBranchMembers4788.filter (independentCachedEdge 252)=independentCachedBranchMembers4787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4787
def independentCachedBranchMembers4789 : Finset ℕ := ([1594,1622,1702,1738,2652,2680,2732,2788,3132,3188,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4789 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4789 4 (fun x => (if x<2732 then (if x<1738 then (if x<1622 then 0 else (if x<1702 then 0 else 0)) else (if x<2652 then 0 else (if x<2680 then 1 else 2))) else (if x<3188 then (if x<2788 then 1 else (if x<3132 then 2 else 1)) else (if x<3276 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4790 : Finset ℕ := ([144,252,1594,1622,1644,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2710,2732,2738,2788,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4790 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4790 144 4
  · have he : independentCachedBranchMembers4790.erase 144=independentCachedBranchMembers4788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4788
  · have he : independentCachedBranchMembers4790.filter (independentCachedEdge 144)=independentCachedBranchMembers4789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4789
def independentCachedBranchMembers4791 : Finset ℕ := ([1692,1702,1738,1776,2606,2680,2710,2732,3132,3178,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4791 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4791 4 (fun x => (if x<2710 then (if x<1776 then (if x<1702 then 0 else (if x<1738 then 0 else 0)) else (if x<2606 then 0 else (if x<2680 then 1 else 1))) else (if x<3178 then (if x<2732 then 2 else (if x<3132 then 2 else 1)) else (if x<3282 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4792 : Finset ℕ := ([68,144,252,1594,1622,1644,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2710,2732,2738,2788,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4792 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4792 68 4
  · have he : independentCachedBranchMembers4792.erase 68=independentCachedBranchMembers4790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4790
  · have he : independentCachedBranchMembers4792.filter (independentCachedEdge 68)=independentCachedBranchMembers4791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4791
def independentCachedBranchMembers4793 : Finset ℕ := ([1692,1702,1738,1776,2652,2662,2738,2788,3150,3188,3226,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4793 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4793 4 (fun x => (if x<2738 then (if x<1776 then (if x<1702 then 0 else (if x<1738 then 0 else 0)) else (if x<2652 then 0 else (if x<2662 then 1 else 1))) else (if x<3188 then (if x<2788 then 2 else (if x<3150 then 2 else 1)) else (if x<3226 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4794 : Finset ℕ := ([40,68,144,252,1594,1622,1644,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2710,2732,2738,2788,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4794 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4794 40 4
  · have he : independentCachedBranchMembers4794.erase 40=independentCachedBranchMembers4792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4792
  · have he : independentCachedBranchMembers4794.filter (independentCachedEdge 40)=independentCachedBranchMembers4793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4793
def independentCachedBranchMembers4795 : Finset ℕ := ([40,68,144,252,1594,1622,1692,1776,2606,2652,2710,2788,3132,3150,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4795 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4795 4 (fun x => (if x<2606 then (if x<1594 then (if x<144 then (if x<68 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1622 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3132 then (if x<2710 then (if x<2652 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3226 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4796 : Finset ℕ := ([40,68,144,252,1594,1622,1644,1650,1692,1702,1720,1738,1748,1776,2606,2652,2662,2680,2710,2732,2738,2788,3132,3150,3178,3188,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4796 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4796 1650 4
  · have he : independentCachedBranchMembers4796.erase 1650=independentCachedBranchMembers4794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4794
  · have he : independentCachedBranchMembers4796.filter (independentCachedEdge 1650)=independentCachedBranchMembers4795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4795
def independentCachedBranchMembers4797 : Finset ℕ := ([40,48,66,68,136,144,250,252,1594,1596,1614,1622,1644,1650,1690,1692,1702,1720,1738,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3130,3132,3150,3158,3178,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4797 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4797 3274 5
  · have he : independentCachedBranchMembers4797.erase 3274=independentCachedBranchMembers4783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4783
  · have he : independentCachedBranchMembers4797.filter (independentCachedEdge 3274)=independentCachedBranchMembers4796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4796
def independentCachedBranchMembers4798 : Finset ℕ := ([1596,1614,1650,1690,1702,1720,1748,1768,2606,2652,2710,2730,2740,2758,2776,2788,3130,3158,3178,3188,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4798 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4798 5 (fun x => (if x<2740 then (if x<1748 then (if x<1690 then (if x<1614 then 0 else (if x<1650 then 0 else 0)) else (if x<1702 then 0 else (if x<1720 then 0 else 1))) else (if x<2652 then (if x<1768 then 0 else (if x<2606 then 0 else 2)) else (if x<2710 then 2 else (if x<2730 then 2 else 1)))) else (if x<3178 then (if x<2788 then (if x<2758 then 1 else (if x<2776 then 1 else 1)) else (if x<3130 then 2 else (if x<3158 then 3 else 3))) else (if x<3276 then (if x<3188 then 4 else (if x<3228 then 4 else 3)) else (if x<3282 then 4 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4799 : Finset ℕ := ([1596,1614,1690,1768,2730,2740,2758,2776,3130,3158,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4799 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4799 4 (fun x => (if x<2758 then (if x<1768 then (if x<1614 then 0 else (if x<1690 then 0 else 0)) else (if x<2730 then 0 else (if x<2740 then 1 else 1))) else (if x<3158 then (if x<2776 then 1 else (if x<3130 then 1 else 2)) else (if x<3228 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
