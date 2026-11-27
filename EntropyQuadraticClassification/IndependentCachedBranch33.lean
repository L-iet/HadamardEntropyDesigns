/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch32
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3840 : Finset ℕ := ([12,40,130,144,1596,1614,1686,1746,2740,2758,2786,3132,3178,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3840 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3840 5 (fun x => (if x<1746 then (if x<144 then (if x<40 then 0 else (if x<130 then 1 else 0)) else (if x<1614 then (if x<1596 then 1 else 0) else (if x<1686 then 2 else 1))) else (if x<3132 then (if x<2758 then (if x<2740 then 2 else 3) else (if x<2786 then 2 else 0)) else (if x<3250 then (if x<3178 then 3 else 1) else (if x<3282 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3841 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2680,2738,2740,2758,2770,2786,2788,3102,3132,3178,3180,3250,3270,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3841 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3841 2788 5
  · have he : independentCachedBranchMembers3841.erase 2788=independentCachedBranchMembers3839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3839
  · have he : independentCachedBranchMembers3841.filter (independentCachedEdge 2788)=independentCachedBranchMembers3840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3840
def independentCachedBranchMembers3842 : Finset ℕ := ([12,192,1594,1596,1614,1686,1762,1776,2680,2738,2740,2758,2770,3132,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3842 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3842 5 (fun x => (if x<1776 then (if x<1596 then (if x<192 then 0 else (if x<1594 then 0 else 1)) else (if x<1686 then (if x<1614 then 0 else 1) else (if x<1762 then 1 else 1))) else (if x<2758 then (if x<2738 then (if x<2680 then 0 else 2) else (if x<2740 then 1 else 2)) else (if x<3132 then (if x<2770 then 1 else 0) else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3843 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2680,2710,2738,2740,2758,2770,2786,2788,3102,3132,3178,3180,3250,3270,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3843 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3843 2710 5
  · have he : independentCachedBranchMembers3843.erase 2710=independentCachedBranchMembers3841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3841
  · have he : independentCachedBranchMembers3843.filter (independentCachedEdge 2710)=independentCachedBranchMembers3842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3842
def independentCachedBranchMembers3844 : Finset ℕ := ([40,144,192,246,1594,1686,1746,1776,2680,2738,2786,3178,3270,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3844 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3844 5 (fun x => (if x<1776 then (if x<246 then (if x<144 then 0 else (if x<192 then 0 else 1)) else (if x<1686 then (if x<1594 then 1 else 2) else (if x<1746 then 0 else 1))) else (if x<3178 then (if x<2738 then (if x<2680 then 2 else 2) else (if x<2786 then 2 else 1)) else (if x<3282 then (if x<3270 then 0 else 1) else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3845 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2652,2680,2710,2738,2740,2758,2770,2786,2788,3102,3132,3178,3180,3250,3270,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3845 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3845 2652 5
  · have he : independentCachedBranchMembers3845.erase 2652=independentCachedBranchMembers3843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3843
  · have he : independentCachedBranchMembers3845.filter (independentCachedEdge 2652)=independentCachedBranchMembers3844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3844
def independentCachedBranchMembers3846 : Finset ℕ := ([12,40,130,144,1596,1614,1686,1746,2606,2652,2680,2710,2738,2770,2788,3102,3180,3270,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3846 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3846 5 (fun x => (if x<2680 then (if x<1614 then (if x<130 then (if x<40 then 0 else 1) else (if x<144 then 0 else (if x<1596 then 1 else 0))) else (if x<1746 then (if x<1686 then 2 else 1) else (if x<2606 then 2 else (if x<2652 then 2 else 0)))) else (if x<3102 then (if x<2738 then (if x<2710 then 3 else 4) else (if x<2770 then 2 else (if x<2788 then 0 else 3))) else (if x<3270 then (if x<3180 then 4 else 0) else (if x<3284 then 3 else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3847 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2652,2680,2710,2738,2740,2758,2770,2786,2788,3102,3132,3178,3180,3250,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3847 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3847 3300 5
  · have he : independentCachedBranchMembers3847.erase 3300=independentCachedBranchMembers3845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3845
  · have he : independentCachedBranchMembers3847.filter (independentCachedEdge 3300)=independentCachedBranchMembers3846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3846
def independentCachedBranchMembers3848 : Finset ℕ := ([12,144,192,246,1614,1746,1748,1762,2606,2680,2738,2740,2770,2786,2788,3132,3178,3180,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3848 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3848 5 (fun x => (if x<2738 then (if x<1746 then (if x<192 then (if x<144 then 0 else 0) else (if x<246 then 1 else (if x<1614 then 1 else 0))) else (if x<1762 then (if x<1748 then 0 else 1) else (if x<2606 then 1 else (if x<2680 then 0 else 2)))) else (if x<3132 then (if x<2770 then (if x<2740 then 0 else 2) else (if x<2786 then 1 else (if x<2788 then 2 else 1))) else (if x<3180 then (if x<3178 then 2 else 2) else (if x<3270 then 0 else (if x<3312 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3849 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2652,2680,2710,2738,2740,2758,2770,2786,2788,3102,3132,3178,3180,3192,3250,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3849 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3849 3192 5
  · have he : independentCachedBranchMembers3849.erase 3192=independentCachedBranchMembers3847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3847
  · have he : independentCachedBranchMembers3849.filter (independentCachedEdge 3192)=independentCachedBranchMembers3848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3848
def independentCachedBranchMembers3850 : Finset ℕ := ([130,246,1686,1762,2606,2652,2680,2710,2738,2740,2758,2786,2788,3102,3132,3178,3180,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3850 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3850 5 (fun x => (if x<2758 then (if x<2652 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1762 then 0 else (if x<2606 then 0 else 1))) else (if x<2710 then (if x<2680 then 1 else 2) else (if x<2738 then 1 else (if x<2740 then 0 else 2)))) else (if x<3178 then (if x<2788 then (if x<2786 then 0 else 2) else (if x<3102 then 1 else (if x<3132 then 1 else 2))) else (if x<3282 then (if x<3180 then 2 else 1) else (if x<3284 then 0 else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3851 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2652,2680,2710,2738,2740,2758,2770,2786,2788,3102,3118,3132,3178,3180,3192,3250,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3851 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3851 3118 5
  · have he : independentCachedBranchMembers3851.erase 3118=independentCachedBranchMembers3849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3849
  · have he : independentCachedBranchMembers3851.filter (independentCachedEdge 3118)=independentCachedBranchMembers3850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3850
def independentCachedBranchMembers3852 : Finset ℕ := ([40,130,1594,1596,1644,1686,1702,1776,2606,2680,2738,2740,2770,2786,2788,3132,3178,3180,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3852 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3852 5 (fun x => (if x<2738 then (if x<1686 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1596 then 1 else (if x<1644 then 0 else 1))) else (if x<1776 then (if x<1702 then 0 else 1) else (if x<2606 then 1 else (if x<2680 then 1 else 0)))) else (if x<3132 then (if x<2770 then (if x<2740 then 1 else 2) else (if x<2786 then 0 else (if x<2788 then 2 else 1))) else (if x<3180 then (if x<3178 then 2 else 2) else (if x<3270 then 0 else (if x<3312 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3853 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2652,2680,2710,2738,2740,2758,2770,2786,2788,2800,3102,3118,3132,3178,3180,3192,3250,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3853 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3853 2800 5
  · have he : independentCachedBranchMembers3853.erase 2800=independentCachedBranchMembers3851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3851
  · have he : independentCachedBranchMembers3853.filter (independentCachedEdge 2800)=independentCachedBranchMembers3852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3852
def independentCachedBranchMembers3854 : Finset ℕ := ([192,246,1594,1644,1702,1748,1762,1776,2606,2652,2680,2710,2738,2770,2788,3102,3180,3270,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3854 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3854 5 (fun x => (if x<2680 then (if x<1748 then (if x<1594 then (if x<246 then 0 else 0) else (if x<1644 then 1 else (if x<1702 then 1 else 1))) else (if x<1776 then (if x<1762 then 0 else 0) else (if x<2606 then 1 else (if x<2652 then 1 else 2)))) else (if x<3102 then (if x<2738 then (if x<2710 then 1 else 2) else (if x<2770 then 1 else (if x<2788 then 0 else 0))) else (if x<3270 then (if x<3180 then 2 else 2) else (if x<3284 then 0 else (if x<3312 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3855 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2652,2668,2680,2710,2738,2740,2758,2770,2786,2788,2800,3102,3118,3132,3178,3180,3192,3250,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3855 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3855 2668 5
  · have he : independentCachedBranchMembers3855.erase 2668=independentCachedBranchMembers3853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3853
  · have he : independentCachedBranchMembers3855.filter (independentCachedEdge 2668)=independentCachedBranchMembers3854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3854
def independentCachedBranchMembers3856 : Finset ℕ := ([12,40,130,192,1594,1644,1746,1762,2606,2652,2668,2680,2740,2758,2770,2786,3132,3178,3250,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3856 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3856 5 (fun x => (if x<2680 then (if x<1644 then (if x<130 then (if x<40 then 0 else 1) else (if x<192 then 0 else (if x<1594 then 1 else 1))) else (if x<2606 then (if x<1746 then 0 else (if x<1762 then 1 else 0)) else (if x<2652 then 1 else (if x<2668 then 0 else 2)))) else (if x<3132 then (if x<2758 then (if x<2740 then 3 else 2) else (if x<2770 then 1 else (if x<2786 then 0 else 2))) else (if x<3284 then (if x<3178 then 0 else (if x<3250 then 2 else 0)) else (if x<3300 then 1 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3857 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2652,2668,2680,2710,2738,2740,2758,2770,2786,2788,2800,3102,3118,3132,3178,3180,3192,3250,3252,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3857 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3857 3252 5
  · have he : independentCachedBranchMembers3857.erase 3252=independentCachedBranchMembers3855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3855
  · have he : independentCachedBranchMembers3857.filter (independentCachedEdge 3252)=independentCachedBranchMembers3856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3856
def independentCachedBranchMembers3858 : Finset ℕ := ([40,144,192,246,1594,1686,1746,1776,2606,2652,2710,2740,2758,2770,2788,2800,3102,3132,3180,3192,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3858 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3858 5 (fun x => (if x<2740 then (if x<1686 then (if x<192 then (if x<144 then 0 else 0) else (if x<246 then 1 else (if x<1594 then 1 else 2))) else (if x<2606 then (if x<1746 then 0 else (if x<1776 then 1 else 2)) else (if x<2652 then 2 else (if x<2710 then 3 else 3)))) else (if x<3102 then (if x<2770 then (if x<2758 then 4 else 1) else (if x<2788 then 0 else (if x<2800 then 2 else 1))) else (if x<3192 then (if x<3132 then 2 else (if x<3180 then 4 else 0)) else (if x<3250 then 3 else (if x<3284 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3859 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2652,2668,2680,2710,2738,2740,2758,2770,2786,2788,2800,3102,3118,3132,3164,3178,3180,3192,3250,3252,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3859 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3859 3164 5
  · have he : independentCachedBranchMembers3859.erase 3164=independentCachedBranchMembers3857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3857
  · have he : independentCachedBranchMembers3859.filter (independentCachedEdge 3164)=independentCachedBranchMembers3858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3858
def independentCachedBranchMembers3860 : Finset ℕ := ([12,130,1596,1614,1644,1702,1748,1762,2606,2652,2710,2740,2758,2770,2788,2800,3102,3132,3180,3192,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3860 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3860 5 (fun x => (if x<2740 then (if x<1702 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1614 then 0 else (if x<1644 then 1 else 2))) else (if x<2606 then (if x<1748 then 1 else (if x<1762 then 1 else 2)) else (if x<2652 then 1 else (if x<2710 then 0 else 3)))) else (if x<3102 then (if x<2770 then (if x<2758 then 1 else 1) else (if x<2788 then 0 else (if x<2800 then 2 else 3))) else (if x<3192 then (if x<3132 then 3 else (if x<3180 then 4 else 0)) else (if x<3250 then 3 else (if x<3284 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3861 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3132,3164,3178,3180,3192,3250,3252,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3861 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3861 2772 5
  · have he : independentCachedBranchMembers3861.erase 2772=independentCachedBranchMembers3859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3859
  · have he : independentCachedBranchMembers3861.filter (independentCachedEdge 2772)=independentCachedBranchMembers3860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3860
def independentCachedBranchMembers3862 : Finset ℕ := ([144,246,1596,1614,1686,1702,1748,1776,2606,2652,2668,2680,2740,2758,2770,2786,3132,3178,3250,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3862 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3862 5 (fun x => (if x<2680 then (if x<1702 then (if x<1596 then (if x<246 then 0 else 0) else (if x<1614 then 1 else (if x<1686 then 1 else 0))) else (if x<2606 then (if x<1748 then 1 else (if x<1776 then 1 else 0)) else (if x<2652 then 1 else (if x<2668 then 1 else 2)))) else (if x<3132 then (if x<2758 then (if x<2740 then 3 else 0) else (if x<2770 then 1 else (if x<2786 then 0 else 2))) else (if x<3284 then (if x<3178 then 2 else (if x<3250 then 2 else 0)) else (if x<3300 then 0 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3863 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2620,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3132,3164,3178,3180,3192,3250,3252,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3863 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3863 2620 5
  · have he : independentCachedBranchMembers3863.erase 2620=independentCachedBranchMembers3861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3861
  · have he : independentCachedBranchMembers3863.filter (independentCachedEdge 2620)=independentCachedBranchMembers3862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3862
def independentCachedBranchMembers3864 : Finset ℕ := ([40,144,1594,1614,1644,1686,1748,1762,2606,2668,2680,2710,2740,2772,2786,3102,3132,3164,3178,3250,3270,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3864 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3864 5 (fun x => (if x<2740 then (if x<1748 then (if x<1614 then (if x<144 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 1 else (if x<1686 then 0 else 1))) else (if x<2668 then (if x<1762 then 0 else (if x<2606 then 1 else 0)) else (if x<2680 then 2 else (if x<2710 then 3 else 0)))) else (if x<3178 then (if x<3102 then (if x<2772 then 2 else (if x<2786 then 3 else 2)) else (if x<3132 then 1 else (if x<3164 then 2 else 3))) else (if x<3282 then (if x<3250 then 0 else (if x<3270 then 1 else 1)) else (if x<3300 then 0 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3865 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2620,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3132,3164,3178,3180,3192,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3865 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3865 3298 5
  · have he : independentCachedBranchMembers3865.erase 3298=independentCachedBranchMembers3863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3863
  · have he : independentCachedBranchMembers3865.filter (independentCachedEdge 3298)=independentCachedBranchMembers3864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3864
def independentCachedBranchMembers3866 : Finset ℕ := ([12,192,1594,1596,1614,1686,1762,1776,2606,2620,2652,2710,2786,2788,2800,3102,3178,3180,3192,3250,3252,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3866 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3866 5 (fun x => (if x<2786 then (if x<1762 then (if x<1596 then (if x<192 then 0 else (if x<1594 then 0 else 1)) else (if x<1614 then 0 else (if x<1686 then 1 else 1))) else (if x<2620 then (if x<1776 then 1 else (if x<2606 then 0 else 0)) else (if x<2652 then 2 else (if x<2710 then 3 else 2)))) else (if x<3192 then (if x<3102 then (if x<2788 then 0 else (if x<2800 then 2 else 3)) else (if x<3178 then 0 else (if x<3180 then 1 else 2))) else (if x<3270 then (if x<3250 then 3 else (if x<3252 then 1 else 2)) else (if x<3282 then 1 else (if x<3284 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3867 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2620,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3132,3164,3178,3180,3192,3222,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3867 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3867 3222 5
  · have he : independentCachedBranchMembers3867.erase 3222=independentCachedBranchMembers3865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3865
  · have he : independentCachedBranchMembers3867.filter (independentCachedEdge 3222)=independentCachedBranchMembers3866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3866
def independentCachedBranchMembers3868 : Finset ℕ := ([12,40,144,192,1594,1596,1614,1644,1702,1746,1748,1776,2620,2668,2772,2800,3118,3164,3192,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3868 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3868 5 (fun x => (if x<2620 then (if x<1614 then (if x<192 then (if x<40 then 0 else (if x<144 then 1 else 0)) else (if x<1594 then 1 else (if x<1596 then 1 else 2))) else (if x<1746 then (if x<1644 then 0 else (if x<1702 then 3 else 2)) else (if x<1748 then 0 else (if x<1776 then 2 else 3)))) else (if x<3192 then (if x<2800 then (if x<2668 then 1 else (if x<2772 then 0 else 1)) else (if x<3118 then 0 else (if x<3164 then 0 else 2))) else (if x<3252 then (if x<3222 then 3 else (if x<3250 then 4 else 0)) else (if x<3298 then (if x<3270 then 2 else 1) else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3869 : Finset ℕ := ([1594,1614,1702,1746,2620,2668,2772,2800,3164,3192,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3869 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3869 4 (fun x => (if x<2772 then (if x<1746 then (if x<1614 then 0 else (if x<1702 then 0 else 0)) else (if x<2620 then 0 else (if x<2668 then 1 else 2))) else (if x<3192 then (if x<2800 then 1 else (if x<3164 then 2 else 1)) else (if x<3252 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3870 : Finset ℕ := ([12,40,144,192,1594,1596,1614,1644,1702,1746,1748,1776,2620,2668,2770,2772,2800,3118,3164,3192,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3870 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3870 2770 4
  · have he : independentCachedBranchMembers3870.erase 2770=independentCachedBranchMembers3868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3868
  · have he : independentCachedBranchMembers3870.filter (independentCachedEdge 2770)=independentCachedBranchMembers3869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3869
def independentCachedBranchMembers3871 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1746,1748,1762,1776,2606,2620,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3132,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3871 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3871 3238 5
  · have he : independentCachedBranchMembers3871.erase 3238=independentCachedBranchMembers3867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3867
  · have he : independentCachedBranchMembers3871.filter (independentCachedEdge 3238)=independentCachedBranchMembers3870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3870
end EntropyDesigns.QuadraticRefinement
