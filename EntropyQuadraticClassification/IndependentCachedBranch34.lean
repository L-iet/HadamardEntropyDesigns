/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch33
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3872 : Finset ℕ := ([12,144,1596,1614,1686,1702,1746,1748,1762,2606,2668,2738,2740,2758,2800,3102,3118,3164,3178,3180,3250,3252,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3872 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3872 5 (fun x => (if x<2740 then (if x<1746 then (if x<1614 then (if x<144 then 0 else (if x<1596 then 0 else 1)) else (if x<1686 then 0 else (if x<1702 then 1 else 2))) else (if x<2606 then (if x<1748 then 0 else (if x<1762 then 2 else 3)) else (if x<2668 then 0 else (if x<2738 then 1 else 0)))) else (if x<3178 then (if x<3102 then (if x<2758 then 1 else (if x<2800 then 1 else 3)) else (if x<3118 then 3 else (if x<3164 then 2 else 2))) else (if x<3252 then (if x<3180 then 4 else (if x<3250 then 0 else 3)) else (if x<3270 then 2 else (if x<3312 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3873 : Finset ℕ := ([144,1686,1746,2668,2738,3118,3164,3178,3252,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3873 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3873 4 (fun x => (if x<3118 then (if x<1746 then (if x<1686 then 0 else 0) else (if x<2668 then 1 else (if x<2738 then 0 else 1))) else (if x<3252 then (if x<3164 then 2 else (if x<3178 then 2 else 0)) else (if x<3270 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3874 : Finset ℕ := ([12,144,1596,1614,1686,1702,1746,1748,1762,2606,2652,2668,2738,2740,2758,2800,3102,3118,3164,3178,3180,3250,3252,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3874 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3874 2652 4
  · have he : independentCachedBranchMembers3874.erase 2652=independentCachedBranchMembers3872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3872
  · have he : independentCachedBranchMembers3874.filter (independentCachedEdge 2652)=independentCachedBranchMembers3873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3873
def independentCachedBranchMembers3875 : Finset ℕ := ([12,144,1596,1748,2652,2668,2740,2800,3164,3180,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3875 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3875 4 (fun x => (if x<2740 then (if x<1748 then (if x<144 then 0 else (if x<1596 then 0 else 1)) else (if x<2652 then 1 else (if x<2668 then 1 else 0))) else (if x<3180 then (if x<2800 then 1 else (if x<3164 then 0 else 2)) else (if x<3252 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3876 : Finset ℕ := ([12,144,1594,1596,1614,1686,1702,1746,1748,1762,2606,2652,2668,2738,2740,2758,2800,3102,3118,3164,3178,3180,3250,3252,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3876 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3876 1594 4
  · have he : independentCachedBranchMembers3876.erase 1594=independentCachedBranchMembers3874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3874
  · have he : independentCachedBranchMembers3876.filter (independentCachedEdge 1594)=independentCachedBranchMembers3875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3875
def independentCachedBranchMembers3877 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1734,1746,1748,1762,1776,2606,2620,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3132,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3877 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3877 1734 5
  · have he : independentCachedBranchMembers3877.erase 1734=independentCachedBranchMembers3871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3871
  · have he : independentCachedBranchMembers3877.filter (independentCachedEdge 1734)=independentCachedBranchMembers3876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3876
def independentCachedBranchMembers3878 : Finset ℕ := ([40,192,1594,1644,1686,1702,1746,1762,1776,2606,2620,2680,2738,2758,2772,2788,3102,3118,3132,3178,3192,3250,3270,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3878 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3878 5 (fun x => (if x<2738 then (if x<1746 then (if x<1644 then (if x<192 then 0 else (if x<1594 then 0 else 0)) else (if x<1686 then 1 else (if x<1702 then 2 else 1))) else (if x<2606 then (if x<1762 then 0 else (if x<1776 then 2 else 1)) else (if x<2620 then 0 else (if x<2680 then 3 else 1)))) else (if x<3132 then (if x<2788 then (if x<2758 then 1 else (if x<2772 then 0 else 3)) else (if x<3102 then 1 else (if x<3118 then 2 else 3))) else (if x<3250 then (if x<3178 then 0 else (if x<3192 then 2 else 4)) else (if x<3284 then (if x<3270 then 2 else 2) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3879 : Finset ℕ := ([40,192,1644,1776,2620,2680,2772,2788,3132,3192,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3879 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3879 4 (fun x => (if x<2772 then (if x<1776 then (if x<192 then 0 else (if x<1644 then 0 else 1)) else (if x<2620 then 1 else (if x<2680 then 0 else 1))) else (if x<3192 then (if x<2788 then 0 else (if x<3132 then 1 else 2)) else (if x<3284 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3880 : Finset ℕ := ([40,192,1594,1614,1644,1686,1702,1746,1762,1776,2606,2620,2680,2738,2758,2772,2788,3102,3118,3132,3178,3192,3250,3270,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3880 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3880 1614 4
  · have he : independentCachedBranchMembers3880.erase 1614=independentCachedBranchMembers3878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3878
  · have he : independentCachedBranchMembers3880.filter (independentCachedEdge 1614)=independentCachedBranchMembers3879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3879
def independentCachedBranchMembers3881 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1644,1686,1702,1714,1734,1746,1748,1762,1776,2606,2620,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3132,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3881 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3881 1714 5
  · have he : independentCachedBranchMembers3881.erase 1714=independentCachedBranchMembers3877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3877
  · have he : independentCachedBranchMembers3881.filter (independentCachedEdge 1714)=independentCachedBranchMembers3880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3880
def independentCachedBranchMembers3882 : Finset ℕ := ([12,130,192,246,1594,1614,1644,1686,1748,1762,2620,2652,2738,2758,2770,2788,2800,3102,3132,3164,3178,3238,3250,3270,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3882 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3882 5 (fun x => (if x<2758 then (if x<1644 then (if x<246 then (if x<130 then 0 else (if x<192 then 0 else 1)) else (if x<1594 then 1 else (if x<1614 then 2 else 2))) else (if x<1762 then (if x<1686 then 0 else (if x<1748 then 2 else 1)) else (if x<2652 then (if x<2620 then 0 else 0) else (if x<2738 then 3 else 0)))) else (if x<3178 then (if x<2800 then (if x<2770 then 1 else (if x<2788 then 3 else 3)) else (if x<3132 then (if x<3102 then 1 else 2) else (if x<3164 then 4 else 0))) else (if x<3270 then (if x<3238 then 2 else (if x<3250 then 4 else 2)) else (if x<3300 then (if x<3282 then 2 else 0) else (if x<3312 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3883 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1642,1644,1686,1702,1714,1734,1746,1748,1762,1776,2606,2620,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3132,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3883 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3883 1642 5
  · have he : independentCachedBranchMembers3883.erase 1642=independentCachedBranchMembers3881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3881
  · have he : independentCachedBranchMembers3883.filter (independentCachedEdge 1642)=independentCachedBranchMembers3882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3882
def independentCachedBranchMembers3884 : Finset ℕ := ([40,130,192,246,1594,1596,1614,1686,1702,1746,1748,1762,2680,2770,2772,2786,3102,3118,3164,3178,3180,3250,3252,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3884 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3884 5 (fun x => (if x<2680 then (if x<1614 then (if x<246 then (if x<130 then 0 else (if x<192 then 0 else 1)) else (if x<1594 then 1 else (if x<1596 then 2 else 0))) else (if x<1746 then (if x<1686 then 2 else (if x<1702 then 0 else 2)) else (if x<1748 then 1 else (if x<1762 then 3 else 3)))) else (if x<3164 then (if x<2786 then (if x<2770 then 0 else (if x<2772 then 0 else 1)) else (if x<3102 then 1 else (if x<3118 then 4 else 2))) else (if x<3250 then (if x<3178 then 3 else (if x<3180 then 3 else 0)) else (if x<3270 then (if x<3252 then 2 else 4) else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3885 : Finset ℕ := ([40,130,1596,1614,1686,1746,2772,2786,3118,3164,3178,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3885 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3885 4 (fun x => (if x<2772 then (if x<1614 then (if x<130 then 0 else (if x<1596 then 0 else 0)) else (if x<1686 then 1 else (if x<1746 then 0 else 1))) else (if x<3164 then (if x<2786 then 2 else (if x<3118 then 2 else 1)) else (if x<3178 then 2 else (if x<3250 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3886 : Finset ℕ := ([40,130,192,246,1594,1596,1614,1686,1702,1746,1748,1762,2680,2770,2772,2786,2788,3102,3118,3164,3178,3180,3250,3252,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3886 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3886 2788 4
  · have he : independentCachedBranchMembers3886.erase 2788=independentCachedBranchMembers3884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3884
  · have he : independentCachedBranchMembers3886.filter (independentCachedEdge 2788)=independentCachedBranchMembers3885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3885
def independentCachedBranchMembers3887 : Finset ℕ := ([192,1594,1596,1614,1686,1762,2680,2770,2772,3118,3164,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3887 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3887 4 (fun x => (if x<2680 then (if x<1614 then (if x<1594 then 0 else (if x<1596 then 0 else 1)) else (if x<1686 then 1 else (if x<1762 then 1 else 0))) else (if x<3118 then (if x<2770 then 2 else (if x<2772 then 2 else 3)) else (if x<3164 then 3 else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3888 : Finset ℕ := ([40,130,192,246,1594,1596,1614,1686,1702,1746,1748,1762,2680,2710,2770,2772,2786,2788,3102,3118,3164,3178,3180,3250,3252,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3888 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3888 2710 4
  · have he : independentCachedBranchMembers3888.erase 2710=independentCachedBranchMembers3886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3886
  · have he : independentCachedBranchMembers3888.filter (independentCachedEdge 2710)=independentCachedBranchMembers3887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3887
def independentCachedBranchMembers3889 : Finset ℕ := ([246,1596,1614,1686,1702,1748,2680,2770,2786,3178,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3889 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3889 4 (fun x => (if x<2680 then (if x<1686 then (if x<1596 then 0 else (if x<1614 then 1 else 1)) else (if x<1702 then 0 else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2770 then 2 else (if x<2786 then 0 else 2)) else (if x<3250 then 2 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3890 : Finset ℕ := ([40,130,192,246,1594,1596,1614,1686,1702,1746,1748,1762,2620,2680,2710,2770,2772,2786,2788,3102,3118,3164,3178,3180,3250,3252,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3890 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3890 2620 4
  · have he : independentCachedBranchMembers3890.erase 2620=independentCachedBranchMembers3888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3888
  · have he : independentCachedBranchMembers3890.filter (independentCachedEdge 2620)=independentCachedBranchMembers3889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3889
def independentCachedBranchMembers3891 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1642,1644,1686,1702,1714,1734,1746,1748,1762,1776,2606,2620,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3891 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3891 3150 5
  · have he : independentCachedBranchMembers3891.erase 3150=independentCachedBranchMembers3883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3883
  · have he : independentCachedBranchMembers3891.filter (independentCachedEdge 3150)=independentCachedBranchMembers3890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3890
def independentCachedBranchMembers3892 : Finset ℕ := ([12,130,144,246,1594,1614,1644,1686,1702,1746,1762,1776,2652,2668,2710,2740,2770,2786,2800,3102,3118,3132,3178,3192,3250,3270,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3892 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3892 5 (fun x => (if x<2710 then (if x<1686 then (if x<246 then (if x<130 then 0 else (if x<144 then 0 else 1)) else (if x<1614 then (if x<1594 then 1 else 2) else (if x<1644 then 2 else 0))) else (if x<1762 then (if x<1702 then 1 else (if x<1746 then 2 else 2)) else (if x<2652 then (if x<1776 then 0 else 1) else (if x<2668 then 0 else 3)))) else (if x<3132 then (if x<2786 then (if x<2740 then 4 else (if x<2770 then 1 else 0)) else (if x<3102 then (if x<2800 then 3 else 4) else (if x<3118 then 4 else 2))) else (if x<3250 then (if x<3178 then 0 else (if x<3192 then 3 else 4)) else (if x<3284 then (if x<3270 then 0 else 2) else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3893 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1642,1644,1686,1702,1714,1734,1746,1748,1762,1776,2606,2620,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3893 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3893 3130 5
  · have he : independentCachedBranchMembers3893.erase 3130=independentCachedBranchMembers3891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3891
  · have he : independentCachedBranchMembers3893.filter (independentCachedEdge 3130)=independentCachedBranchMembers3892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3892
def independentCachedBranchMembers3894 : Finset ℕ := ([12,40,130,144,192,246,1596,1644,1686,1714,1734,1748,1762,1776,2652,2680,2740,2770,2788,3118,3132,3180,3222,3250,3270,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3894 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3894 5 (fun x => (if x<2652 then (if x<1644 then (if x<144 then (if x<40 then 0 else (if x<130 then 1 else 0)) else (if x<246 then (if x<192 then 1 else 2) else (if x<1596 then 2 else 0))) else (if x<1734 then (if x<1686 then 1 else (if x<1714 then 3 else 0)) else (if x<1762 then (if x<1748 then 2 else 1) else (if x<1776 then 3 else 2)))) else (if x<3180 then (if x<2770 then (if x<2680 then 0 else (if x<2740 then 4 else 4)) else (if x<3118 then (if x<2788 then 0 else 2) else (if x<3132 then 1 else 4))) else (if x<3270 then (if x<3222 then 0 else (if x<3250 then 1 else 3)) else (if x<3298 then (if x<3284 then 3 else 2) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3895 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1642,1644,1686,1702,1714,1734,1746,1748,1762,1776,2606,2620,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3895 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3895 2650 5
  · have he : independentCachedBranchMembers3895.erase 2650=independentCachedBranchMembers3893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3893
  · have he : independentCachedBranchMembers3895.filter (independentCachedEdge 2650)=independentCachedBranchMembers3894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3894
def independentCachedBranchMembers3896 : Finset ℕ := ([12,40,130,144,1594,1644,1702,1734,1748,1762,1776,2606,2620,2680,2710,2738,2770,2788,3118,3132,3164,3178,3192,3222,3250,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3896 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3896 5 (fun x => (if x<2680 then (if x<1702 then (if x<144 then (if x<40 then 0 else (if x<130 then 1 else 0)) else (if x<1594 then 1 else (if x<1644 then 2 else 0))) else (if x<1762 then (if x<1734 then 2 else (if x<1748 then 3 else 1)) else (if x<2606 then (if x<1776 then 0 else 2) else (if x<2620 then 1 else 0)))) else (if x<3164 then (if x<2770 then (if x<2710 then 2 else (if x<2738 then 1 else 0)) else (if x<3118 then (if x<2788 then 3 else 2) else (if x<3132 then 4 else 3))) else (if x<3222 then (if x<3178 then 0 else (if x<3192 then 1 else 4)) else (if x<3282 then (if x<3250 then 3 else 4) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3897 : Finset ℕ := ([40,144,1594,1734,1776,2620,2680,2738,3118,3164,3178,3222,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3897 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3897 4 (fun x => (if x<2738 then (if x<1734 then (if x<144 then 0 else (if x<1594 then 0 else 1)) else (if x<2620 then (if x<1776 then 2 else 1) else (if x<2680 then 2 else 1))) else (if x<3178 then (if x<3118 then 1 else (if x<3164 then 0 else 3)) else (if x<3282 then (if x<3222 then 3 else 0) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3898 : Finset ℕ := ([12,40,130,144,1594,1644,1702,1734,1748,1762,1776,2606,2620,2652,2680,2710,2738,2770,2788,3118,3132,3164,3178,3192,3222,3250,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3898 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3898 2652 4
  · have he : independentCachedBranchMembers3898.erase 2652=independentCachedBranchMembers3896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3896
  · have he : independentCachedBranchMembers3898.filter (independentCachedEdge 2652)=independentCachedBranchMembers3897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3897
def independentCachedBranchMembers3899 : Finset ℕ := ([40,130,1594,1702,1748,1762,2680,2770,2788,3118,3164,3178,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3899 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3899 4 (fun x => (if x<2680 then (if x<1702 then (if x<130 then 0 else (if x<1594 then 0 else 1)) else (if x<1748 then 1 else (if x<1762 then 2 else 2))) else (if x<3118 then (if x<2770 then 0 else (if x<2788 then 0 else 1)) else (if x<3178 then (if x<3164 then 3 else 2) else (if x<3250 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3900 : Finset ℕ := ([1594,1762,2680,2770,3118,3164] : List ℕ).toFinset
theorem independentCachedBranchBound3900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3900 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3900 3 (fun x => (if x<2770 then (if x<1762 then 0 else (if x<2680 then 0 else 1)) else (if x<3118 then 1 else (if x<3164 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3901 : Finset ℕ := ([40,130,1594,1702,1748,1762,2680,2710,2770,2788,3118,3164,3178,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3901 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3901 2710 3
  · have he : independentCachedBranchMembers3901.erase 2710=independentCachedBranchMembers3899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3899
  · have he : independentCachedBranchMembers3901.filter (independentCachedEdge 2710)=independentCachedBranchMembers3900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3900
def independentCachedBranchMembers3902 : Finset ℕ := ([1702,1748,2680,2770,3178,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3902 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3902 3 (fun x => (if x<2770 then (if x<1748 then 0 else (if x<2680 then 0 else 1)) else (if x<3178 then 1 else (if x<3250 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3903 : Finset ℕ := ([40,130,1594,1702,1748,1762,2620,2680,2710,2770,2788,3118,3164,3178,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3903 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3903 2620 3
  · have he : independentCachedBranchMembers3903.erase 2620=independentCachedBranchMembers3901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3901
  · have he : independentCachedBranchMembers3903.filter (independentCachedEdge 2620)=independentCachedBranchMembers3902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3902
end EntropyDesigns.QuadraticRefinement
