/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch34
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3904 : Finset ℕ := ([12,40,130,144,1594,1644,1702,1734,1748,1762,1776,2606,2620,2652,2680,2710,2738,2770,2788,3118,3132,3150,3164,3178,3192,3222,3250,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3904 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3904 3150 4
  · have he : independentCachedBranchMembers3904.erase 3150=independentCachedBranchMembers3898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3898
  · have he : independentCachedBranchMembers3904.filter (independentCachedEdge 3150)=independentCachedBranchMembers3903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3903
def independentCachedBranchMembers3905 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1642,1644,1686,1702,1714,1734,1746,1748,1762,1764,1776,2606,2620,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3905 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3905 1764 5
  · have he : independentCachedBranchMembers3905.erase 1764=independentCachedBranchMembers3895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3895
  · have he : independentCachedBranchMembers3905.filter (independentCachedEdge 1764)=independentCachedBranchMembers3904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3904
def independentCachedBranchMembers3906 : Finset ℕ := ([40,144,192,246,1596,1614,1644,1702,1714,1748,1762,2606,2652,2710,2740,2758,2770,2800,3118,3164,3178,3222,3252,3270,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3906 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3906 5 (fun x => (if x<2710 then (if x<1644 then (if x<246 then (if x<144 then 0 else (if x<192 then 0 else 1)) else (if x<1596 then 1 else (if x<1614 then 2 else 2))) else (if x<1748 then (if x<1702 then 0 else (if x<1714 then 2 else 3)) else (if x<2606 then (if x<1762 then 0 else 1) else (if x<2652 then 0 else 2)))) else (if x<3178 then (if x<2770 then (if x<2740 then 0 else (if x<2758 then 2 else 1)) else (if x<3118 then (if x<2800 then 3 else 1) else (if x<3164 then 4 else 4))) else (if x<3270 then (if x<3222 then 0 else (if x<3252 then 3 else 4)) else (if x<3300 then (if x<3282 then 4 else 0) else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3907 : Finset ℕ := ([40,144,1596,1614,1714,2740,2758,2800,3118,3164,3178,3222,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3907 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3907 4 (fun x => (if x<2800 then (if x<1614 then (if x<144 then 0 else (if x<1596 then 0 else 1)) else (if x<2740 then (if x<1714 then 1 else 2) else (if x<2758 then 1 else 1))) else (if x<3178 then (if x<3118 then 2 else (if x<3164 then 0 else 3)) else (if x<3282 then (if x<3222 then 3 else 0) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3908 : Finset ℕ := ([40,144,192,246,1596,1614,1644,1702,1714,1748,1762,2606,2652,2710,2740,2758,2770,2788,2800,3118,3164,3178,3222,3252,3270,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3908 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3908 2788 4
  · have he : independentCachedBranchMembers3908.erase 2788=independentCachedBranchMembers3906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3906
  · have he : independentCachedBranchMembers3908.filter (independentCachedEdge 2788)=independentCachedBranchMembers3907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3907
def independentCachedBranchMembers3909 : Finset ℕ := ([144,246,1614,1644,1702,1762,2740,2770,2800,3118,3178,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3909 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3909 4 (fun x => (if x<2740 then (if x<1644 then (if x<246 then 0 else (if x<1614 then 0 else 1)) else (if x<1702 then 2 else (if x<1762 then 1 else 2))) else (if x<3118 then (if x<2770 then 0 else (if x<2800 then 0 else 3)) else (if x<3270 then (if x<3178 then 1 else 2) else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3910 : Finset ℕ := ([1614,1762,2740,2770,3118,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3910 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3910 3 (fun x => (if x<2770 then (if x<1762 then 0 else (if x<2740 then 0 else 1)) else (if x<3118 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3911 : Finset ℕ := ([144,246,1614,1644,1702,1762,2710,2740,2770,2800,3118,3178,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3911 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3911 2710 3
  · have he : independentCachedBranchMembers3911.erase 2710=independentCachedBranchMembers3909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3909
  · have he : independentCachedBranchMembers3911.filter (independentCachedEdge 2710)=independentCachedBranchMembers3910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3910
def independentCachedBranchMembers3912 : Finset ℕ := ([144,246,3118,3178,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3912 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3912 3 (fun x => (if x<3178 then (if x<246 then 0 else (if x<3118 then 0 else 1)) else (if x<3270 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3913 : Finset ℕ := ([144,246,1614,1644,1702,1762,2652,2710,2740,2770,2800,3118,3178,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3913 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3913 2652 3
  · have he : independentCachedBranchMembers3913.erase 2652=independentCachedBranchMembers3911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3911
  · have he : independentCachedBranchMembers3913.filter (independentCachedEdge 2652)=independentCachedBranchMembers3912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3912
def independentCachedBranchMembers3914 : Finset ℕ := ([40,144,192,246,1596,1614,1644,1702,1714,1748,1762,2606,2652,2710,2740,2758,2770,2788,2800,3118,3130,3164,3178,3222,3252,3270,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3914 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3914 3130 4
  · have he : independentCachedBranchMembers3914.erase 3130=independentCachedBranchMembers3908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3908
  · have he : independentCachedBranchMembers3914.filter (independentCachedEdge 3130)=independentCachedBranchMembers3913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3913
def independentCachedBranchMembers3915 : Finset ℕ := ([12,40,130,144,192,246,1594,1596,1614,1628,1642,1644,1686,1702,1714,1734,1746,1748,1762,1764,1776,2606,2620,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3915 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3915 1628 5
  · have he : independentCachedBranchMembers3915.erase 1628=independentCachedBranchMembers3905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3905
  · have he : independentCachedBranchMembers3915.filter (independentCachedEdge 1628)=independentCachedBranchMembers3914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3914
def independentCachedBranchMembers3916 : Finset ℕ := ([1594,1596,1614,1644,1702,1748,1776,2606,2680,2740,2786,3118,3164,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3916 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3916 5 (fun x => (if x<2680 then (if x<1702 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1644 then 0 else 2)) else (if x<1776 then (if x<1748 then 0 else 1) else (if x<2606 then 2 else 0))) else (if x<3164 then (if x<2786 then (if x<2740 then 2 else 1) else (if x<3118 then 3 else 4)) else (if x<3270 then (if x<3250 then 3 else 4) else (if x<3300 then 3 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3917 : Finset ℕ := ([1594,1596,1614,1776,2606,2786,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3917 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3917 4 (fun x => (if x<2606 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1776 then 0 else 1)) else (if x<3250 then (if x<2786 then 0 else 1) else (if x<3270 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3918 : Finset ℕ := ([1594,1596,1614,1644,1702,1748,1776,2606,2680,2740,2786,3118,3164,3222,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3918 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3918 3222 4
  · have he : independentCachedBranchMembers3918.erase 3222=independentCachedBranchMembers3916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3916
  · have he : independentCachedBranchMembers3918.filter (independentCachedEdge 3222)=independentCachedBranchMembers3917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3917
def independentCachedBranchMembers3919 : Finset ℕ := ([1644,1776,2680,2786,3118,3164,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3919 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3919 4 (fun x => (if x<3118 then (if x<2680 then (if x<1776 then 0 else 0) else (if x<2786 then 0 else 1)) else (if x<3250 then (if x<3164 then 2 else 1) else (if x<3270 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3920 : Finset ℕ := ([1594,1596,1614,1644,1702,1748,1776,2606,2680,2740,2758,2786,3118,3164,3222,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3920 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3920 2758 4
  · have he : independentCachedBranchMembers3920.erase 2758=independentCachedBranchMembers3918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3918
  · have he : independentCachedBranchMembers3920.filter (independentCachedEdge 2758)=independentCachedBranchMembers3919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3919
def independentCachedBranchMembers3921 : Finset ℕ := ([1596,1748,2740,2786,3118,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3921 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3921 4 (fun x => (if x<3118 then (if x<2740 then (if x<1748 then 0 else 0) else (if x<2786 then 0 else 1)) else (if x<3270 then (if x<3250 then 2 else 1) else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3922 : Finset ℕ := ([1594,1596,1614,1644,1702,1748,1776,2606,2680,2738,2740,2758,2786,3118,3164,3222,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3922 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3922 2738 4
  · have he : independentCachedBranchMembers3922.erase 2738=independentCachedBranchMembers3920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3920
  · have he : independentCachedBranchMembers3922.filter (independentCachedEdge 2738)=independentCachedBranchMembers3921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3921
def independentCachedBranchMembers3923 : Finset ℕ := ([1596,1644,1748,1776,2680,2740,3164,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3923 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3923 4 (fun x => (if x<2680 then (if x<1748 then (if x<1644 then 0 else 1) else (if x<1776 then 0 else 1)) else (if x<3164 then (if x<2740 then 1 else 0) else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3924 : Finset ℕ := ([1594,1596,1614,1644,1702,1746,1748,1776,2606,2680,2738,2740,2758,2786,3118,3164,3222,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3924 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3924 1746 4
  · have he : independentCachedBranchMembers3924.erase 1746=independentCachedBranchMembers3922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3922
  · have he : independentCachedBranchMembers3924.filter (independentCachedEdge 1746)=independentCachedBranchMembers3923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3923
def independentCachedBranchMembers3925 : Finset ℕ := ([1594,1596,1614,1644,2606,2680,3118,3164] : List ℕ).toFinset
theorem independentCachedBranchBound3925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3925 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3925 4 (fun x => (if x<2606 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1644 then 0 else 2)) else (if x<3118 then (if x<2680 then 0 else 1) else (if x<3164 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3926 : Finset ℕ := ([246,1594,1596,1614,1644,1702,1746,1748,1776,2606,2680,2738,2740,2758,2786,3118,3164,3222,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3926 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3926 246 4
  · have he : independentCachedBranchMembers3926.erase 246=independentCachedBranchMembers3924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3924
  · have he : independentCachedBranchMembers3926.filter (independentCachedEdge 246)=independentCachedBranchMembers3925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3925
def independentCachedBranchMembers3927 : Finset ℕ := ([1594,1614,1748,1776,2606,2740,3118,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3927 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3927 4 (fun x => (if x<2606 then (if x<1748 then (if x<1614 then 0 else 0) else (if x<1776 then 1 else 2)) else (if x<3118 then (if x<2740 then 0 else 1) else (if x<3300 then 2 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3928 : Finset ℕ := ([130,246,1594,1596,1614,1644,1702,1746,1748,1776,2606,2680,2738,2740,2758,2786,3118,3164,3222,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3928 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3928 130 4
  · have he : independentCachedBranchMembers3928.erase 130=independentCachedBranchMembers3926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3926
  · have he : independentCachedBranchMembers3928.filter (independentCachedEdge 130)=independentCachedBranchMembers3927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3927
def independentCachedBranchMembers3929 : Finset ℕ := ([1594,1614,1644,1748,2606,2680,2740,2786,3164,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3929 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3929 4 (fun x => (if x<2740 then (if x<1748 then (if x<1614 then 0 else (if x<1644 then 0 else 1)) else (if x<2606 then 1 else (if x<2680 then 0 else 2))) else (if x<3250 then (if x<2786 then 2 else (if x<3164 then 2 else 1)) else (if x<3270 then 3 else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3930 : Finset ℕ := ([130,246,1594,1596,1614,1644,1702,1746,1748,1776,2606,2680,2738,2740,2758,2786,3118,3164,3222,3250,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3930 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3930 3298 4
  · have he : independentCachedBranchMembers3930.erase 3298=independentCachedBranchMembers3928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3928
  · have he : independentCachedBranchMembers3930.filter (independentCachedEdge 3298)=independentCachedBranchMembers3929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3929
def independentCachedBranchMembers3931 : Finset ℕ := ([130,1594,1644,1746,2606,2680,2740,2758,2786,3222,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3931 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3931 4 (fun x => (if x<2740 then (if x<1746 then (if x<1594 then 0 else (if x<1644 then 1 else 0)) else (if x<2606 then 1 else (if x<2680 then 1 else 0))) else (if x<3222 then (if x<2758 then 2 else (if x<2786 then 1 else 2)) else (if x<3250 then 0 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3932 : Finset ℕ := ([130,246,1594,1596,1614,1644,1702,1746,1748,1776,2606,2680,2738,2740,2758,2786,3118,3164,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3932 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3932 3252 4
  · have he : independentCachedBranchMembers3932.erase 3252=independentCachedBranchMembers3930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3930
  · have he : independentCachedBranchMembers3932.filter (independentCachedEdge 3252)=independentCachedBranchMembers3931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3931
def independentCachedBranchMembers3933 : Finset ℕ := ([246,1614,1746,1748,2606,2680,2738,2740,2786,3164,3222,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3933 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3933 4 (fun x => (if x<2738 then (if x<1748 then (if x<1614 then 0 else (if x<1746 then 1 else 0)) else (if x<2606 then 1 else (if x<2680 then 1 else 2))) else (if x<3164 then (if x<2740 then 0 else (if x<2786 then 1 else 2)) else (if x<3222 then 2 else (if x<3270 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3934 : Finset ℕ := ([130,246,1594,1596,1614,1644,1702,1746,1748,1776,2606,2680,2738,2740,2758,2786,3118,3164,3192,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3934 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3934 3192 4
  · have he : independentCachedBranchMembers3934.erase 3192=independentCachedBranchMembers3932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3932
  · have he : independentCachedBranchMembers3934.filter (independentCachedEdge 3192)=independentCachedBranchMembers3933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3933
def independentCachedBranchMembers3935 : Finset ℕ := ([130,1596,1614,1746,2740,2758,2786,3118,3164,3192,3222,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3935 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3935 4 (fun x => (if x<2786 then (if x<1746 then (if x<1596 then 0 else (if x<1614 then 0 else 1)) else (if x<2740 then 1 else (if x<2758 then 2 else 0))) else (if x<3192 then (if x<3118 then 2 else (if x<3164 then 1 else 3)) else (if x<3250 then (if x<3222 then 0 else 3) else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
