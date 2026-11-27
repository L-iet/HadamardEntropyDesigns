/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch35
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3936 : Finset ℕ := ([130,246,1594,1596,1614,1644,1702,1746,1748,1776,2606,2680,2738,2740,2758,2786,2788,3118,3164,3192,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3936 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3936 2788 4
  · have he : independentCachedBranchMembers3936.erase 2788=independentCachedBranchMembers3934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3934
  · have he : independentCachedBranchMembers3936.filter (independentCachedEdge 2788)=independentCachedBranchMembers3935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3935
def independentCachedBranchMembers3937 : Finset ℕ := ([1594,1596,1614,1776,2680,2738,2740,2758,3118,3164,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3937 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3937 4 (fun x => (if x<2740 then (if x<1776 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<2680 then 1 else (if x<2738 then 1 else 0))) else (if x<3164 then (if x<2758 then 1 else (if x<3118 then 0 else 2)) else (if x<3298 then (if x<3222 then 2 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3938 : Finset ℕ := ([130,246,1594,1596,1614,1644,1702,1746,1748,1776,2606,2680,2710,2738,2740,2758,2786,2788,3118,3164,3192,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3938 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3938 2710 4
  · have he : independentCachedBranchMembers3938.erase 2710=independentCachedBranchMembers3936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3936
  · have he : independentCachedBranchMembers3938.filter (independentCachedEdge 2710)=independentCachedBranchMembers3937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3937
def independentCachedBranchMembers3939 : Finset ℕ := ([246,1594,1746,1776,2680,2738,2786,3118,3164,3222,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3939 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3939 4 (fun x => (if x<2786 then (if x<1776 then (if x<1594 then 0 else (if x<1746 then 1 else 0)) else (if x<2680 then 1 else (if x<2738 then 1 else 0))) else (if x<3222 then (if x<3118 then 2 else (if x<3164 then 3 else 2)) else (if x<3270 then 0 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3940 : Finset ℕ := ([1594,1746,2680,2786,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3940 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3940 3 (fun x => (if x<2786 then (if x<1746 then 0 else (if x<2680 then 0 else 1)) else (if x<3222 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3941 : Finset ℕ := ([246,1594,1746,1776,2680,2738,2786,3118,3164,3222,3252,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3941 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3941 3252 3
  · have he : independentCachedBranchMembers3941.erase 3252=independentCachedBranchMembers3939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3939
  · have he : independentCachedBranchMembers3941.filter (independentCachedEdge 3252)=independentCachedBranchMembers3940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3940
def independentCachedBranchMembers3942 : Finset ℕ := ([130,246,1594,1596,1614,1644,1702,1746,1748,1776,2606,2652,2680,2710,2738,2740,2758,2786,2788,3118,3164,3192,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3942 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3942 2652 4
  · have he : independentCachedBranchMembers3942.erase 2652=independentCachedBranchMembers3938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3938
  · have he : independentCachedBranchMembers3942.filter (independentCachedEdge 2652)=independentCachedBranchMembers3941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3941
def independentCachedBranchMembers3943 : Finset ℕ := ([130,246,1594,1614,1644,1748,2652,2738,2758,2788,3164,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3943 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3943 4 (fun x => (if x<2738 then (if x<1614 then (if x<246 then 0 else (if x<1594 then 0 else 1)) else (if x<1748 then (if x<1644 then 1 else 2) else (if x<2652 then 2 else 2))) else (if x<3164 then (if x<2758 then 0 else (if x<2788 then 0 else 2)) else (if x<3270 then (if x<3250 then 3 else 1) else (if x<3300 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3944 : Finset ℕ := ([130,246,1594,1596,1614,1642,1644,1702,1746,1748,1776,2606,2652,2680,2710,2738,2740,2758,2786,2788,3118,3164,3192,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3944 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3944 1642 4
  · have he : independentCachedBranchMembers3944.erase 1642=independentCachedBranchMembers3942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3942
  · have he : independentCachedBranchMembers3944.filter (independentCachedEdge 1642)=independentCachedBranchMembers3943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3943
def independentCachedBranchMembers3945 : Finset ℕ := ([130,246,1596,1644,1748,1776,2652,2680,2740,2788,3118,3222,3250,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3945 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3945 4 (fun x => (if x<2680 then (if x<1644 then (if x<246 then 0 else (if x<1596 then 0 else 1)) else (if x<1776 then (if x<1748 then 2 else 1) else (if x<2652 then 2 else 1))) else (if x<3222 then (if x<2788 then (if x<2740 then 2 else 1) else (if x<3118 then 2 else 3)) else (if x<3270 then (if x<3250 then 0 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3946 : Finset ℕ := ([130,246,1594,1596,1614,1642,1644,1702,1746,1748,1776,2606,2650,2652,2680,2710,2738,2740,2758,2786,2788,3118,3164,3192,3222,3250,3252,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3946 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3946 2650 4
  · have he : independentCachedBranchMembers3946.erase 2650=independentCachedBranchMembers3944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3944
  · have he : independentCachedBranchMembers3946.filter (independentCachedEdge 2650)=independentCachedBranchMembers3945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3945
def independentCachedBranchMembers3947 : Finset ℕ := ([12,40,130,144,192,246,1582,1594,1596,1614,1628,1642,1644,1686,1702,1714,1734,1746,1748,1762,1764,1776,2606,2620,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3947 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3947 1582 5
  · have he : independentCachedBranchMembers3947.erase 1582=independentCachedBranchMembers3915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3915
  · have he : independentCachedBranchMembers3947.filter (independentCachedEdge 1582)=independentCachedBranchMembers3946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3946
def independentCachedBranchMembers3948 : Finset ℕ := ([40,130,192,246,1594,1596,1614,1686,1702,1746,1748,1762,2606,2652,2668,2738,2740,2758,2800,3132,3150,3192,3222,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3948 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3948 5 (fun x => (if x<2652 then (if x<1614 then (if x<246 then (if x<130 then 0 else (if x<192 then 0 else 1)) else (if x<1594 then 1 else (if x<1596 then 2 else 0))) else (if x<1746 then (if x<1686 then 2 else (if x<1702 then 0 else 2)) else (if x<1762 then (if x<1748 then 1 else 3) else (if x<2606 then 3 else 2)))) else (if x<3150 then (if x<2740 then (if x<2668 then 3 else (if x<2738 then 0 else 2)) else (if x<2800 then (if x<2758 then 4 else 0) else (if x<3132 then 1 else 4))) else (if x<3282 then (if x<3192 then 4 else (if x<3222 then 0 else 4)) else (if x<3298 then (if x<3284 then 0 else 1) else (if x<3300 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3949 : Finset ℕ := ([40,192,1594,1596,1614,1702,1746,1748,2668,2800,3192,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3949 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3949 4 (fun x => (if x<1748 then (if x<1596 then (if x<192 then 0 else (if x<1594 then 0 else 0)) else (if x<1702 then (if x<1614 then 1 else 1) else (if x<1746 then 1 else 0))) else (if x<3192 then (if x<2668 then 1 else (if x<2800 then 2 else 2)) else (if x<3298 then (if x<3222 then 2 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3950 : Finset ℕ := ([40,130,192,246,1594,1596,1614,1686,1702,1746,1748,1762,2606,2652,2668,2738,2740,2758,2800,3132,3150,3192,3222,3238,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3950 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3950 3238 4
  · have he : independentCachedBranchMembers3950.erase 3238=independentCachedBranchMembers3948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3948
  · have he : independentCachedBranchMembers3950.filter (independentCachedEdge 3238)=independentCachedBranchMembers3949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3949
def independentCachedBranchMembers3951 : Finset ℕ := ([40,130,192,246,1596,1686,1748,1762,2652,2740,3132,3222,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3951 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3951 4 (fun x => (if x<1762 then (if x<246 then (if x<130 then 0 else (if x<192 then 0 else 1)) else (if x<1686 then (if x<1596 then 1 else 0) else (if x<1748 then 0 else 1))) else (if x<3132 then (if x<2652 then 1 else (if x<2740 then 2 else 2)) else (if x<3284 then (if x<3222 then 2 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3952 : Finset ℕ := ([40,130,192,246,1594,1596,1614,1686,1702,1746,1748,1762,2606,2650,2652,2668,2738,2740,2758,2800,3132,3150,3192,3222,3238,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3952 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3952 2650 4
  · have he : independentCachedBranchMembers3952.erase 2650=independentCachedBranchMembers3950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3950
  · have he : independentCachedBranchMembers3952.filter (independentCachedEdge 2650)=independentCachedBranchMembers3951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3951
def independentCachedBranchMembers3953 : Finset ℕ := ([40,130,1594,1702,1748,1762,2606,2652,2738,3132,3150,3192,3222,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3953 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3953 4 (fun x => (if x<2652 then (if x<1702 then (if x<130 then 0 else (if x<1594 then 0 else 1)) else (if x<1762 then (if x<1748 then 1 else 2) else (if x<2606 then 2 else 1))) else (if x<3192 then (if x<3132 then (if x<2738 then 2 else 1) else (if x<3150 then 0 else 3)) else (if x<3282 then (if x<3222 then 3 else 0) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3954 : Finset ℕ := ([40,130,192,246,1594,1596,1614,1686,1702,1746,1748,1762,1764,2606,2650,2652,2668,2738,2740,2758,2800,3132,3150,3192,3222,3238,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3954 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3954 1764 4
  · have he : independentCachedBranchMembers3954.erase 1764=independentCachedBranchMembers3952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3952
  · have he : independentCachedBranchMembers3954.filter (independentCachedEdge 1764)=independentCachedBranchMembers3953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3953
def independentCachedBranchMembers3955 : Finset ℕ := ([130,246,1594,1614,1686,1702,1746,1762,2652,2668,2740,2800,3132,3192,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3955 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3955 4 (fun x => (if x<2652 then (if x<1686 then (if x<1594 then (if x<246 then 0 else 0) else (if x<1614 then 1 else 1)) else (if x<1746 then (if x<1702 then 0 else 1) else (if x<1762 then 1 else 0))) else (if x<3132 then (if x<2740 then (if x<2668 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3284 then (if x<3192 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3956 : Finset ℕ := ([40,130,192,246,1594,1596,1614,1686,1702,1746,1748,1762,1764,2606,2650,2652,2668,2738,2740,2758,2800,3130,3132,3150,3192,3222,3238,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3956 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3956 3130 4
  · have he : independentCachedBranchMembers3956.erase 3130=independentCachedBranchMembers3954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3954
  · have he : independentCachedBranchMembers3956.filter (independentCachedEdge 3130)=independentCachedBranchMembers3955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3955
def independentCachedBranchMembers3957 : Finset ℕ := ([12,40,130,144,192,246,1582,1594,1596,1614,1628,1642,1644,1686,1702,1714,1734,1746,1748,1762,1764,1776,2606,2620,2638,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3957 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3957 2638 5
  · have he : independentCachedBranchMembers3957.erase 2638=independentCachedBranchMembers3947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3947
  · have he : independentCachedBranchMembers3957.filter (independentCachedEdge 2638)=independentCachedBranchMembers3956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3956
def independentCachedBranchMembers3958 : Finset ℕ := ([12,130,144,246,1594,1614,1644,1686,1702,1746,1762,1776,2606,2620,2650,2680,2738,2758,2772,2788,3130,3164,3180,3222,3238,3252,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3958 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3958 5 (fun x => (if x<2650 then (if x<1686 then (if x<246 then (if x<130 then 0 else (if x<144 then 0 else 1)) else (if x<1614 then (if x<1594 then 1 else 2) else (if x<1644 then 2 else 0))) else (if x<1762 then (if x<1702 then 1 else (if x<1746 then 2 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2620 then 2 else 0)))) else (if x<3164 then (if x<2758 then (if x<2680 then 2 else (if x<2738 then 3 else 0)) else (if x<2788 then (if x<2772 then 2 else 1) else (if x<3130 then 3 else 3))) else (if x<3252 then (if x<3222 then (if x<3180 then 0 else 3) else (if x<3238 then 4 else 3)) else (if x<3298 then (if x<3282 then 1 else 0) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3959 : Finset ℕ := ([144,246,1614,1644,1702,1762,2606,2758,2788,3130,3164,3222,3252,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3959 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3959 4 (fun x => (if x<2758 then (if x<1644 then (if x<246 then 0 else (if x<1614 then 0 else 1)) else (if x<1762 then (if x<1702 then 2 else 1) else (if x<2606 then 2 else 1))) else (if x<3222 then (if x<3130 then (if x<2788 then 1 else 2) else (if x<3164 then 3 else 3)) else (if x<3282 then (if x<3252 then 0 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3960 : Finset ℕ := ([12,130,144,246,1594,1614,1628,1644,1686,1702,1746,1762,1776,2606,2620,2650,2680,2738,2758,2772,2788,3130,3164,3180,3222,3238,3252,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3960 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3960 1628 4
  · have he : independentCachedBranchMembers3960.erase 1628=independentCachedBranchMembers3958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3958
  · have he : independentCachedBranchMembers3960.filter (independentCachedEdge 1628)=independentCachedBranchMembers3959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3959
def independentCachedBranchMembers3961 : Finset ℕ := ([130,246,1594,1614,1686,1702,1746,1762,2620,2680,2772,2788,3164,3180,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3961 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3961 4 (fun x => (if x<2620 then (if x<1686 then (if x<1594 then (if x<246 then 0 else 0) else (if x<1614 then 1 else 1)) else (if x<1746 then (if x<1702 then 0 else 1) else (if x<1762 then 1 else 0))) else (if x<3164 then (if x<2772 then (if x<2680 then 2 else 3) else (if x<2788 then 2 else 3)) else (if x<3252 then (if x<3180 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3962 : Finset ℕ := ([12,130,144,246,1594,1614,1628,1644,1686,1702,1746,1762,1776,2606,2620,2650,2680,2738,2758,2772,2788,3130,3150,3164,3180,3222,3238,3252,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3962 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3962 3150 4
  · have he : independentCachedBranchMembers3962.erase 3150=independentCachedBranchMembers3960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3960
  · have he : independentCachedBranchMembers3962.filter (independentCachedEdge 3150)=independentCachedBranchMembers3961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3961
def independentCachedBranchMembers3963 : Finset ℕ := ([12,40,130,144,192,246,1582,1594,1596,1614,1628,1642,1644,1686,1702,1714,1734,1746,1748,1762,1764,1776,2606,2618,2620,2638,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3963 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3963 2618 5
  · have he : independentCachedBranchMembers3963.erase 2618=independentCachedBranchMembers3957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3957
  · have he : independentCachedBranchMembers3963.filter (independentCachedEdge 2618)=independentCachedBranchMembers3962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3962
def independentCachedBranchMembers3964 : Finset ℕ := ([40,144,192,246,1594,1614,1642,1702,1746,1764,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3118,3180,3250,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3964 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3964 5 (fun x => (if x<2668 then (if x<1642 then (if x<246 then (if x<144 then 0 else (if x<192 then 0 else 1)) else (if x<1594 then 1 else (if x<1614 then 2 else 2))) else (if x<1764 then (if x<1702 then 0 else (if x<1746 then 2 else 0)) else (if x<2620 then (if x<2606 then 1 else 0) else (if x<2650 then 3 else 2)))) else (if x<2800 then (if x<2758 then (if x<2710 then 4 else (if x<2738 then 0 else 2)) else (if x<2772 then 1 else (if x<2786 then 3 else 4))) else (if x<3250 then (if x<3118 then 1 else (if x<3180 then 3 else 0)) else (if x<3284 then (if x<3270 then 4 else 3) else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3965 : Finset ℕ := ([40,144,192,246,1614,1702,2606,2710,2758,2800,3118,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3965 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3965 4 (fun x => (if x<2606 then (if x<246 then (if x<144 then 0 else (if x<192 then 0 else 1)) else (if x<1614 then 1 else (if x<1702 then 2 else 2))) else (if x<2800 then (if x<2710 then 0 else (if x<2758 then 0 else 1)) else (if x<3118 then 1 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3966 : Finset ℕ := ([40,144,192,246,1594,1614,1628,1642,1702,1746,1764,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3118,3180,3250,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3966 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3966 1628 4
  · have he : independentCachedBranchMembers3966.erase 1628=independentCachedBranchMembers3964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3964
  · have he : independentCachedBranchMembers3966.filter (independentCachedEdge 1628)=independentCachedBranchMembers3965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3965
def independentCachedBranchMembers3967 : Finset ℕ := ([144,192,1594,1614,1642,1764,2606,2650,2772,2800,3118,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3967 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3967 4 (fun x => (if x<2606 then (if x<1614 then (if x<192 then 0 else (if x<1594 then 1 else 1)) else (if x<1642 then 0 else (if x<1764 then 2 else 2))) else (if x<2800 then (if x<2650 then 0 else (if x<2772 then 2 else 1)) else (if x<3118 then 3 else (if x<3284 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
