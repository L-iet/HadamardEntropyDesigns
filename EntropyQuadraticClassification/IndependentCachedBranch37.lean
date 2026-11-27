/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch36
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3968 : Finset ℕ := ([40,130,144,192,246,1594,1614,1628,1642,1702,1746,1764,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3118,3180,3250,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3968 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3968 130 4
  · have he : independentCachedBranchMembers3968.erase 130=independentCachedBranchMembers3966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3966
  · have he : independentCachedBranchMembers3968.filter (independentCachedEdge 130)=independentCachedBranchMembers3967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3967
def independentCachedBranchMembers3969 : Finset ℕ := ([40,246,1594,1642,1702,1764,2650,2710,2758,2772,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3969 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3969 4 (fun x => (if x<2650 then (if x<1642 then (if x<246 then 0 else (if x<1594 then 1 else 0)) else (if x<1702 then 2 else (if x<1764 then 1 else 2))) else (if x<2772 then (if x<2710 then 2 else (if x<2758 then 1 else 0)) else (if x<3270 then 2 else (if x<3284 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3970 : Finset ℕ := ([12,40,130,144,192,246,1594,1614,1628,1642,1702,1746,1764,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3118,3180,3250,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3970 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3970 12 4
  · have he : independentCachedBranchMembers3970.erase 12=independentCachedBranchMembers3968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3968
  · have he : independentCachedBranchMembers3970.filter (independentCachedEdge 12)=independentCachedBranchMembers3969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3969
def independentCachedBranchMembers3971 : Finset ℕ := ([130,1594,1628,1642,1702,2620,2650,2668,2710,2758,2800,3118,3250,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3971 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3971 4 (fun x => (if x<2668 then (if x<1642 then (if x<1594 then 0 else (if x<1628 then 1 else 0)) else (if x<2620 then (if x<1702 then 2 else 1) else (if x<2650 then 0 else 1))) else (if x<3118 then (if x<2758 then (if x<2710 then 2 else 3) else (if x<2800 then 1 else 3)) else (if x<3284 then (if x<3250 then 2 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3972 : Finset ℕ := ([1628,1702,2650,2800,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3972 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3972 3 (fun x => (if x<2800 then (if x<1702 then 0 else (if x<2650 then 1 else 0)) else (if x<3250 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3973 : Finset ℕ := ([40,130,1594,1628,1642,1702,2620,2650,2668,2710,2758,2800,3118,3250,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3973 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3973 40 3
  · have he : independentCachedBranchMembers3973.erase 40=independentCachedBranchMembers3971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3971
  · have he : independentCachedBranchMembers3973.filter (independentCachedEdge 40)=independentCachedBranchMembers3972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3972
def independentCachedBranchMembers3974 : Finset ℕ := ([12,40,130,144,192,246,1594,1614,1628,1642,1702,1746,1764,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3118,3180,3250,3270,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3974 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3974 3312 4
  · have he : independentCachedBranchMembers3974.erase 3312=independentCachedBranchMembers3970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3970
  · have he : independentCachedBranchMembers3974.filter (independentCachedEdge 3312)=independentCachedBranchMembers3973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3973
def independentCachedBranchMembers3975 : Finset ℕ := ([192,1594,1614,1628,1764,2606,2620,2650,2710,2786,2800,3180,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3975 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3975 4 (fun x => (if x<2650 then (if x<1628 then (if x<1594 then 0 else (if x<1614 then 0 else 1)) else (if x<2606 then (if x<1764 then 2 else 1) else (if x<2620 then 0 else 2))) else (if x<3180 then (if x<2786 then (if x<2710 then 1 else 3) else (if x<2800 then 3 else 1)) else (if x<3270 then (if x<3250 then 2 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3976 : Finset ℕ := ([1594,1764,2650,2710,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3976 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3976 3 (fun x => (if x<2710 then (if x<1764 then 0 else (if x<2650 then 1 else 0)) else (if x<3270 then 2 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3977 : Finset ℕ := ([12,192,1594,1614,1628,1764,2606,2620,2650,2710,2786,2800,3180,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3977 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3977 12 3
  · have he : independentCachedBranchMembers3977.erase 12=independentCachedBranchMembers3975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3975
  · have he : independentCachedBranchMembers3977.filter (independentCachedEdge 12)=independentCachedBranchMembers3976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3976
def independentCachedBranchMembers3978 : Finset ℕ := ([12,40,130,144,192,246,1594,1614,1628,1642,1702,1746,1764,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3118,3180,3222,3250,3270,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3978 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3978 3222 4
  · have he : independentCachedBranchMembers3978.erase 3222=independentCachedBranchMembers3974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3974
  · have he : independentCachedBranchMembers3978.filter (independentCachedEdge 3222)=independentCachedBranchMembers3977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3977
def independentCachedBranchMembers3979 : Finset ℕ := ([246,1614,1642,1702,1764,2620,2650,2710,2738,2772,2800,3118,3180,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3979 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3979 4 (fun x => (if x<2710 then (if x<1702 then (if x<1614 then 0 else (if x<1642 then 1 else 2)) else (if x<2620 then (if x<1764 then 0 else 1) else (if x<2650 then 3 else 1))) else (if x<3118 then (if x<2772 then (if x<2738 then 0 else 3) else (if x<2800 then 2 else 1)) else (if x<3270 then (if x<3180 then 2 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3980 : Finset ℕ := ([1702,1764,2620,2650,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3980 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3980 3 (fun x => (if x<2650 then (if x<1764 then 0 else (if x<2620 then 1 else 2)) else (if x<3270 then 0 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3981 : Finset ℕ := ([144,246,1614,1642,1702,1764,2620,2650,2710,2738,2772,2800,3118,3180,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3981 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3981 144 3
  · have he : independentCachedBranchMembers3981.erase 144=independentCachedBranchMembers3979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3979
  · have he : independentCachedBranchMembers3981.filter (independentCachedEdge 144)=independentCachedBranchMembers3980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3980
def independentCachedBranchMembers3982 : Finset ℕ := ([12,40,130,144,192,246,1594,1614,1628,1642,1702,1746,1764,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3118,3132,3180,3222,3250,3270,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3982 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3982 3132 4
  · have he : independentCachedBranchMembers3982.erase 3132=independentCachedBranchMembers3978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3978
  · have he : independentCachedBranchMembers3982.filter (independentCachedEdge 3132)=independentCachedBranchMembers3981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3981
def independentCachedBranchMembers3983 : Finset ℕ := ([12,40,130,144,192,246,1582,1594,1596,1614,1626,1628,1642,1644,1686,1702,1714,1734,1746,1748,1762,1764,1776,2606,2618,2620,2638,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3983 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3983 1626 5
  · have he : independentCachedBranchMembers3983.erase 1626=independentCachedBranchMembers3963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3963
  · have he : independentCachedBranchMembers3983.filter (independentCachedEdge 1626)=independentCachedBranchMembers3982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3982
def independentCachedBranchMembers3984 : Finset ℕ := ([12,130,144,192,1596,1614,1644,1714,1746,1762,1776,2606,2620,2638,2652,2668,2738,2770,2786,2800,3102,3118,3164,3180,3250,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3984 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3984 5 (fun x => (if x<2652 then (if x<1714 then (if x<192 then (if x<130 then 0 else (if x<144 then 0 else 1)) else (if x<1614 then (if x<1596 then 2 else 0) else (if x<1644 then 1 else 3))) else (if x<1776 then (if x<1746 then 0 else (if x<1762 then 1 else 2)) else (if x<2620 then (if x<2606 then 3 else 1) else (if x<2638 then 2 else 3)))) else (if x<3118 then (if x<2770 then (if x<2668 then 0 else (if x<2738 then 4 else 1)) else (if x<2800 then (if x<2786 then 0 else 4) else (if x<3102 then 2 else 2))) else (if x<3250 then (if x<3164 then 3 else (if x<3180 then 4 else 0)) else (if x<3298 then (if x<3282 then 3 else 2) else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3985 : Finset ℕ := ([130,1596,1614,1644,1746,1776,2606,2652,2738,2786,3118,3164,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3985 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3985 4 (fun x => (if x<2652 then (if x<1644 then (if x<1596 then 0 else (if x<1614 then 0 else 1)) else (if x<1776 then (if x<1746 then 2 else 1) else (if x<2606 then 2 else 1))) else (if x<3118 then (if x<2738 then 0 else (if x<2786 then 1 else 3)) else (if x<3250 then (if x<3164 then 2 else 3) else (if x<3298 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3986 : Finset ℕ := ([12,130,144,192,1582,1596,1614,1644,1714,1746,1762,1776,2606,2620,2638,2652,2668,2738,2770,2786,2800,3102,3118,3164,3180,3250,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3986 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3986 1582 4
  · have he : independentCachedBranchMembers3986.erase 1582=independentCachedBranchMembers3984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3984
  · have he : independentCachedBranchMembers3986.filter (independentCachedEdge 1582)=independentCachedBranchMembers3985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3985
def independentCachedBranchMembers3987 : Finset ℕ := ([144,1596,1614,1714,1776,2620,2638,2738,2800,3102,3118,3164,3180,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3987 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3987 4 (fun x => (if x<2738 then (if x<1714 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<2620 then (if x<1776 then 1 else 2) else (if x<2638 then 3 else 2))) else (if x<3164 then (if x<3102 then (if x<2800 then 0 else 3) else (if x<3118 then 2 else 3)) else (if x<3282 then (if x<3180 then 1 else 0) else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3988 : Finset ℕ := ([12,130,144,192,1582,1596,1614,1644,1714,1746,1762,1776,2606,2620,2638,2652,2668,2738,2770,2786,2800,3102,3118,3132,3164,3180,3250,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3988 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3988 3132 4
  · have he : independentCachedBranchMembers3988.erase 3132=independentCachedBranchMembers3986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3986
  · have he : independentCachedBranchMembers3988.filter (independentCachedEdge 3132)=independentCachedBranchMembers3987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3987
def independentCachedBranchMembers3989 : Finset ℕ := ([144,1596,1614,1644,1714,1762,2606,2652,2770,2800,3118,3164,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3989 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3989 4 (fun x => (if x<2652 then (if x<1644 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1762 then (if x<1714 then 2 else 1) else (if x<2606 then 2 else 0))) else (if x<3118 then (if x<2770 then 1 else (if x<2800 then 1 else 3)) else (if x<3282 then (if x<3164 then 3 else 2) else (if x<3312 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3990 : Finset ℕ := ([144,1614,1644,1714,2652,3164] : List ℕ).toFinset
theorem independentCachedBranchBound3990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3990 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3990 3 (fun x => (if x<1714 then (if x<1614 then 0 else (if x<1644 then 0 else 1)) else (if x<2652 then 2 else (if x<3164 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3991 : Finset ℕ := ([144,192,1596,1614,1644,1714,1762,2606,2652,2770,2800,3118,3164,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3991 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3991 192 3
  · have he : independentCachedBranchMembers3991.erase 192=independentCachedBranchMembers3989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3989
  · have he : independentCachedBranchMembers3991.filter (independentCachedEdge 192)=independentCachedBranchMembers3990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3990
def independentCachedBranchMembers3992 : Finset ℕ := ([12,130,144,192,1582,1596,1614,1628,1644,1714,1746,1762,1776,2606,2620,2638,2652,2668,2738,2770,2786,2800,3102,3118,3132,3164,3180,3250,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3992 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3992 1628 4
  · have he : independentCachedBranchMembers3992.erase 1628=independentCachedBranchMembers3988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3988
  · have he : independentCachedBranchMembers3992.filter (independentCachedEdge 1628)=independentCachedBranchMembers3991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3991
def independentCachedBranchMembers3993 : Finset ℕ := ([130,192,1596,1614,1746,1762,2620,2638,2770,2786,3102,3118,3164,3180,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3993 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3993 4 (fun x => (if x<2770 then (if x<1746 then (if x<1596 then (if x<192 then 0 else 1) else (if x<1614 then 0 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2638 then 1 else 3))) else (if x<3164 then (if x<3102 then (if x<2786 then 0 else 3) else (if x<3118 then 2 else 1)) else (if x<3250 then (if x<3180 then 3 else 0) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3994 : Finset ℕ := ([12,130,144,192,1582,1596,1614,1628,1644,1714,1746,1762,1776,2606,2620,2638,2652,2668,2738,2770,2786,2800,3102,3118,3132,3150,3164,3180,3250,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3994 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3994 3150 4
  · have he : independentCachedBranchMembers3994.erase 3150=independentCachedBranchMembers3992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3992
  · have he : independentCachedBranchMembers3994.filter (independentCachedEdge 3150)=independentCachedBranchMembers3993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3993
def independentCachedBranchMembers3995 : Finset ℕ := ([12,40,130,132,144,192,246,1582,1594,1596,1614,1626,1628,1642,1644,1686,1702,1714,1734,1746,1748,1762,1764,1776,2606,2618,2620,2638,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3995 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3995 132 5
  · have he : independentCachedBranchMembers3995.erase 132=independentCachedBranchMembers3983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3983
  · have he : independentCachedBranchMembers3995.filter (independentCachedEdge 132)=independentCachedBranchMembers3994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3994
def independentCachedBranchMembers3996 : Finset ℕ := ([12,40,192,246,1582,1594,1734,1746,1762,1776,2618,2620,2770,2772,2786,2788,2800,3102,3118,3132,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3996 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3996 5 (fun x => (if x<2770 then (if x<1734 then (if x<246 then (if x<40 then 0 else (if x<192 then 1 else 0)) else (if x<1582 then 2 else (if x<1594 then 0 else 1))) else (if x<1776 then (if x<1746 then 2 else (if x<1762 then 1 else 0)) else (if x<2618 then 2 else (if x<2620 then 3 else 0)))) else (if x<3118 then (if x<2788 then (if x<2772 then 2 else (if x<2786 then 1 else 3)) else (if x<2800 then 2 else (if x<3102 then 0 else 0))) else (if x<3282 then (if x<3132 then 1 else (if x<3270 then 3 else 1)) else (if x<3300 then (if x<3284 then 0 else 2) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3997 : Finset ℕ := ([246,1582,1734,1762,2618,2620,2770,2772,2800,3118,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3997 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3997 4 (fun x => (if x<2770 then (if x<1762 then (if x<1582 then 0 else (if x<1734 then 1 else 0)) else (if x<2618 then 1 else (if x<2620 then 2 else 1))) else (if x<3118 then (if x<2772 then 0 else (if x<2800 then 3 else 1)) else (if x<3270 then 2 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3998 : Finset ℕ := ([12,40,192,246,1582,1594,1734,1746,1762,1776,2606,2618,2620,2770,2772,2786,2788,2800,3102,3118,3132,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3998 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3998 2606 4
  · have he : independentCachedBranchMembers3998.erase 2606=independentCachedBranchMembers3996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3996
  · have he : independentCachedBranchMembers3998.filter (independentCachedEdge 2606)=independentCachedBranchMembers3997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3997
def independentCachedBranchMembers3999 : Finset ℕ := ([12,1582,1594,1734,1746,1776,2620,2772,2786,3102,3132,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3999 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3999 4 (fun x => (if x<2620 then (if x<1734 then (if x<1582 then 0 else (if x<1594 then 0 else 1)) else (if x<1746 then 2 else (if x<1776 then 1 else 2))) else (if x<3102 then (if x<2772 then 0 else (if x<2786 then 1 else 2)) else (if x<3132 then 0 else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
