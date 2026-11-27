/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch37
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4000 : Finset ℕ := ([12,40,192,246,1582,1594,1734,1746,1748,1762,1776,2606,2618,2620,2770,2772,2786,2788,2800,3102,3118,3132,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4000 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4000 1748 4
  · have he : independentCachedBranchMembers4000.erase 1748=independentCachedBranchMembers3998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3998
  · have he : independentCachedBranchMembers4000.filter (independentCachedEdge 1748)=independentCachedBranchMembers3999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3999
def independentCachedBranchMembers4001 : Finset ℕ := ([12,1582,1734,1776,2620,2770,2772,2786,2788,3102,3118,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4001 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4001 4 (fun x => (if x<2772 then (if x<1776 then (if x<1582 then 0 else (if x<1734 then 0 else 1)) else (if x<2620 then 1 else (if x<2770 then 0 else 1))) else (if x<3102 then (if x<2786 then 2 else (if x<2788 then 2 else 1)) else (if x<3270 then (if x<3118 then 0 else 3) else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4002 : Finset ℕ := ([12,1776,2620,2772,2788,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4002 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4002 3 (fun x => (if x<2772 then (if x<1776 then 0 else (if x<2620 then 0 else 1)) else (if x<2788 then 1 else (if x<3312 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4003 : Finset ℕ := ([12,1582,1734,1776,2618,2620,2770,2772,2786,2788,3102,3118,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4003 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4003 2618 3
  · have he : independentCachedBranchMembers4003.erase 2618=independentCachedBranchMembers4001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4001
  · have he : independentCachedBranchMembers4003.filter (independentCachedEdge 2618)=independentCachedBranchMembers4002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4002
def independentCachedBranchMembers4004 : Finset ℕ := ([12,40,192,246,1582,1594,1734,1746,1748,1762,1776,2606,2618,2620,2758,2770,2772,2786,2788,2800,3102,3118,3132,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4004 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4004 2758 4
  · have he : independentCachedBranchMembers4004.erase 2758=independentCachedBranchMembers4000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4000
  · have he : independentCachedBranchMembers4004.filter (independentCachedEdge 2758)=independentCachedBranchMembers4003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4003
def independentCachedBranchMembers4005 : Finset ℕ := ([246,1582,1594,1734,1746,1762,2620,2772,2788,2800,3132,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4005 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4005 4 (fun x => (if x<2772 then (if x<1734 then (if x<1582 then 0 else (if x<1594 then 1 else 2)) else (if x<1762 then (if x<1746 then 0 else 2) else (if x<2620 then 1 else 1))) else (if x<3132 then (if x<2788 then 0 else (if x<2800 then 3 else 1)) else (if x<3300 then (if x<3284 then 2 else 2) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4006 : Finset ℕ := ([12,40,192,246,1582,1594,1596,1734,1746,1748,1762,1776,2606,2618,2620,2758,2770,2772,2786,2788,2800,3102,3118,3132,3270,3282,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4006 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4006 1596 4
  · have he : independentCachedBranchMembers4006.erase 1596=independentCachedBranchMembers4004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4004
  · have he : independentCachedBranchMembers4006.filter (independentCachedEdge 1596)=independentCachedBranchMembers4005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4005
def independentCachedBranchMembers4007 : Finset ℕ := ([40,1594,1748,1762,2606,2618,2772,2786,3102,3132,3270,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4007 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4007 4 (fun x => (if x<2786 then (if x<1762 then (if x<1594 then 0 else (if x<1748 then 0 else 1)) else (if x<2618 then (if x<2606 then 1 else 0) else (if x<2772 then 2 else 3))) else (if x<3270 then (if x<3102 then 2 else (if x<3132 then 2 else 0)) else (if x<3300 then (if x<3282 then 1 else 3) else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4008 : Finset ℕ := ([1594,1748,2606,2786,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4008 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4008 3 (fun x => (if x<2786 then (if x<1748 then 0 else (if x<2606 then 1 else 0)) else (if x<3270 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4009 : Finset ℕ := ([40,1582,1594,1748,1762,2606,2618,2772,2786,3102,3132,3270,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4009 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4009 1582 3
  · have he : independentCachedBranchMembers4009.erase 1582=independentCachedBranchMembers4007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4007
  · have he : independentCachedBranchMembers4009.filter (independentCachedEdge 1582)=independentCachedBranchMembers4008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4008
def independentCachedBranchMembers4010 : Finset ℕ := ([12,40,192,246,1582,1594,1596,1734,1746,1748,1762,1776,2606,2618,2620,2758,2770,2772,2786,2788,2800,3102,3118,3132,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4010 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4010 3298 4
  · have he : independentCachedBranchMembers4010.erase 3298=independentCachedBranchMembers4006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4006
  · have he : independentCachedBranchMembers4010.filter (independentCachedEdge 3298)=independentCachedBranchMembers4009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4009
def independentCachedBranchMembers4011 : Finset ℕ := ([12,40,1594,1734,1748,1762,1776,2606,2620,2770,2788,3118,3132,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4011 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4011 4 (fun x => (if x<2606 then (if x<1734 then (if x<40 then 0 else (if x<1594 then 1 else 1)) else (if x<1762 then (if x<1748 then 2 else 3) else (if x<1776 then 0 else 2))) else (if x<3118 then (if x<2770 then (if x<2620 then 1 else 0) else (if x<2788 then 2 else 2)) else (if x<3282 then (if x<3132 then 3 else 1) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4012 : Finset ℕ := ([12,40,192,246,1582,1594,1596,1734,1746,1748,1762,1764,1776,2606,2618,2620,2758,2770,2772,2786,2788,2800,3102,3118,3132,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4012 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4012 1764 4
  · have he : independentCachedBranchMembers4012.erase 1764=independentCachedBranchMembers4010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4010
  · have he : independentCachedBranchMembers4012.filter (independentCachedEdge 1764)=independentCachedBranchMembers4011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4011
def independentCachedBranchMembers4013 : Finset ℕ := ([12,246,1594,1746,1762,1776,2618,2770,2786,2800,3102,3118,3132,3270,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4013 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4013 4 (fun x => (if x<2786 then (if x<1762 then (if x<1594 then (if x<246 then 0 else 1) else (if x<1746 then 2 else 0)) else (if x<2618 then (if x<1776 then 1 else 2) else (if x<2770 then 3 else 1))) else (if x<3132 then (if x<3102 then (if x<2800 then 0 else 3) else (if x<3118 then 2 else 3)) else (if x<3284 then (if x<3270 then 0 else 1) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4014 : Finset ℕ := ([12,40,192,246,1582,1594,1596,1734,1746,1748,1762,1764,1776,2606,2618,2620,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4014 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4014 3130 4
  · have he : independentCachedBranchMembers4014.erase 3130=independentCachedBranchMembers4012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4012
  · have he : independentCachedBranchMembers4014.filter (independentCachedEdge 3130)=independentCachedBranchMembers4013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4013
def independentCachedBranchMembers4015 : Finset ℕ := ([12,40,72,130,132,144,192,246,1582,1594,1596,1614,1626,1628,1642,1644,1686,1702,1714,1734,1746,1748,1762,1764,1776,2606,2618,2620,2638,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4015 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4015 72 5
  · have he : independentCachedBranchMembers4015.erase 72=independentCachedBranchMembers3995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3995
  · have he : independentCachedBranchMembers4015.filter (independentCachedEdge 72)=independentCachedBranchMembers4014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4014
def independentCachedBranchMembers4016 : Finset ℕ := ([144,192,246,1582,1626,1644,1686,1734,1748,1762,1776,2606,2620,2650,2710,2738,2758,2772,2800,3102,3130,3150,3178,3192,3238,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4016 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4016 5 (fun x => (if x<2710 then (if x<1734 then (if x<1582 then (if x<192 then 0 else (if x<246 then 1 else 0)) else (if x<1644 then (if x<1626 then 1 else 2) else (if x<1686 then 2 else 0))) else (if x<1776 then (if x<1748 then 1 else (if x<1762 then 2 else 2)) else (if x<2620 then (if x<2606 then 0 else 3) else (if x<2650 then 1 else 3)))) else (if x<3150 then (if x<2772 then (if x<2738 then 3 else (if x<2758 then 0 else 4)) else (if x<3102 then (if x<2800 then 0 else 4) else (if x<3130 then 3 else 1))) else (if x<3238 then (if x<3178 then 4 else (if x<3192 then 2 else 4)) else (if x<3282 then (if x<3252 then 3 else 0) else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4017 : Finset ℕ := ([246,1626,1762,1776,2650,2738,2800,3102,3150,3238,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4017 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4017 4 (fun x => (if x<2800 then (if x<1776 then (if x<1626 then 0 else (if x<1762 then 1 else 0)) else (if x<2650 then 1 else (if x<2738 then 2 else 0))) else (if x<3238 then (if x<3102 then 2 else (if x<3150 then 1 else 2)) else (if x<3252 then 0 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4018 : Finset ℕ := ([40,144,192,246,1582,1626,1644,1686,1734,1748,1762,1776,2606,2620,2650,2710,2738,2758,2772,2800,3102,3130,3150,3178,3192,3238,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4018 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4018 40 4
  · have he : independentCachedBranchMembers4018.erase 40=independentCachedBranchMembers4016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4016
  · have he : independentCachedBranchMembers4018.filter (independentCachedEdge 40)=independentCachedBranchMembers4017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4017
def independentCachedBranchMembers4019 : Finset ℕ := ([40,144,192,246,1582,1686,1734,1776,2606,2710,2758,2800,3102,3150,3192,3238] : List ℕ).toFinset
theorem independentCachedBranchBound4019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4019 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4019 4 (fun x => (if x<2606 then (if x<1582 then (if x<192 then (if x<144 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1734 then (if x<1686 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3102 then (if x<2758 then (if x<2710 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3192 then (if x<3150 then 2 else 3) else (if x<3238 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4020 : Finset ℕ := ([40,144,192,246,1582,1626,1644,1686,1734,1748,1762,1776,2606,2620,2650,2710,2738,2758,2772,2800,3102,3130,3150,3164,3178,3192,3238,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4020 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4020 3164 4
  · have he : independentCachedBranchMembers4020.erase 3164=independentCachedBranchMembers4018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4018
  · have he : independentCachedBranchMembers4020.filter (independentCachedEdge 3164)=independentCachedBranchMembers4019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4019
def independentCachedBranchMembers4021 : Finset ℕ := ([40,144,1582,1626,1644,1686,1748,1762,2620,2738,2758,2800,3130,3150,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound4021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4021 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4021 4 (fun x => (if x<2620 then (if x<1644 then (if x<1582 then (if x<144 then 0 else 0) else (if x<1626 then 0 else 1)) else (if x<1748 then (if x<1686 then 1 else 0) else (if x<1762 then 1 else 1))) else (if x<3130 then (if x<2758 then (if x<2738 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3192 then (if x<3150 then 2 else 3) else (if x<3252 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4022 : Finset ℕ := ([40,144,192,246,1582,1626,1644,1686,1734,1748,1762,1776,2606,2620,2650,2710,2738,2758,2772,2786,2800,3102,3130,3150,3164,3178,3192,3238,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4022 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4022 2786 4
  · have he : independentCachedBranchMembers4022.erase 2786=independentCachedBranchMembers4020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4020
  · have he : independentCachedBranchMembers4022.filter (independentCachedEdge 2786)=independentCachedBranchMembers4021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4021
def independentCachedBranchMembers4023 : Finset ℕ := ([192,246,1626,1644,1734,1748,1762,1776,2606,2620,2710,2738,3102,3130,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound4023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4023 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4023 4 (fun x => (if x<2606 then (if x<1734 then (if x<1626 then (if x<246 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<1762 then (if x<1748 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3102 then (if x<2710 then (if x<2620 then 2 else 3) else (if x<2738 then 2 else 3)) else (if x<3238 then (if x<3130 then 2 else 3) else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4024 : Finset ℕ := ([40,144,192,246,1582,1626,1644,1686,1734,1748,1762,1776,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3102,3130,3150,3164,3178,3192,3238,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4024 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4024 2668 4
  · have he : independentCachedBranchMembers4024.erase 2668=independentCachedBranchMembers4022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4022
  · have he : independentCachedBranchMembers4024.filter (independentCachedEdge 2668)=independentCachedBranchMembers4023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4023
def independentCachedBranchMembers4025 : Finset ℕ := ([192,1644,1686,1762,1776,2606,2620,2650,2738,2758,2772,3102,3178,3192,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4025 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4025 4 (fun x => (if x<2650 then (if x<1762 then (if x<1644 then 0 else (if x<1686 then 1 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2620 then 1 else 0))) else (if x<3102 then (if x<2758 then (if x<2738 then 3 else 1) else (if x<2772 then 2 else 3)) else (if x<3192 then (if x<3178 then 0 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4026 : Finset ℕ := ([1762,1776,2650,2738,3102,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4026 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4026 3 (fun x => (if x<2738 then (if x<1776 then 0 else (if x<2650 then 1 else 2)) else (if x<3102 then 0 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4027 : Finset ℕ := ([40,192,1644,1686,1762,1776,2606,2620,2650,2738,2758,2772,3102,3178,3192,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4027 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4027 40 3
  · have he : independentCachedBranchMembers4027.erase 40=independentCachedBranchMembers4025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4025
  · have he : independentCachedBranchMembers4027.filter (independentCachedEdge 40)=independentCachedBranchMembers4026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4026
def independentCachedBranchMembers4028 : Finset ℕ := ([40,144,192,246,1582,1626,1644,1686,1714,1734,1748,1762,1776,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3102,3130,3150,3164,3178,3192,3238,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4028 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4028 1714 4
  · have he : independentCachedBranchMembers4028.erase 1714=independentCachedBranchMembers4024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4024
  · have he : independentCachedBranchMembers4028.filter (independentCachedEdge 1714)=independentCachedBranchMembers4027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4027
def independentCachedBranchMembers4029 : Finset ℕ := ([246,1582,1644,1734,1762,2620,2650,2710,2738,2772,2800,3150,3178,3238,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4029 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4029 4 (fun x => (if x<2710 then (if x<1734 then (if x<1582 then 0 else (if x<1644 then 1 else 2)) else (if x<2620 then (if x<1762 then 0 else 1) else (if x<2650 then 1 else 3))) else (if x<3150 then (if x<2772 then (if x<2738 then 0 else 2) else (if x<2800 then 3 else 1)) else (if x<3238 then (if x<3178 then 2 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4030 : Finset ℕ := ([1734,1762,2620,2650,3238,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4030 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4030 3 (fun x => (if x<2650 then (if x<1762 then 0 else (if x<2620 then 1 else 0)) else (if x<3238 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4031 : Finset ℕ := ([144,246,1582,1644,1734,1762,2620,2650,2710,2738,2772,2800,3150,3178,3238,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4031 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4031 144 3
  · have he : independentCachedBranchMembers4031.erase 144=independentCachedBranchMembers4029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4029
  · have he : independentCachedBranchMembers4031.filter (independentCachedEdge 144)=independentCachedBranchMembers4030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4030
end EntropyDesigns.QuadraticRefinement
