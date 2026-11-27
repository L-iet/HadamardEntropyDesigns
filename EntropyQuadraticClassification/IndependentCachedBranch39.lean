/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch38
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4032 : Finset ℕ := ([40,144,192,246,1582,1596,1626,1644,1686,1714,1734,1748,1762,1776,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3102,3130,3150,3164,3178,3192,3238,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4032 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4032 1596 4
  · have he : independentCachedBranchMembers4032.erase 1596=independentCachedBranchMembers4028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4028
  · have he : independentCachedBranchMembers4032.filter (independentCachedEdge 1596)=independentCachedBranchMembers4031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4031
def independentCachedBranchMembers4033 : Finset ℕ := ([144,192,1582,1626,1748,1776,2606,2650,2772,2800,3102,3130,3150,3178,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4033 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4033 4 (fun x => (if x<2772 then (if x<1748 then (if x<1582 then (if x<192 then 0 else 1) else (if x<1626 then 0 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2650 then 1 else 3))) else (if x<3150 then (if x<3102 then (if x<2800 then 0 else 3) else (if x<3130 then 2 else 1)) else (if x<3252 then (if x<3178 then 3 else 0) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4034 : Finset ℕ := ([40,130,144,192,246,1582,1596,1626,1644,1686,1714,1734,1748,1762,1776,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3102,3130,3150,3164,3178,3192,3238,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4034 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4034 130 4
  · have he : independentCachedBranchMembers4034.erase 130=independentCachedBranchMembers4032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4032
  · have he : independentCachedBranchMembers4034.filter (independentCachedEdge 130)=independentCachedBranchMembers4033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4033
def independentCachedBranchMembers4035 : Finset ℕ := ([40,246,1626,1686,1734,1748,2650,2710,2758,2772,3130,3178,3192,3238,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4035 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4035 4 (fun x => (if x<2758 then (if x<1734 then (if x<1626 then (if x<246 then 0 else 1) else (if x<1686 then 2 else 0)) else (if x<2650 then (if x<1748 then 1 else 2) else (if x<2710 then 3 else 1))) else (if x<3192 then (if x<3130 then (if x<2772 then 0 else 3) else (if x<3178 then 2 else 3)) else (if x<3252 then (if x<3238 then 0 else 1) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4036 : Finset ℕ := ([12,40,130,144,192,246,1582,1596,1626,1644,1686,1714,1734,1748,1762,1776,2606,2620,2650,2668,2710,2738,2758,2772,2786,2800,3102,3130,3150,3164,3178,3192,3238,3252,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4036 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4036 12 4
  · have he : independentCachedBranchMembers4036.erase 12=independentCachedBranchMembers4034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4034
  · have he : independentCachedBranchMembers4036.filter (independentCachedEdge 12)=independentCachedBranchMembers4035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4035
def independentCachedBranchMembers4037 : Finset ℕ := ([12,40,72,130,132,144,192,246,1582,1594,1596,1614,1626,1628,1642,1644,1686,1702,1714,1734,1746,1748,1762,1764,1776,2606,2618,2620,2638,2650,2652,2668,2680,2710,2738,2740,2758,2770,2772,2786,2788,2800,3102,3118,3130,3132,3150,3162,3164,3178,3180,3192,3222,3238,3250,3252,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4037 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4037 3162 5
  · have he : independentCachedBranchMembers4037.erase 3162=independentCachedBranchMembers4015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4015
  · have he : independentCachedBranchMembers4037.filter (independentCachedEdge 3162)=independentCachedBranchMembers4036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4036
def independentCachedBranchMembers4038 : Finset ℕ := ([12,18,36,40,48,66,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4038 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4038 136 6
  · have he : independentCachedBranchMembers4038.erase 136=independentCachedBranchMembers3830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3830
  · have he : independentCachedBranchMembers4038.filter (independentCachedEdge 136)=independentCachedBranchMembers4037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4037
def independentCachedBranchMembers4039 : Finset ℕ := ([36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2680,2732,2762,2770,2786,3118,3132,3186,3238,3274,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4039 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4039 6 (fun x => (if x<1776 then (if x<1626 then (if x<192 then (if x<66 then 0 else (if x<80 then 0 else 1)) else (if x<1590 then (if x<250 then 2 else 1) else (if x<1596 then 2 else 0))) else (if x<1708 then (if x<1642 then 0 else (if x<1678 then 3 else 3)) else (if x<1752 then (if x<1746 then 4 else 1) else (if x<1762 then 3 else 2)))) else (if x<3118 then (if x<2732 then (if x<2606 then 4 else (if x<2680 then 3 else 3)) else (if x<2770 then (if x<2762 then 0 else 0) else (if x<2786 then 4 else 5))) else (if x<3238 then (if x<3132 then 4 else (if x<3186 then 2 else 1)) else (if x<3282 then (if x<3274 then 5 else 5) else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4040 : Finset ℕ := ([36,250,1590,1626,1642,1752,2680,2762,3238,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4040 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4040 5 (fun x => (if x<1752 then (if x<1590 then (if x<250 then 0 else 1) else (if x<1626 then 0 else (if x<1642 then 0 else 1))) else (if x<3238 then (if x<2680 then 1 else (if x<2762 then 1 else 0)) else (if x<3274 then 2 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4041 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2680,2732,2762,2770,2786,3118,3132,3186,3238,3274,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4041 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4041 12 5
  · have he : independentCachedBranchMembers4041.erase 12=independentCachedBranchMembers4039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4039
  · have he : independentCachedBranchMembers4041.filter (independentCachedEdge 12)=independentCachedBranchMembers4040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4040
def independentCachedBranchMembers4042 : Finset ℕ := ([12,66,1596,1642,1678,1708,1752,1762,2732,2786,3118,3238,3274,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4042 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4042 5 (fun x => (if x<1762 then (if x<1642 then (if x<66 then 0 else (if x<1596 then 0 else 0)) else (if x<1708 then (if x<1678 then 1 else 1) else (if x<1752 then 2 else 1))) else (if x<3238 then (if x<2786 then (if x<2732 then 2 else 0) else (if x<3118 then 0 else 1)) else (if x<3282 then (if x<3274 then 2 else 1) else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4043 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2680,2732,2762,2770,2786,3118,3132,3186,3238,3274,3282,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4043 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4043 3288 5
  · have he : independentCachedBranchMembers4043.erase 3288=independentCachedBranchMembers4041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4041
  · have he : independentCachedBranchMembers4043.filter (independentCachedEdge 3288)=independentCachedBranchMembers4042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4042
def independentCachedBranchMembers4044 : Finset ℕ := ([12,80,192,250,1678,1746,1752,1762,2606,2680,2770,2786,3132,3238,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4044 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4044 5 (fun x => (if x<1762 then (if x<250 then (if x<80 then 0 else (if x<192 then 0 else 1)) else (if x<1746 then (if x<1678 then 1 else 0) else (if x<1752 then 0 else 1))) else (if x<2786 then (if x<2680 then (if x<2606 then 1 else 0) else (if x<2770 then 2 else 1)) else (if x<3238 then (if x<3132 then 2 else 2) else (if x<3274 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4045 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2680,2732,2762,2770,2786,3118,3132,3186,3238,3252,3274,3282,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4045 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4045 3252 5
  · have he : independentCachedBranchMembers4045.erase 3252=independentCachedBranchMembers4043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4043
  · have he : independentCachedBranchMembers4045.filter (independentCachedEdge 3252)=independentCachedBranchMembers4044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4044
def independentCachedBranchMembers4046 : Finset ℕ := ([36,66,80,250,1642,1708,1746,1752,2680,2732,2762,2770,3118,3132,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4046 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4046 5 (fun x => (if x<1752 then (if x<250 then (if x<66 then 0 else (if x<80 then 0 else 1)) else (if x<1708 then (if x<1642 then 1 else 2) else (if x<1746 then 0 else 1))) else (if x<2770 then (if x<2732 then (if x<2680 then 2 else 2) else (if x<2762 then 3 else 2)) else (if x<3132 then (if x<3118 then 0 else 3) else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4047 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2680,2732,2762,2770,2786,3102,3118,3132,3186,3238,3252,3274,3282,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4047 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4047 3102 5
  · have he : independentCachedBranchMembers4047.erase 3102=independentCachedBranchMembers4045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4045
  · have he : independentCachedBranchMembers4047.filter (independentCachedEdge 3102)=independentCachedBranchMembers4046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4046
def independentCachedBranchMembers4048 : Finset ℕ := ([36,66,1590,1596,1626,1642,1708,1776,2606,2680,2770,2786,3132,3238,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4048 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4048 5 (fun x => (if x<1776 then (if x<1596 then (if x<66 then 0 else (if x<1590 then 0 else 1)) else (if x<1642 then (if x<1626 then 0 else 0) else (if x<1708 then 1 else 1))) else (if x<2786 then (if x<2680 then (if x<2606 then 1 else 1) else (if x<2770 then 2 else 0)) else (if x<3238 then (if x<3132 then 2 else 2) else (if x<3274 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4049 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2680,2732,2762,2770,2786,2800,3102,3118,3132,3186,3238,3252,3274,3282,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4049 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4049 2800 5
  · have he : independentCachedBranchMembers4049.erase 2800=independentCachedBranchMembers4047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4047
  · have he : independentCachedBranchMembers4049.filter (independentCachedEdge 2800)=independentCachedBranchMembers4048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4048
def independentCachedBranchMembers4050 : Finset ℕ := ([36,80,192,250,1590,1626,1746,1776,2732,2786,3118,3238,3274,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4050 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4050 5 (fun x => (if x<1776 then (if x<250 then (if x<80 then 0 else (if x<192 then 0 else 1)) else (if x<1626 then (if x<1590 then 1 else 2) else (if x<1746 then 0 else 1))) else (if x<3238 then (if x<2786 then (if x<2732 then 2 else 0) else (if x<3118 then 1 else 2)) else (if x<3282 then (if x<3274 then 0 else 1) else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4051 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2680,2716,2732,2762,2770,2786,2800,3102,3118,3132,3186,3238,3252,3274,3282,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4051 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4051 2716 5
  · have he : independentCachedBranchMembers4051.erase 2716=independentCachedBranchMembers4049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4049
  · have he : independentCachedBranchMembers4051.filter (independentCachedEdge 2716)=independentCachedBranchMembers4050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4050
def independentCachedBranchMembers4052 : Finset ℕ := ([12,192,1590,1596,1626,1678,1762,1776,2680,2732,2762,2770,3118,3132,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4052 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4052 5 (fun x => (if x<1776 then (if x<1596 then (if x<192 then 0 else (if x<1590 then 0 else 1)) else (if x<1678 then (if x<1626 then 0 else 1) else (if x<1762 then 1 else 1))) else (if x<2770 then (if x<2732 then (if x<2680 then 0 else 2) else (if x<2762 then 2 else 1)) else (if x<3132 then (if x<3118 then 0 else 0) else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4053 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2650,2680,2716,2732,2762,2770,2786,2800,3102,3118,3132,3186,3238,3252,3274,3282,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4053 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4053 2650 5
  · have he : independentCachedBranchMembers4053.erase 2650=independentCachedBranchMembers4051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4051
  · have he : independentCachedBranchMembers4053.filter (independentCachedEdge 2650)=independentCachedBranchMembers4052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4052
def independentCachedBranchMembers4054 : Finset ℕ := ([36,66,1590,1596,1626,1642,1708,1776,2650,2716,2732,2762,2800,3102,3118,3186,3252,3282,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4054 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4054 5 (fun x => (if x<2732 then (if x<1642 then (if x<1590 then (if x<66 then 0 else 0) else (if x<1596 then 1 else (if x<1626 then 0 else 0))) else (if x<1776 then (if x<1708 then 1 else 1) else (if x<2650 then 1 else (if x<2716 then 2 else 2)))) else (if x<3186 then (if x<2800 then (if x<2762 then 0 else 0) else (if x<3102 then 2 else (if x<3118 then 2 else 1))) else (if x<3282 then (if x<3252 then 1 else 0) else (if x<3288 then 0 else (if x<3304 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4055 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2650,2680,2716,2732,2762,2770,2786,2800,3102,3118,3132,3186,3238,3252,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4055 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4055 3312 5
  · have he : independentCachedBranchMembers4055.erase 3312=independentCachedBranchMembers4053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4053
  · have he : independentCachedBranchMembers4055.filter (independentCachedEdge 3312)=independentCachedBranchMembers4054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4054
def independentCachedBranchMembers4056 : Finset ℕ := ([192,250,1590,1642,1708,1752,1762,1776,2680,2732,2762,2786,2800,3118,3132,3186,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4056 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4056 5 (fun x => (if x<2762 then (if x<1752 then (if x<1590 then (if x<250 then 0 else 0) else (if x<1642 then 1 else (if x<1708 then 1 else 1))) else (if x<1776 then (if x<1762 then 0 else 0) else (if x<2680 then 1 else (if x<2732 then 2 else 2)))) else (if x<3186 then (if x<2800 then (if x<2786 then 0 else 2) else (if x<3118 then 0 else (if x<3132 then 1 else 2))) else (if x<3252 then (if x<3238 then 1 else 2) else (if x<3282 then 1 else (if x<3304 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4057 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2650,2680,2716,2732,2762,2770,2786,2800,3102,3118,3132,3186,3238,3244,3252,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4057 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4057 3244 5
  · have he : independentCachedBranchMembers4057.erase 3244=independentCachedBranchMembers4055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4055
  · have he : independentCachedBranchMembers4057.filter (independentCachedEdge 3244)=independentCachedBranchMembers4056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4056
def independentCachedBranchMembers4058 : Finset ℕ := ([12,36,66,80,1596,1626,1678,1746,2680,2732,2762,2786,2800,3118,3132,3186,3238,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4058 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4058 5 (fun x => (if x<2762 then (if x<1626 then (if x<66 then (if x<36 then 0 else 1) else (if x<80 then 0 else (if x<1596 then 1 else 0))) else (if x<1746 then (if x<1678 then 1 else 2) else (if x<2680 then 2 else (if x<2732 then 3 else 0)))) else (if x<3186 then (if x<2800 then (if x<2786 then 2 else 0) else (if x<3118 then 2 else (if x<3132 then 4 else 3))) else (if x<3252 then (if x<3238 then 3 else 1) else (if x<3282 then 4 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4059 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2650,2680,2716,2732,2762,2770,2786,2792,2800,3102,3118,3132,3186,3238,3244,3252,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4059 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4059 2792 5
  · have he : independentCachedBranchMembers4059.erase 2792=independentCachedBranchMembers4057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4057
  · have he : independentCachedBranchMembers4059.filter (independentCachedEdge 2792)=independentCachedBranchMembers4058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4058
def independentCachedBranchMembers4060 : Finset ℕ := ([12,80,192,250,1678,1746,1752,1762,2650,2716,2732,2762,2800,3102,3118,3186,3252,3282,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4060 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4060 5 (fun x => (if x<2732 then (if x<1746 then (if x<192 then (if x<80 then 0 else 0) else (if x<250 then 1 else (if x<1678 then 1 else 0))) else (if x<1762 then (if x<1752 then 0 else 1) else (if x<2650 then 1 else (if x<2716 then 2 else 2)))) else (if x<3186 then (if x<2800 then (if x<2762 then 0 else 1) else (if x<3102 then 0 else (if x<3118 then 2 else 0))) else (if x<3282 then (if x<3252 then 0 else 2) else (if x<3288 then 1 else (if x<3304 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4061 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2650,2680,2716,2732,2740,2762,2770,2786,2792,2800,3102,3118,3132,3186,3238,3244,3252,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4061 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4061 2740 5
  · have he : independentCachedBranchMembers4061.erase 2740=independentCachedBranchMembers4059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4059
  · have he : independentCachedBranchMembers4061.filter (independentCachedEdge 2740)=independentCachedBranchMembers4060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4060
def independentCachedBranchMembers4062 : Finset ℕ := ([36,192,1596,1752,2650,2680,2716,2732,2770,2786,2800,3102,3118,3132,3186,3238,3252,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4062 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4062 5 (fun x => (if x<2800 then (if x<2680 then (if x<1596 then (if x<192 then 0 else 0) else (if x<1752 then 0 else (if x<2650 then 0 else 1))) else (if x<2732 then (if x<2716 then 2 else 1) else (if x<2770 then 2 else (if x<2786 then 0 else 2)))) else (if x<3238 then (if x<3118 then (if x<3102 then 1 else 1) else (if x<3132 then 0 else (if x<3186 then 2 else 1))) else (if x<3274 then (if x<3252 then 2 else 1) else (if x<3288 then 0 else (if x<3304 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4063 : Finset ℕ := ([12,36,66,80,192,250,1590,1596,1626,1642,1678,1708,1746,1752,1762,1776,2606,2650,2674,2680,2716,2732,2740,2762,2770,2786,2792,2800,3102,3118,3132,3186,3238,3244,3252,3274,3282,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4063 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4063 2674 5
  · have he : independentCachedBranchMembers4063.erase 2674=independentCachedBranchMembers4061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4061
  · have he : independentCachedBranchMembers4063.filter (independentCachedEdge 2674)=independentCachedBranchMembers4062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4062
end EntropyDesigns.QuadraticRefinement
