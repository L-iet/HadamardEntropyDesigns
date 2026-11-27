/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch15
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers2048 : Finset ℕ := ([18,72,132,222,1626,1644,1686,1734,1740,1776,2638,2674,2680,2740,2770,2776,2788,3130,3158,3164,3178,3226,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2048 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2048 5 (fun x => (if x<2680 then (if x<1686 then (if x<222 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1626 then 0 else (if x<1644 then 0 else 1))) else (if x<1776 then (if x<1734 then 0 else (if x<1740 then 1 else 0)) else (if x<2638 then 1 else (if x<2674 then 1 else 2)))) else (if x<3158 then (if x<2776 then (if x<2740 then 1 else (if x<2770 then 2 else 1)) else (if x<2788 then 2 else (if x<3130 then 1 else 3))) else (if x<3226 then (if x<3164 then 3 else (if x<3178 then 4 else 4)) else (if x<3244 then (if x<3238 then 4 else 3) else (if x<3274 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2049 : Finset ℕ := ([18,72,132,222,1644,1734,2638,2674,2776,2788,3158,3178,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2049 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2049 4 (fun x => (if x<2674 then (if x<222 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1734 then (if x<1644 then 0 else 1) else (if x<2638 then 1 else 1))) else (if x<3158 then (if x<2776 then 2 else (if x<2788 then 2 else 1)) else (if x<3226 then (if x<3178 then 3 else 3) else (if x<3238 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2050 : Finset ℕ := ([18,72,132,222,1596,1626,1644,1686,1734,1740,1776,2638,2674,2680,2740,2770,2776,2788,3130,3158,3164,3178,3226,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2050 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2050 1596 4
  · have he : independentCachedBranchMembers2050.erase 1596=independentCachedBranchMembers2048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2048
  · have he : independentCachedBranchMembers2050.filter (independentCachedEdge 1596)=independentCachedBranchMembers2049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2049
def independentCachedBranchMembers2051 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2051 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2051 2800 5
  · have he : independentCachedBranchMembers2051.erase 2800=independentCachedBranchMembers2047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2047
  · have he : independentCachedBranchMembers2051.filter (independentCachedEdge 2800)=independentCachedBranchMembers2050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2050
def independentCachedBranchMembers2052 : Finset ℕ := ([12,48,192,252,1596,1650,1686,1740,1752,1776,2614,2668,2680,2716,2740,2758,2770,3118,3130,3164,3188,3244,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2052 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2052 5 (fun x => (if x<2680 then (if x<1686 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1596 then 0 else (if x<1650 then 0 else 1))) else (if x<1776 then (if x<1740 then 1 else (if x<1752 then 0 else 1)) else (if x<2614 then 0 else (if x<2668 then 1 else 2)))) else (if x<3130 then (if x<2758 then (if x<2716 then 1 else (if x<2740 then 1 else 2)) else (if x<2770 then 2 else (if x<3118 then 1 else 3))) else (if x<3244 then (if x<3164 then 4 else (if x<3188 then 3 else 4)) else (if x<3274 then (if x<3256 then 4 else 3) else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2053 : Finset ℕ := ([12,48,192,252,1650,1752,2614,2668,2716,2758,3118,3188,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2053 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2053 4 (fun x => (if x<2668 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1752 then (if x<1650 then 0 else 1) else (if x<2614 then 1 else 1))) else (if x<3118 then (if x<2716 then 2 else (if x<2758 then 1 else 2)) else (if x<3256 then (if x<3188 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2054 : Finset ℕ := ([12,48,192,252,1596,1626,1650,1686,1740,1752,1776,2614,2668,2680,2716,2740,2758,2770,3118,3130,3164,3188,3244,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2054 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2054 1626 4
  · have he : independentCachedBranchMembers2054.erase 1626=independentCachedBranchMembers2052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2052
  · have he : independentCachedBranchMembers2054.filter (independentCachedEdge 1626)=independentCachedBranchMembers2053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2053
def independentCachedBranchMembers2055 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2055 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2055 2710 5
  · have he : independentCachedBranchMembers2055.erase 2710=independentCachedBranchMembers2051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2051
  · have he : independentCachedBranchMembers2055.filter (independentCachedEdge 2710)=independentCachedBranchMembers2054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2054
def independentCachedBranchMembers2056 : Finset ℕ := ([12,48,192,252,1596,1626,1644,1734,1740,1776,2638,2674,2680,2740,2770,2776,2788,3118,3188,3214,3250,3256,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2056 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2056 5 (fun x => (if x<2680 then (if x<1644 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1596 then 0 else (if x<1626 then 0 else 1))) else (if x<1776 then (if x<1734 then 1 else (if x<1740 then 1 else 0)) else (if x<2638 then 0 else (if x<2674 then 1 else 2)))) else (if x<3188 then (if x<2776 then (if x<2740 then 1 else (if x<2770 then 2 else 1)) else (if x<2788 then 2 else (if x<3118 then 1 else 3))) else (if x<3256 then (if x<3214 then 3 else (if x<3250 then 4 else 3)) else (if x<3298 then (if x<3284 then 4 else 4) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2057 : Finset ℕ := ([12,48,192,252,1644,1734,2638,2674,2776,2788,3118,3188,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2057 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2057 4 (fun x => (if x<2674 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1734 then (if x<1644 then 0 else 1) else (if x<2638 then 1 else 1))) else (if x<3118 then (if x<2776 then 2 else (if x<2788 then 2 else 1)) else (if x<3256 then (if x<3188 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2058 : Finset ℕ := ([12,48,192,252,1596,1626,1644,1686,1734,1740,1776,2638,2674,2680,2740,2770,2776,2788,3118,3188,3214,3250,3256,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2058 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2058 1686 4
  · have he : independentCachedBranchMembers2058.erase 1686=independentCachedBranchMembers2056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2056
  · have he : independentCachedBranchMembers2058.filter (independentCachedEdge 1686)=independentCachedBranchMembers2057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2057
def independentCachedBranchMembers2059 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2650,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2059 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2059 2650 5
  · have he : independentCachedBranchMembers2059.erase 2650=independentCachedBranchMembers2055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2055
  · have he : independentCachedBranchMembers2059.filter (independentCachedEdge 2650)=independentCachedBranchMembers2058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2058
def independentCachedBranchMembers2060 : Finset ℕ := ([18,72,132,222,1596,1626,1650,1686,1740,1752,2614,2668,2680,2716,2740,2758,2770,3158,3178,3214,3226,3238,3250,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2060 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2060 5 (fun x => (if x<2680 then (if x<1650 then (if x<222 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1596 then 0 else (if x<1626 then 1 else 0))) else (if x<1752 then (if x<1686 then 1 else (if x<1740 then 0 else 0)) else (if x<2614 then 1 else (if x<2668 then 1 else 2)))) else (if x<3178 then (if x<2758 then (if x<2716 then 1 else (if x<2740 then 1 else 2)) else (if x<2770 then 2 else (if x<3158 then 1 else 3))) else (if x<3238 then (if x<3214 then 3 else (if x<3226 then 3 else 4)) else (if x<3284 then (if x<3250 then 4 else 3) else (if x<3304 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2061 : Finset ℕ := ([18,72,132,222,1650,1752,2614,2668,2716,2758,3158,3178,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2061 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2061 4 (fun x => (if x<2668 then (if x<222 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1752 then (if x<1650 then 0 else 1) else (if x<2614 then 1 else 1))) else (if x<3158 then (if x<2716 then 2 else (if x<2758 then 1 else 2)) else (if x<3226 then (if x<3178 then 3 else 3) else (if x<3238 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2062 : Finset ℕ := ([18,72,132,222,1596,1626,1650,1686,1740,1752,1776,2614,2668,2680,2716,2740,2758,2770,3158,3178,3214,3226,3238,3250,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2062 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2062 1776 4
  · have he : independentCachedBranchMembers2062.erase 1776=independentCachedBranchMembers2060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2060
  · have he : independentCachedBranchMembers2062.filter (independentCachedEdge 1776)=independentCachedBranchMembers2061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2061
def independentCachedBranchMembers2063 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2620,2638,2650,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2063 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2063 2620 5
  · have he : independentCachedBranchMembers2063.erase 2620=independentCachedBranchMembers2059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2059
  · have he : independentCachedBranchMembers2063.filter (independentCachedEdge 2620)=independentCachedBranchMembers2062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2062
def independentCachedBranchMembers2064 : Finset ℕ := ([72,222,1626,1644,1734,1740,1776,2620,2638,2674,2680,2710,2730,2770,2776,2788,3118,3158,3164,3178,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2064 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2064 5 (fun x => (if x<2730 then (if x<1776 then (if x<1644 then (if x<222 then 0 else (if x<1626 then 0 else 0)) else (if x<1734 then 1 else (if x<1740 then 1 else 0))) else (if x<2674 then (if x<2620 then 1 else (if x<2638 then 2 else 0)) else (if x<2680 then 2 else (if x<2710 then 1 else 2)))) else (if x<3164 then (if x<2788 then (if x<2770 then 2 else (if x<2776 then 1 else 0)) else (if x<3118 then 1 else (if x<3158 then 3 else 3))) else (if x<3250 then (if x<3178 then 0 else (if x<3214 then 4 else 4)) else (if x<3256 then 3 else (if x<3274 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2065 : Finset ℕ := ([222,1626,1644,2710,2730,2770,2776,2788,3118,3158,3164,3178] : List ℕ).toFinset
theorem independentCachedBranchBound2065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2065 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2065 4 (fun x => (if x<2776 then (if x<2710 then (if x<1626 then 0 else (if x<1644 then 0 else 1)) else (if x<2730 then 1 else (if x<2770 then 2 else 0))) else (if x<3158 then (if x<2788 then 2 else (if x<3118 then 1 else 2)) else (if x<3164 then 0 else (if x<3178 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2066 : Finset ℕ := ([48,72,222,1626,1644,1734,1740,1776,2620,2638,2674,2680,2710,2730,2770,2776,2788,3118,3158,3164,3178,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2066 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2066 48 4
  · have he : independentCachedBranchMembers2066.erase 48=independentCachedBranchMembers2064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2064
  · have he : independentCachedBranchMembers2066.filter (independentCachedEdge 48)=independentCachedBranchMembers2065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2065
def independentCachedBranchMembers2067 : Finset ℕ := ([72,1626,1734,2680,2710,2730,2776,2788,3158,3178,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2067 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2067 4 (fun x => (if x<2776 then (if x<2680 then (if x<1626 then 0 else (if x<1734 then 0 else 1)) else (if x<2710 then 0 else (if x<2730 then 1 else 2))) else (if x<3178 then (if x<2788 then 2 else (if x<3158 then 1 else 3)) else (if x<3256 then 0 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2068 : Finset ℕ := ([12,48,72,222,1626,1644,1734,1740,1776,2620,2638,2674,2680,2710,2730,2770,2776,2788,3118,3158,3164,3178,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2068 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2068 12 4
  · have he : independentCachedBranchMembers2068.erase 12=independentCachedBranchMembers2066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2066
  · have he : independentCachedBranchMembers2068.filter (independentCachedEdge 12)=independentCachedBranchMembers2067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2067
def independentCachedBranchMembers2069 : Finset ℕ := ([48,72,1626,1644,1734,1776,2620,2674,2710,2776,3118,3158,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2069 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2069 4 (fun x => (if x<2674 then (if x<1644 then (if x<72 then 0 else (if x<1626 then 0 else 1)) else (if x<1776 then (if x<1734 then 1 else 1) else (if x<2620 then 1 else 2))) else (if x<3118 then (if x<2710 then 2 else (if x<2776 then 2 else 2)) else (if x<3250 then (if x<3158 then 3 else 3) else (if x<3274 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2070 : Finset ℕ := ([12,48,72,222,1626,1644,1734,1740,1776,2620,2638,2674,2680,2710,2716,2730,2770,2776,2788,3118,3158,3164,3178,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2070 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2070 2716 4
  · have he : independentCachedBranchMembers2070.erase 2716=independentCachedBranchMembers2068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2068
  · have he : independentCachedBranchMembers2070.filter (independentCachedEdge 2716)=independentCachedBranchMembers2069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2069
def independentCachedBranchMembers2071 : Finset ℕ := ([12,222,1626,1644,1734,1776,2620,2674,2710,2776,3164,3178,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2071 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2071 4 (fun x => (if x<2674 then (if x<1644 then (if x<222 then 0 else (if x<1626 then 0 else 1)) else (if x<1776 then (if x<1734 then 1 else 1) else (if x<2620 then 1 else 2))) else (if x<3164 then (if x<2710 then 2 else (if x<2776 then 2 else 2)) else (if x<3214 then (if x<3178 then 0 else 3) else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2072 : Finset ℕ := ([12,48,72,222,1626,1644,1734,1740,1776,2614,2620,2638,2674,2680,2710,2716,2730,2770,2776,2788,3118,3158,3164,3178,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2072 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2072 2614 4
  · have he : independentCachedBranchMembers2072.erase 2614=independentCachedBranchMembers2070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2070
  · have he : independentCachedBranchMembers2072.filter (independentCachedEdge 2614)=independentCachedBranchMembers2071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2071
def independentCachedBranchMembers2073 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1764,1776,2614,2620,2638,2650,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2073 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2073 1764 5
  · have he : independentCachedBranchMembers2073.erase 1764=independentCachedBranchMembers2063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2063
  · have he : independentCachedBranchMembers2073.filter (independentCachedEdge 1764)=independentCachedBranchMembers2072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2072
def independentCachedBranchMembers2074 : Finset ℕ := ([48,192,1596,1650,1686,1740,1752,2614,2650,2668,2680,2716,2730,2758,2770,2800,3118,3130,3158,3188,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2074 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2074 5 (fun x => (if x<2730 then (if x<1752 then (if x<1650 then (if x<192 then 0 else (if x<1596 then 0 else 0)) else (if x<1686 then 1 else (if x<1740 then 1 else 0))) else (if x<2668 then (if x<2614 then 1 else (if x<2650 then 0 else 2)) else (if x<2680 then 2 else (if x<2716 then 1 else 1)))) else (if x<3158 then (if x<2800 then (if x<2758 then 2 else (if x<2770 then 0 else 1)) else (if x<3118 then 2 else (if x<3130 then 3 else 0))) else (if x<3250 then (if x<3188 then 3 else (if x<3238 then 4 else 4)) else (if x<3274 then 3 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2075 : Finset ℕ := ([192,1596,1650,2716,2730,2758,2770,2800,3118,3130,3158,3188] : List ℕ).toFinset
theorem independentCachedBranchBound2075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2075 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2075 4 (fun x => (if x<2770 then (if x<2716 then (if x<1596 then 0 else (if x<1650 then 0 else 1)) else (if x<2730 then 1 else (if x<2758 then 2 else 0))) else (if x<3130 then (if x<2800 then 1 else (if x<3118 then 2 else 2)) else (if x<3158 then 0 else (if x<3188 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2076 : Finset ℕ := ([48,72,192,1596,1650,1686,1740,1752,2614,2650,2668,2680,2716,2730,2758,2770,2800,3118,3130,3158,3188,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2076 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2076 72 4
  · have he : independentCachedBranchMembers2076.erase 72=independentCachedBranchMembers2074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2074
  · have he : independentCachedBranchMembers2076.filter (independentCachedEdge 72)=independentCachedBranchMembers2075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2075
def independentCachedBranchMembers2077 : Finset ℕ := ([48,1596,1752,2680,2716,2730,2758,2800,3118,3188,3238,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2077 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2077 4 (fun x => (if x<2758 then (if x<2680 then (if x<1596 then 0 else (if x<1752 then 0 else 1)) else (if x<2716 then 0 else (if x<2730 then 1 else 2))) else (if x<3188 then (if x<2800 then 2 else (if x<3118 then 1 else 3)) else (if x<3238 then 0 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2078 : Finset ℕ := ([18,48,72,192,1596,1650,1686,1740,1752,2614,2650,2668,2680,2716,2730,2758,2770,2800,3118,3130,3158,3188,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2078 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2078 18 4
  · have he : independentCachedBranchMembers2078.erase 18=independentCachedBranchMembers2076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2076
  · have he : independentCachedBranchMembers2078.filter (independentCachedEdge 18)=independentCachedBranchMembers2077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2077
def independentCachedBranchMembers2079 : Finset ℕ := ([48,72,1596,1650,1686,1752,2650,2668,2758,2800,3118,3158,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2079 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2079 4 (fun x => (if x<2668 then (if x<1650 then (if x<72 then 0 else (if x<1596 then 0 else 1)) else (if x<1752 then (if x<1686 then 1 else 1) else (if x<2650 then 1 else 2))) else (if x<3118 then (if x<2758 then 2 else (if x<2800 then 2 else 2)) else (if x<3250 then (if x<3158 then 3 else 3) else (if x<3274 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2080 : Finset ℕ := ([18,48,72,192,1596,1650,1686,1740,1752,2614,2650,2668,2680,2716,2730,2758,2770,2788,2800,3118,3130,3158,3188,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2080 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2080 2788 4
  · have he : independentCachedBranchMembers2080.erase 2788=independentCachedBranchMembers2078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2078
  · have he : independentCachedBranchMembers2080.filter (independentCachedEdge 2788)=independentCachedBranchMembers2079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2079
def independentCachedBranchMembers2081 : Finset ℕ := ([18,192,1596,1650,1686,1752,2650,2668,2758,2800,3130,3188,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2081 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2081 4 (fun x => (if x<2668 then (if x<1650 then (if x<192 then 0 else (if x<1596 then 0 else 1)) else (if x<1752 then (if x<1686 then 1 else 1) else (if x<2650 then 1 else 2))) else (if x<3130 then (if x<2758 then 2 else (if x<2800 then 2 else 2)) else (if x<3238 then (if x<3188 then 0 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2082 : Finset ℕ := ([18,48,72,192,1596,1650,1686,1740,1752,2614,2638,2650,2668,2680,2716,2730,2758,2770,2788,2800,3118,3130,3158,3188,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2082 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2082 2638 4
  · have he : independentCachedBranchMembers2082.erase 2638=independentCachedBranchMembers2080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2080
  · have he : independentCachedBranchMembers2082.filter (independentCachedEdge 2638)=independentCachedBranchMembers2081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2081
def independentCachedBranchMembers2083 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1692,1734,1740,1752,1764,1776,2614,2620,2638,2650,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2083 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2083 1692 5
  · have he : independentCachedBranchMembers2083.erase 1692=independentCachedBranchMembers2073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2073
  · have he : independentCachedBranchMembers2083.filter (independentCachedEdge 1692)=independentCachedBranchMembers2082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2082
def independentCachedBranchMembers2084 : Finset ℕ := ([192,252,1626,1644,1734,1740,1776,2620,2638,2674,2680,2710,2730,2770,2776,2788,3130,3188,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2084 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2084 5 (fun x => (if x<2730 then (if x<1776 then (if x<1644 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1734 then 1 else (if x<1740 then 1 else 0))) else (if x<2674 then (if x<2620 then 0 else (if x<2638 then 2 else 1)) else (if x<2680 then 2 else (if x<2710 then 1 else 2)))) else (if x<3226 then (if x<2788 then (if x<2770 then 2 else (if x<2776 then 1 else 0)) else (if x<3130 then 0 else (if x<3188 then 3 else 3))) else (if x<3284 then (if x<3238 then 4 else (if x<3244 then 3 else 4)) else (if x<3298 then 0 else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2085 : Finset ℕ := ([192,1644,1776,2620,2638,2730,2770,2776,3188,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2085 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2085 4 (fun x => (if x<2770 then (if x<2620 then (if x<1644 then 0 else (if x<1776 then 1 else 0)) else (if x<2638 then 1 else (if x<2730 then 1 else 2))) else (if x<3226 then (if x<2776 then 0 else (if x<3188 then 2 else 3)) else (if x<3298 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2086 : Finset ℕ := ([132,192,252,1626,1644,1734,1740,1776,2620,2638,2674,2680,2710,2730,2770,2776,2788,3130,3188,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2086 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2086 132 4
  · have he : independentCachedBranchMembers2086.erase 132=independentCachedBranchMembers2084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2084
  · have he : independentCachedBranchMembers2086.filter (independentCachedEdge 132)=independentCachedBranchMembers2085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2085
def independentCachedBranchMembers2087 : Finset ℕ := ([252,1734,1776,2620,2638,2680,2730,2776,3188,3238,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2087 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2087 4 (fun x => (if x<2730 then (if x<2620 then (if x<1734 then 0 else (if x<1776 then 1 else 0)) else (if x<2638 then 1 else (if x<2680 then 1 else 0))) else (if x<3238 then (if x<2776 then 2 else (if x<3188 then 2 else 0)) else (if x<3284 then 2 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2088 : Finset ℕ := ([18,132,192,252,1626,1644,1734,1740,1776,2620,2638,2674,2680,2710,2730,2770,2776,2788,3130,3188,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2088 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2088 18 4
  · have he : independentCachedBranchMembers2088.erase 18=independentCachedBranchMembers2086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2086
  · have he : independentCachedBranchMembers2088.filter (independentCachedEdge 18)=independentCachedBranchMembers2087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2087
def independentCachedBranchMembers2089 : Finset ℕ := ([18,192,1626,1644,1734,1776,2620,2674,2710,2776,3130,3188,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2089 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2089 4 (fun x => (if x<2674 then (if x<1644 then (if x<192 then 0 else (if x<1626 then 0 else 1)) else (if x<1776 then (if x<1734 then 1 else 1) else (if x<2620 then 1 else 2))) else (if x<3130 then (if x<2710 then 2 else (if x<2776 then 2 else 2)) else (if x<3238 then (if x<3188 then 0 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2090 : Finset ℕ := ([18,132,192,252,1626,1644,1734,1740,1776,2620,2638,2674,2680,2710,2716,2730,2770,2776,2788,3130,3188,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2090 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2090 2716 4
  · have he : independentCachedBranchMembers2090.erase 2716=independentCachedBranchMembers2088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2088
  · have he : independentCachedBranchMembers2090.filter (independentCachedEdge 2716)=independentCachedBranchMembers2089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2089
def independentCachedBranchMembers2091 : Finset ℕ := ([132,252,1626,1644,1734,1776,2620,2674,2710,2776,3226,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2091 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2091 4 (fun x => (if x<2674 then (if x<1644 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1776 then (if x<1734 then 1 else 1) else (if x<2620 then 1 else 2))) else (if x<3226 then (if x<2710 then 2 else (if x<2776 then 2 else 2)) else (if x<3284 then (if x<3244 then 3 else 0) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2092 : Finset ℕ := ([18,132,192,252,1626,1644,1734,1740,1776,2614,2620,2638,2674,2680,2710,2716,2730,2770,2776,2788,3130,3188,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2092 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2092 2614 4
  · have he : independentCachedBranchMembers2092.erase 2614=independentCachedBranchMembers2090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2090
  · have he : independentCachedBranchMembers2092.filter (independentCachedEdge 2614)=independentCachedBranchMembers2091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2091
def independentCachedBranchMembers2093 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1614,1626,1644,1650,1686,1692,1734,1740,1752,1764,1776,2614,2620,2638,2650,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2093 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2093 1614 5
  · have he : independentCachedBranchMembers2093.erase 1614=independentCachedBranchMembers2083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2083
  · have he : independentCachedBranchMembers2093.filter (independentCachedEdge 1614)=independentCachedBranchMembers2092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2092
def independentCachedBranchMembers2094 : Finset ℕ := ([132,222,252,1596,1650,1686,1740,1752,2614,2650,2668,2680,2716,2730,2758,2770,2800,3164,3178,3214,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2094 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2094 5 (fun x => (if x<2716 then (if x<1740 then (if x<1596 then (if x<222 then 0 else (if x<252 then 0 else 1)) else (if x<1650 then 1 else (if x<1686 then 2 else 0))) else (if x<2650 then (if x<1752 then 0 else (if x<2614 then 1 else 2)) else (if x<2668 then 2 else (if x<2680 then 3 else 1)))) else (if x<3178 then (if x<2770 then (if x<2730 then 0 else (if x<2758 then 3 else 0)) else (if x<2800 then 4 else (if x<3164 then 2 else 1))) else (if x<3244 then (if x<3214 then 3 else (if x<3226 then 0 else 3)) else (if x<3284 then (if x<3256 then 3 else 1) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2095 : Finset ℕ := ([132,1686,1752,2614,2650,2680,2730,2758,3178,3226,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2095 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2095 4 (fun x => (if x<2730 then (if x<2614 then (if x<1686 then 0 else (if x<1752 then 0 else 1)) else (if x<2650 then 1 else (if x<2680 then 1 else 0))) else (if x<3226 then (if x<2758 then 2 else (if x<3178 then 2 else 0)) else (if x<3256 then 3 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2096 : Finset ℕ := ([12,132,222,252,1596,1650,1686,1740,1752,2614,2650,2668,2680,2716,2730,2758,2770,2800,3164,3178,3214,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2096 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2096 12 4
  · have he : independentCachedBranchMembers2096.erase 12=independentCachedBranchMembers2094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2094
  · have he : independentCachedBranchMembers2096.filter (independentCachedEdge 12)=independentCachedBranchMembers2095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2095
def independentCachedBranchMembers2097 : Finset ℕ := ([12,222,1596,1650,1686,1752,2650,2668,2758,2800,3164,3178,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2097 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2097 4 (fun x => (if x<2668 then (if x<1650 then (if x<222 then 0 else (if x<1596 then 0 else 1)) else (if x<1752 then (if x<1686 then 1 else 1) else (if x<2650 then 1 else 2))) else (if x<3164 then (if x<2758 then 2 else (if x<2800 then 2 else 2)) else (if x<3214 then (if x<3178 then 0 else 3) else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2098 : Finset ℕ := ([12,132,222,252,1596,1650,1686,1740,1752,2614,2650,2668,2680,2716,2730,2758,2770,2788,2800,3164,3178,3214,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2098 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2098 2788 4
  · have he : independentCachedBranchMembers2098.erase 2788=independentCachedBranchMembers2096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2096
  · have he : independentCachedBranchMembers2098.filter (independentCachedEdge 2788)=independentCachedBranchMembers2097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2097
def independentCachedBranchMembers2099 : Finset ℕ := ([132,252,1596,1650,1686,1752,2650,2668,2758,2800,3226,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2099 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2099 4 (fun x => (if x<2668 then (if x<1650 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1752 then (if x<1686 then 1 else 1) else (if x<2650 then 1 else 2))) else (if x<3226 then (if x<2758 then 2 else (if x<2800 then 2 else 2)) else (if x<3284 then (if x<3244 then 3 else 0) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2100 : Finset ℕ := ([12,132,222,252,1596,1650,1686,1740,1752,2614,2638,2650,2668,2680,2716,2730,2758,2770,2788,2800,3164,3178,3214,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2100 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2100 2638 4
  · have he : independentCachedBranchMembers2100.erase 2638=independentCachedBranchMembers2098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2098
  · have he : independentCachedBranchMembers2100.filter (independentCachedEdge 2638)=independentCachedBranchMembers2099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2099
def independentCachedBranchMembers2101 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1596,1614,1626,1644,1650,1686,1692,1734,1740,1752,1764,1776,2614,2620,2638,2650,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2101 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2101 1590 5
  · have he : independentCachedBranchMembers2101.erase 1590=independentCachedBranchMembers2093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2093
  · have he : independentCachedBranchMembers2101.filter (independentCachedEdge 1590)=independentCachedBranchMembers2100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2100
def independentCachedBranchMembers2102 : Finset ℕ := ([132,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2716,2758,2776,2788,3130,3164,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2102 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2102 5 (fun x => (if x<2716 then (if x<1740 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1626 then 1 else (if x<1686 then 1 else 1))) else (if x<2638 then (if x<1776 then 0 else (if x<2614 then 1 else 2)) else (if x<2668 then 2 else (if x<2674 then 3 else 3)))) else (if x<3214 then (if x<2788 then (if x<2758 then 0 else (if x<2776 then 3 else 3)) else (if x<3130 then 0 else (if x<3164 then 4 else 4))) else (if x<3274 then (if x<3244 then 4 else (if x<3250 then 0 else 2)) else (if x<3284 then 2 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2103 : Finset ℕ := ([1596,1776,2674,2716,2758,2788,3130,3214,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2103 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2103 4 (fun x => (if x<2788 then (if x<2674 then (if x<1776 then 0 else 0) else (if x<2716 then 1 else (if x<2758 then 2 else 1))) else (if x<3214 then (if x<3130 then 2 else 1) else (if x<3244 then 1 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2104 : Finset ℕ := ([72,132,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2716,2758,2776,2788,3130,3164,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2104 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2104 72 4
  · have he : independentCachedBranchMembers2104.erase 72=independentCachedBranchMembers2102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2102
  · have he : independentCachedBranchMembers2104.filter (independentCachedEdge 72)=independentCachedBranchMembers2103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2103
def independentCachedBranchMembers2105 : Finset ℕ := ([1626,1686,2668,2716,2776,2788,3164,3244,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2105 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2105 4 (fun x => (if x<2788 then (if x<2668 then (if x<1686 then 0 else 0) else (if x<2716 then 1 else (if x<2776 then 1 else 2))) else (if x<3244 then (if x<3164 then 2 else 1) else (if x<3284 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2106 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2716,2758,2776,2788,3130,3164,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2106 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2106 48 4
  · have he : independentCachedBranchMembers2106.erase 48=independentCachedBranchMembers2104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2104
  · have he : independentCachedBranchMembers2106.filter (independentCachedEdge 48)=independentCachedBranchMembers2105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2105
def independentCachedBranchMembers2107 : Finset ℕ := ([48,252,1596,1776,2614,2668,2674,2788,3130,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2107 4 (fun x => (if x<2674 then (if x<1776 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<2614 then 0 else (if x<2668 then 1 else 1))) else (if x<3244 then (if x<2788 then 2 else (if x<3130 then 2 else 2)) else (if x<3250 then 2 else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2108 : Finset ℕ := ([48,72,132,222,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2716,2758,2776,2788,3130,3164,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2108 222 4
  · have he : independentCachedBranchMembers2108.erase 222=independentCachedBranchMembers2106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2106
  · have he : independentCachedBranchMembers2108.filter (independentCachedEdge 222)=independentCachedBranchMembers2107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2107
def independentCachedBranchMembers2109 : Finset ℕ := ([72,132,1626,1686,2638,2668,2674,2716,3164,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound2109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2109 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2109 4 (fun x => (if x<2674 then (if x<1686 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<2638 then 0 else (if x<2668 then 1 else 2))) else (if x<3214 then (if x<2716 then 1 else (if x<3164 then 2 else 2)) else (if x<3244 then 1 else (if x<3250 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2110 : Finset ℕ := ([48,72,132,192,222,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2716,2758,2776,2788,3130,3164,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2110 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2110 192 4
  · have he : independentCachedBranchMembers2110.erase 192=independentCachedBranchMembers2108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2108
  · have he : independentCachedBranchMembers2110.filter (independentCachedEdge 192)=independentCachedBranchMembers2109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2109
def independentCachedBranchMembers2111 : Finset ℕ := ([48,252,1596,1776,2638,2716,2758,2776,3164,3214,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2111 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2111 4 (fun x => (if x<2758 then (if x<1776 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<2638 then 0 else (if x<2716 then 1 else 1))) else (if x<3214 then (if x<2776 then 2 else (if x<3164 then 2 else 1)) else (if x<3274 then 1 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2112 : Finset ℕ := ([18,48,72,132,192,222,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2716,2758,2776,2788,3130,3164,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2112 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2112 18 4
  · have he : independentCachedBranchMembers2112.erase 18=independentCachedBranchMembers2110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2110
  · have he : independentCachedBranchMembers2112.filter (independentCachedEdge 18)=independentCachedBranchMembers2111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2111
def independentCachedBranchMembers2113 : Finset ℕ := ([72,132,1626,1686,2614,2758,2776,2788,3130,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2113 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2113 4 (fun x => (if x<2776 then (if x<1686 then (if x<132 then 0 else (if x<1626 then 0 else 0)) else (if x<2614 then 0 else (if x<2758 then 1 else 1))) else (if x<3274 then (if x<2788 then 2 else (if x<3130 then 2 else 1)) else (if x<3284 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2114 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2716,2758,2776,2788,3130,3164,3214,3244,3250,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2114 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2114 12 4
  · have he : independentCachedBranchMembers2114.erase 12=independentCachedBranchMembers2112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2112
  · have he : independentCachedBranchMembers2114.filter (independentCachedEdge 12)=independentCachedBranchMembers2113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2113
def independentCachedBranchMembers2115 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1596,1614,1626,1644,1650,1686,1692,1734,1740,1752,1764,1776,2614,2620,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2115 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2115 2662 5
  · have he : independentCachedBranchMembers2115.erase 2662=independentCachedBranchMembers2101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2101
  · have he : independentCachedBranchMembers2115.filter (independentCachedEdge 2662)=independentCachedBranchMembers2114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2114
def independentCachedBranchMembers2116 : Finset ℕ := ([1596,1626,1644,1650,1686,1734,1752,1776,2614,2638,2680,2716,2730,2740,2764,2770,2788,3130,3164,3178,3188,3214,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2116 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2116 5 (fun x => (if x<2730 then (if x<1752 then (if x<1650 then (if x<1626 then 0 else (if x<1644 then 0 else 1)) else (if x<1686 then 1 else (if x<1734 then 0 else 1))) else (if x<2638 then (if x<1776 then 1 else (if x<2614 then 0 else 2)) else (if x<2680 then 2 else (if x<2716 then 0 else 2)))) else (if x<3164 then (if x<2770 then (if x<2740 then 2 else (if x<2764 then 0 else 1)) else (if x<2788 then 0 else (if x<3130 then 2 else 3))) else (if x<3214 then (if x<3178 then 3 else (if x<3188 then 4 else 4)) else (if x<3256 then (if x<3238 then 3 else 4) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2117 : Finset ℕ := ([1626,1650,1686,1734,2614,2638,2730,2770,3130,3178,3214,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2117 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2117 4 (fun x => (if x<2730 then (if x<1734 then (if x<1650 then 0 else (if x<1686 then 1 else 0)) else (if x<2614 then 1 else (if x<2638 then 2 else 2))) else (if x<3178 then (if x<2770 then 2 else (if x<3130 then 0 else 1)) else (if x<3214 then 3 else (if x<3238 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2118 : Finset ℕ := ([252,1596,1626,1644,1650,1686,1734,1752,1776,2614,2638,2680,2716,2730,2740,2764,2770,2788,3130,3164,3178,3188,3214,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2118 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2118 252 4
  · have he : independentCachedBranchMembers2118.erase 252=independentCachedBranchMembers2116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2116
  · have he : independentCachedBranchMembers2118.filter (independentCachedEdge 252)=independentCachedBranchMembers2117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2117
def independentCachedBranchMembers2119 : Finset ℕ := ([1596,1644,1752,1776,2614,2638,2730,2770,3164,3188,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2119 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2119 4 (fun x => (if x<2730 then (if x<1776 then (if x<1644 then 0 else (if x<1752 then 1 else 0)) else (if x<2614 then 1 else (if x<2638 then 0 else 1))) else (if x<3188 then (if x<2770 then 2 else (if x<3164 then 0 else 2)) else (if x<3256 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2120 : Finset ℕ := ([132,252,1596,1626,1644,1650,1686,1734,1752,1776,2614,2638,2680,2716,2730,2740,2764,2770,2788,3130,3164,3178,3188,3214,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2120 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2120 132 4
  · have he : independentCachedBranchMembers2120.erase 132=independentCachedBranchMembers2118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2118
  · have he : independentCachedBranchMembers2120.filter (independentCachedEdge 132)=independentCachedBranchMembers2119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2119
def independentCachedBranchMembers2121 : Finset ℕ := ([1596,1650,1734,1776,2716,2730,2770,2788,3130,3188,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2121 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2121 4 (fun x => (if x<2770 then (if x<1776 then (if x<1650 then 0 else (if x<1734 then 0 else 1)) else (if x<2716 then 1 else (if x<2730 then 0 else 2))) else (if x<3188 then (if x<2788 then 0 else (if x<3130 then 1 else 2)) else (if x<3214 then 2 else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2122 : Finset ℕ := ([72,132,252,1596,1626,1644,1650,1686,1734,1752,1776,2614,2638,2680,2716,2730,2740,2764,2770,2788,3130,3164,3178,3188,3214,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2122 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2122 72 4
  · have he : independentCachedBranchMembers2122.erase 72=independentCachedBranchMembers2120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2120
  · have he : independentCachedBranchMembers2122.filter (independentCachedEdge 72)=independentCachedBranchMembers2121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2121
def independentCachedBranchMembers2123 : Finset ℕ := ([1626,1644,1686,1752,2716,2730,2770,2788,3164,3178,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2123 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2123 4 (fun x => (if x<2770 then (if x<1752 then (if x<1644 then 0 else (if x<1686 then 0 else 1)) else (if x<2716 then 1 else (if x<2730 then 1 else 2))) else (if x<3178 then (if x<2788 then 0 else (if x<3164 then 0 else 2)) else (if x<3238 then 2 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2124 : Finset ℕ := ([48,72,132,252,1596,1626,1644,1650,1686,1734,1752,1776,2614,2638,2680,2716,2730,2740,2764,2770,2788,3130,3164,3178,3188,3214,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2124 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2124 48 4
  · have he : independentCachedBranchMembers2124.erase 48=independentCachedBranchMembers2122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2122
  · have he : independentCachedBranchMembers2124.filter (independentCachedEdge 48)=independentCachedBranchMembers2123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2123
def independentCachedBranchMembers2125 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1776,2614,2638,2716,2788,3130,3164,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2125 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2125 4 (fun x => (if x<2614 then (if x<1596 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3130 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2126 : Finset ℕ := ([48,72,132,252,1596,1626,1644,1650,1686,1734,1752,1776,2614,2638,2662,2680,2716,2730,2740,2764,2770,2788,3130,3164,3178,3188,3214,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2126 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2126 2662 4
  · have he : independentCachedBranchMembers2126.erase 2662=independentCachedBranchMembers2124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2124
  · have he : independentCachedBranchMembers2126.filter (independentCachedEdge 2662)=independentCachedBranchMembers2125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2125
def independentCachedBranchMembers2127 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1596,1614,1626,1644,1650,1686,1692,1734,1740,1746,1752,1764,1776,2614,2620,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2127 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2127 1746 5
  · have he : independentCachedBranchMembers2127.erase 1746=independentCachedBranchMembers2115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2115
  · have he : independentCachedBranchMembers2127.filter (independentCachedEdge 1746)=independentCachedBranchMembers2126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2126
def independentCachedBranchMembers2128 : Finset ℕ := ([12,18,48,72,132,192,222,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2128 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2128 3242 6
  · have he : independentCachedBranchMembers2128.erase 3242=independentCachedBranchMembers2006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2006
  · have he : independentCachedBranchMembers2128.filter (independentCachedEdge 3242)=independentCachedBranchMembers2127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2127
def independentCachedBranchMembers2129 : Finset ℕ := ([12,132,222,252,1596,1614,1628,1678,1686,1708,1748,1764,2606,2646,2652,2702,2716,2740,2764,2788,3102,3150,3180,3188,3228,3238,3244,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2129 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2129 6 (fun x => (if x<2702 then (if x<1678 then (if x<252 then (if x<132 then 0 else (if x<222 then 1 else 0)) else (if x<1614 then (if x<1596 then 1 else 2) else (if x<1628 then 0 else 3))) else (if x<1764 then (if x<1708 then (if x<1686 then 2 else 3) else (if x<1748 then 1 else 1)) else (if x<2646 then (if x<2606 then 2 else 4) else (if x<2652 then 3 else 0)))) else (if x<3180 then (if x<2764 then (if x<2716 then 0 else (if x<2740 then 1 else 4)) else (if x<3102 then (if x<2788 then 4 else 1) else (if x<3150 then 0 else 4))) else (if x<3244 then (if x<3228 then (if x<3188 then 5 else 2) else (if x<3238 then 5 else 5)) else (if x<3276 then (if x<3270 then 2 else 2) else (if x<3284 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2130 : Finset ℕ := ([12,252,1628,1708,2646,2702,2764,2788,3102,3180,3188,3228,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2130 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2130 5 (fun x => (if x<2788 then (if x<1708 then (if x<252 then 0 else (if x<1628 then 0 else 0)) else (if x<2702 then (if x<2646 then 0 else 1) else (if x<2764 then 1 else 0))) else (if x<3188 then (if x<3102 then 1 else (if x<3180 then 1 else 0)) else (if x<3244 then (if x<3228 then 1 else 0) else (if x<3270 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2131 : Finset ℕ := ([12,132,222,252,1596,1614,1628,1678,1686,1708,1748,1764,2606,2646,2652,2702,2716,2740,2758,2764,2788,3102,3150,3180,3188,3228,3238,3244,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2131 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2131 2758 5
  · have he : independentCachedBranchMembers2131.erase 2758=independentCachedBranchMembers2129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2129
  · have he : independentCachedBranchMembers2131.filter (independentCachedEdge 2758)=independentCachedBranchMembers2130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2130
def independentCachedBranchMembers2132 : Finset ℕ := ([132,222,1678,1748,2606,2652,2764,2788,3102,3180,3228,3238,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2132 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2132 5 (fun x => (if x<2788 then (if x<1748 then (if x<222 then 0 else (if x<1678 then 0 else 0)) else (if x<2652 then (if x<2606 then 0 else 1) else (if x<2764 then 1 else 0))) else (if x<3228 then (if x<3102 then 1 else (if x<3180 then 1 else 1)) else (if x<3270 then (if x<3238 then 0 else 1) else (if x<3284 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2133 : Finset ℕ := ([12,132,222,252,1596,1614,1628,1678,1686,1708,1748,1764,2606,2646,2652,2668,2702,2716,2740,2758,2764,2788,3102,3150,3180,3188,3228,3238,3244,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2133 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2133 2668 5
  · have he : independentCachedBranchMembers2133.erase 2668=independentCachedBranchMembers2131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2131
  · have he : independentCachedBranchMembers2133.filter (independentCachedEdge 2668)=independentCachedBranchMembers2132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2132
def independentCachedBranchMembers2134 : Finset ℕ := ([1614,1628,1678,1708,1748,1764,2606,2646,2740,2764,3102,3188,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2134 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2134 5 (fun x => (if x<2646 then (if x<1708 then (if x<1628 then 0 else (if x<1678 then 1 else 1)) else (if x<1764 then (if x<1748 then 0 else 0) else (if x<2606 then 1 else 0))) else (if x<3102 then (if x<2740 then 0 else (if x<2764 then 0 else 0)) else (if x<3238 then (if x<3188 then 1 else 1) else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2135 : Finset ℕ := ([12,132,222,252,1596,1614,1628,1678,1686,1708,1740,1748,1764,2606,2646,2652,2668,2702,2716,2740,2758,2764,2788,3102,3150,3180,3188,3228,3238,3244,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2135 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2135 1740 5
  · have he : independentCachedBranchMembers2135.erase 1740=independentCachedBranchMembers2133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2133
  · have he : independentCachedBranchMembers2135.filter (independentCachedEdge 1740)=independentCachedBranchMembers2134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2134
def independentCachedBranchMembers2136 : Finset ℕ := ([12,222,1628,1678,1740,2606,2646,2652,2668,2702,2740,2758,2764,3150,3188,3228,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2136 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2136 5 (fun x => (if x<2702 then (if x<1740 then (if x<1628 then (if x<222 then 0 else 0) else (if x<1678 then 0 else 0)) else (if x<2646 then (if x<2606 then 1 else 2) else (if x<2652 then 2 else (if x<2668 then 1 else 3)))) else (if x<3188 then (if x<2758 then (if x<2740 then 1 else 2) else (if x<2764 then 3 else (if x<3150 then 0 else 0))) else (if x<3238 then (if x<3228 then 4 else 0) else (if x<3244 then 4 else (if x<3284 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2137 : Finset ℕ := ([12,132,222,252,1596,1614,1628,1678,1686,1708,1740,1748,1764,2606,2646,2652,2668,2702,2716,2740,2758,2764,2788,3102,3150,3180,3188,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2137 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2137 3252 5
  · have he : independentCachedBranchMembers2137.erase 3252=independentCachedBranchMembers2135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2135
  · have he : independentCachedBranchMembers2137.filter (independentCachedEdge 3252)=independentCachedBranchMembers2136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2136
def independentCachedBranchMembers2138 : Finset ℕ := ([12,252,1596,1614,1628,1686,1708,1740,1764,2646,2668,2702,2716,2740,2758,3150,3188,3244,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2138 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2138 5 (fun x => (if x<2646 then (if x<1628 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1614 then 0 else 1)) else (if x<1708 then (if x<1686 then 2 else 1) else (if x<1740 then 1 else (if x<1764 then 0 else 2)))) else (if x<2758 then (if x<2702 then (if x<2668 then 1 else 0) else (if x<2716 then 1 else (if x<2740 then 0 else 1))) else (if x<3188 then (if x<3150 then 3 else 3) else (if x<3244 then 2 else (if x<3276 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2139 : Finset ℕ := ([12,132,222,252,1596,1614,1628,1678,1686,1708,1740,1748,1764,2606,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3150,3180,3188,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2139 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2139 2710 5
  · have he : independentCachedBranchMembers2139.erase 2710=independentCachedBranchMembers2137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2137
  · have he : independentCachedBranchMembers2139.filter (independentCachedEdge 2710)=independentCachedBranchMembers2138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2138
def independentCachedBranchMembers2140 : Finset ℕ := ([132,222,1596,1614,1678,1686,1740,1748,1764,2606,2652,2668,2716,2740,2758,3150,3238,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2140 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2140 5 (fun x => (if x<2606 then (if x<1678 then (if x<1596 then (if x<222 then 0 else 0) else (if x<1614 then 1 else 1)) else (if x<1740 then (if x<1686 then 0 else 1) else (if x<1748 then 2 else (if x<1764 then 0 else 1)))) else (if x<2758 then (if x<2668 then (if x<2652 then 3 else 2) else (if x<2716 then 1 else (if x<2740 then 0 else 1))) else (if x<3238 then (if x<3150 then 0 else 2) else (if x<3276 then 3 else (if x<3284 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2141 : Finset ℕ := ([12,132,222,252,1596,1614,1628,1678,1686,1708,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3150,3180,3188,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2141 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2141 2620 5
  · have he : independentCachedBranchMembers2141.erase 2620=independentCachedBranchMembers2139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2139
  · have he : independentCachedBranchMembers2141.filter (independentCachedEdge 2620)=independentCachedBranchMembers2140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2140
def independentCachedBranchMembers2142 : Finset ℕ := ([1596,1628,1678,1686,1708,1740,1748,2606,2646,2668,2716,2758,2788,3150,3180,3188,3228,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2142 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2142 5 (fun x => (if x<2668 then (if x<1708 then (if x<1678 then (if x<1628 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<1748 then (if x<1740 then 1 else 2) else (if x<2606 then 0 else (if x<2646 then 0 else 1)))) else (if x<3180 then (if x<2758 then (if x<2716 then 1 else 0) else (if x<2788 then 0 else (if x<3150 then 2 else 3))) else (if x<3228 then (if x<3188 then 2 else 3) else (if x<3238 then 3 else (if x<3270 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2143 : Finset ℕ := ([12,132,222,252,1596,1614,1628,1678,1686,1692,1708,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3150,3180,3188,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2143 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2143 1692 5
  · have he : independentCachedBranchMembers2143.erase 1692=independentCachedBranchMembers2141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2141
  · have he : independentCachedBranchMembers2143.filter (independentCachedEdge 1692)=independentCachedBranchMembers2142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2142
def independentCachedBranchMembers2144 : Finset ℕ := ([12,132,222,252,1596,1686,1740,2652,2668,2702,2716,2758,2788,3150,3180,3228,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2144 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2144 5 (fun x => (if x<2702 then (if x<1596 then (if x<222 then (if x<132 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1740 then (if x<1686 then 2 else 2) else (if x<2652 then 0 else (if x<2668 then 0 else 2)))) else (if x<3180 then (if x<2758 then (if x<2716 then 0 else 1) else (if x<2788 then 2 else (if x<3150 then 1 else 0))) else (if x<3244 then (if x<3228 then 3 else 0) else (if x<3270 then 1 else (if x<3284 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2145 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1678,1686,1692,1708,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3150,3180,3188,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2145 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2145 1590 5
  · have he : independentCachedBranchMembers2145.erase 1590=independentCachedBranchMembers2143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2143
  · have he : independentCachedBranchMembers2145.filter (independentCachedEdge 1590)=independentCachedBranchMembers2144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2144
def independentCachedBranchMembers2146 : Finset ℕ := ([252,1590,1596,1628,1678,1748,1764,2620,2646,2652,2668,2702,2740,2788,3102,3150,3188,3228,3238,3244,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2146 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2146 5 (fun x => (if x<2702 then (if x<1748 then (if x<1596 then (if x<1590 then 0 else 1) else (if x<1628 then 0 else (if x<1678 then 1 else 1))) else (if x<2646 then (if x<1764 then 0 else (if x<2620 then 1 else 2)) else (if x<2652 then 2 else (if x<2668 then 0 else 3)))) else (if x<3188 then (if x<2788 then (if x<2740 then 2 else 0) else (if x<3102 then 2 else (if x<3150 then 1 else 3))) else (if x<3244 then (if x<3228 then 0 else (if x<3238 then 0 else 1)) else (if x<3270 then 2 else (if x<3276 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2147 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1678,1686,1692,1708,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3150,3180,3188,3214,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2147 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2147 3214 5
  · have he : independentCachedBranchMembers2147.erase 3214=independentCachedBranchMembers2145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2145
  · have he : independentCachedBranchMembers2147.filter (independentCachedEdge 3214)=independentCachedBranchMembers2146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2146
def independentCachedBranchMembers2148 : Finset ℕ := ([132,222,1596,1614,1678,1686,1740,1748,1764,2620,2646,2702,2710,2764,2788,3102,3180,3188,3228,3244,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2148 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2148 5 (fun x => (if x<2702 then (if x<1686 then (if x<1596 then (if x<222 then 0 else 0) else (if x<1614 then 1 else (if x<1678 then 1 else 0))) else (if x<1764 then (if x<1740 then 1 else (if x<1748 then 2 else 0)) else (if x<2620 then 1 else (if x<2646 then 3 else 3)))) else (if x<3180 then (if x<2764 then (if x<2710 then 2 else 0) else (if x<2788 then 0 else (if x<3102 then 2 else 1))) else (if x<3244 then (if x<3188 then 1 else (if x<3228 then 3 else 0)) else (if x<3252 then 2 else (if x<3270 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2149 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1678,1686,1692,1708,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3132,3150,3180,3188,3214,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2149 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2149 3132 5
  · have he : independentCachedBranchMembers2149.erase 3132=independentCachedBranchMembers2147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2147
  · have he : independentCachedBranchMembers2149.filter (independentCachedEdge 3132)=independentCachedBranchMembers2148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2148
def independentCachedBranchMembers2150 : Finset ℕ := ([12,252,1596,1614,1678,1686,1740,1748,1764,2606,2652,2668,2716,2740,2758,3102,3180,3188,3228,3244,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2150 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2150 5 (fun x => (if x<2668 then (if x<1686 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1614 then 0 else (if x<1678 then 1 else 2))) else (if x<1764 then (if x<1740 then 1 else (if x<1748 then 0 else 2)) else (if x<2606 then 1 else (if x<2652 then 2 else 0)))) else (if x<3180 then (if x<2740 then (if x<2716 then 1 else 2) else (if x<2758 then 1 else (if x<3102 then 1 else 3))) else (if x<3244 then (if x<3188 then 0 else (if x<3228 then 3 else 0)) else (if x<3252 then 3 else (if x<3270 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2151 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1678,1686,1692,1708,1734,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3132,3150,3180,3188,3214,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2151 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2151 1734 5
  · have he : independentCachedBranchMembers2151.erase 1734=independentCachedBranchMembers2149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2149
  · have he : independentCachedBranchMembers2151.filter (independentCachedEdge 1734)=independentCachedBranchMembers2150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2150
def independentCachedBranchMembers2152 : Finset ℕ := ([12,132,222,1590,1596,1628,1678,1748,1764,2606,2710,2716,2758,2764,3102,3150,3188,3228,3238,3244,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2152 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2152 5 (fun x => (if x<2716 then (if x<1628 then (if x<222 then (if x<132 then 0 else 1) else (if x<1590 then 0 else (if x<1596 then 2 else 3))) else (if x<1764 then (if x<1678 then 0 else (if x<1748 then 0 else 1)) else (if x<2606 then 2 else (if x<2710 then 3 else 1)))) else (if x<3188 then (if x<2764 then (if x<2758 then 0 else 3) else (if x<3102 then 1 else (if x<3150 then 0 else 4))) else (if x<3244 then (if x<3228 then 2 else (if x<3238 then 1 else 2)) else (if x<3270 then 4 else (if x<3276 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2153 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1652,1678,1686,1692,1708,1734,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3132,3150,3180,3188,3214,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2153 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2153 1652 5
  · have he : independentCachedBranchMembers2153.erase 1652=independentCachedBranchMembers2151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2151
  · have he : independentCachedBranchMembers2153.filter (independentCachedEdge 1652)=independentCachedBranchMembers2152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2152
def independentCachedBranchMembers2154 : Finset ℕ := ([12,252,1596,1614,1628,1652,1686,1708,1740,1764,2606,2620,2652,2710,2764,2788,3102,3180,3214,3228,3238,3252,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2154 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2154 5 (fun x => (if x<2652 then (if x<1686 then (if x<1614 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1628 then 1 else (if x<1652 then 2 else 1))) else (if x<1764 then (if x<1708 then 1 else (if x<1740 then 1 else 0)) else (if x<2606 then 2 else (if x<2620 then 3 else 4)))) else (if x<3214 then (if x<2788 then (if x<2710 then 0 else (if x<2764 then 3 else 2)) else (if x<3102 then 3 else (if x<3180 then 3 else 0))) else (if x<3252 then (if x<3228 then 1 else (if x<3238 then 0 else 3)) else (if x<3270 then 1 else (if x<3284 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2155 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1652,1678,1686,1692,1708,1734,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3132,3150,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2155 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2155 3222 5
  · have he : independentCachedBranchMembers2155.erase 3222=independentCachedBranchMembers2153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2153
  · have he : independentCachedBranchMembers2155.filter (independentCachedEdge 3222)=independentCachedBranchMembers2154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2154
def independentCachedBranchMembers2156 : Finset ℕ := ([132,1590,1628,1678,1686,1708,1734,1764,2606,2652,2702,2710,2740,2758,2788,3102,3132,3150,3180,3188,3228,3238,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2156 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2156 5 (fun x => (if x<2740 then (if x<1734 then (if x<1678 then (if x<1590 then 0 else (if x<1628 then 1 else 1)) else (if x<1686 then 0 else (if x<1708 then 2 else 1))) else (if x<2652 then (if x<1764 then 1 else (if x<2606 then 0 else 3)) else (if x<2702 then 3 else (if x<2710 then 2 else 3)))) else (if x<3180 then (if x<3102 then (if x<2758 then 2 else (if x<2788 then 0 else 3)) else (if x<3132 then 3 else (if x<3150 then 1 else 4))) else (if x<3238 then (if x<3188 then 3 else (if x<3228 then 4 else 2)) else (if x<3276 then 0 else (if x<3284 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2157 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1652,1678,1686,1692,1708,1734,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3132,3150,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2157 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2157 3164 5
  · have he : independentCachedBranchMembers2157.erase 3164=independentCachedBranchMembers2155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2155
  · have he : independentCachedBranchMembers2157.filter (independentCachedEdge 3164)=independentCachedBranchMembers2156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2156
def independentCachedBranchMembers2158 : Finset ℕ := ([12,222,252,1590,1628,1678,1708,1734,1764,2620,2646,2668,2716,2764,3102,3132,3150,3180,3188,3228,3238,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2158 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2158 5 (fun x => (if x<2668 then (if x<1678 then (if x<252 then (if x<222 then 0 else 0) else (if x<1590 then 1 else (if x<1628 then 2 else 0))) else (if x<1764 then (if x<1708 then 0 else (if x<1734 then 1 else 2)) else (if x<2620 then 3 else (if x<2646 then 1 else 2)))) else (if x<3180 then (if x<3102 then (if x<2716 then 3 else (if x<2764 then 0 else 1)) else (if x<3132 then 0 else (if x<3150 then 4 else 4))) else (if x<3238 then (if x<3188 then 1 else (if x<3228 then 3 else 1)) else (if x<3276 then 4 else (if x<3284 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2159 : Finset ℕ := ([12,252,1590,1678,1734,2620,2764,3132,3150,3188,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2159 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2159 4 (fun x => (if x<2620 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1678 then 1 else (if x<1734 then 1 else 2))) else (if x<3150 then (if x<2764 then 0 else (if x<3132 then 0 else 2)) else (if x<3188 then 2 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2160 : Finset ℕ := ([12,222,252,1590,1628,1678,1686,1708,1734,1764,2620,2646,2668,2716,2764,3102,3132,3150,3180,3188,3228,3238,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2160 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2160 1686 4
  · have he : independentCachedBranchMembers2160.erase 1686=independentCachedBranchMembers2158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2158
  · have he : independentCachedBranchMembers2160.filter (independentCachedEdge 1686)=independentCachedBranchMembers2159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2159
def independentCachedBranchMembers2161 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3132,3150,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2161 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2161 1702 5
  · have he : independentCachedBranchMembers2161.erase 1702=independentCachedBranchMembers2157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2157
  · have he : independentCachedBranchMembers2161.filter (independentCachedEdge 1702)=independentCachedBranchMembers2160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2160
def independentCachedBranchMembers2162 : Finset ℕ := ([132,222,1596,1614,1628,1652,1686,1708,1740,1764,2646,2668,2702,2716,2740,2758,3102,3180,3214,3228,3238,3252,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2162 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2162 5 (fun x => (if x<2702 then (if x<1686 then (if x<1614 then (if x<222 then 0 else (if x<1596 then 0 else 1)) else (if x<1628 then 1 else (if x<1652 then 2 else 3))) else (if x<1764 then (if x<1708 then 0 else (if x<1740 then 2 else 0)) else (if x<2646 then 1 else (if x<2668 then 2 else 1)))) else (if x<3214 then (if x<2758 then (if x<2716 then 0 else (if x<2740 then 2 else 1)) else (if x<3102 then 1 else (if x<3180 then 4 else 3))) else (if x<3252 then (if x<3228 then 3 else (if x<3238 then 0 else 4)) else (if x<3270 then 3 else (if x<3284 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2163 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2788,3102,3132,3150,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2163 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2163 1644 5
  · have he : independentCachedBranchMembers2163.erase 1644=independentCachedBranchMembers2161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2161
  · have he : independentCachedBranchMembers2163.filter (independentCachedEdge 1644)=independentCachedBranchMembers2162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2162
def independentCachedBranchMembers2164 : Finset ℕ := ([12,1590,1596,1614,1644,1678,1708,1748,2606,2646,2652,2710,2716,2740,2758,2764,2788,3102,3132,3150,3180,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2164 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2164 5 (fun x => (if x<2716 then (if x<1708 then (if x<1614 then (if x<1590 then 0 else (if x<1596 then 1 else 0)) else (if x<1644 then 0 else (if x<1678 then 1 else 1))) else (if x<2646 then (if x<1748 then 2 else (if x<2606 then 1 else 0)) else (if x<2652 then 2 else (if x<2710 then 0 else 1)))) else (if x<3132 then (if x<2764 then (if x<2740 then 2 else (if x<2758 then 3 else 3)) else (if x<2788 then 1 else (if x<3102 then 2 else 0))) else (if x<3238 then (if x<3150 then 3 else (if x<3180 then 3 else 0)) else (if x<3244 then 3 else (if x<3284 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2165 : Finset ℕ := ([1590,1596,1644,1678,1748,2646,2652,2740,2788,3102,3150,3238,3244] : List ℕ).toFinset
theorem independentCachedBranchBound2165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2165 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2165 4 (fun x => (if x<2652 then (if x<1678 then (if x<1596 then 0 else (if x<1644 then 1 else 0)) else (if x<1748 then 0 else (if x<2646 then 0 else 2))) else (if x<3102 then (if x<2740 then 1 else (if x<2788 then 1 else 2)) else (if x<3238 then (if x<3150 then 2 else 3) else (if x<3244 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2166 : Finset ℕ := ([12,1590,1596,1614,1644,1678,1708,1748,2606,2646,2652,2710,2716,2740,2758,2764,2788,3102,3132,3150,3180,3214,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2166 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2166 3214 4
  · have he : independentCachedBranchMembers2166.erase 3214=independentCachedBranchMembers2164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2164
  · have he : independentCachedBranchMembers2166.filter (independentCachedEdge 3214)=independentCachedBranchMembers2165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2165
def independentCachedBranchMembers2167 : Finset ℕ := ([12,1590,1678,1708,2646,2716,2764,3102,3132,3150,3180,3238,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2167 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2167 4 (fun x => (if x<2764 then (if x<1708 then (if x<1590 then 0 else (if x<1678 then 1 else 0)) else (if x<2646 then 1 else (if x<2716 then 1 else 0))) else (if x<3150 then (if x<3102 then 1 else (if x<3132 then 0 else 2)) else (if x<3238 then (if x<3180 then 2 else 3) else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2168 : Finset ℕ := ([12,1590,1596,1614,1644,1678,1702,1708,1748,2606,2646,2652,2710,2716,2740,2758,2764,2788,3102,3132,3150,3180,3214,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2168 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2168 1702 4
  · have he : independentCachedBranchMembers2168.erase 1702=independentCachedBranchMembers2166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2166
  · have he : independentCachedBranchMembers2168.filter (independentCachedEdge 1702)=independentCachedBranchMembers2167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2167
def independentCachedBranchMembers2169 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2740,2758,2764,2772,2788,3102,3132,3150,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2169 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2169 2772 5
  · have he : independentCachedBranchMembers2169.erase 2772=independentCachedBranchMembers2163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2163
  · have he : independentCachedBranchMembers2169.filter (independentCachedEdge 2772)=independentCachedBranchMembers2168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2168
def independentCachedBranchMembers2170 : Finset ℕ := ([222,1590,1614,1628,1686,1708,1734,1748,2606,2620,2646,2668,2702,2716,2740,2764,2788,3102,3150,3188,3222,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2170 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2170 5 (fun x => (if x<2702 then (if x<1734 then (if x<1628 then (if x<1590 then 0 else (if x<1614 then 1 else 0)) else (if x<1686 then 1 else (if x<1708 then 0 else 1))) else (if x<2620 then (if x<1748 then 1 else (if x<2606 then 2 else 2)) else (if x<2646 then 1 else (if x<2668 then 0 else 3)))) else (if x<3150 then (if x<2764 then (if x<2716 then 0 else (if x<2740 then 2 else 3)) else (if x<2788 then 1 else (if x<3102 then 2 else 0))) else (if x<3244 then (if x<3188 then 3 else (if x<3222 then 3 else 3)) else (if x<3270 then 3 else (if x<3284 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2171 : Finset ℕ := ([1590,1628,1686,1708,1734,2606,2702,2740,2788,3102,3150,3188,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2171 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2171 4 (fun x => (if x<2702 then (if x<1708 then (if x<1628 then 0 else (if x<1686 then 0 else 1)) else (if x<1734 then 0 else (if x<2606 then 0 else 2))) else (if x<3102 then (if x<2740 then 1 else (if x<2788 then 1 else 2)) else (if x<3188 then (if x<3150 then 2 else 3) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2172 : Finset ℕ := ([222,1590,1614,1628,1686,1708,1734,1748,2606,2620,2646,2668,2702,2716,2740,2764,2788,3102,3150,3164,3188,3222,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2172 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2172 3164 4
  · have he : independentCachedBranchMembers2172.erase 3164=independentCachedBranchMembers2170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2170
  · have he : independentCachedBranchMembers2172.filter (independentCachedEdge 3164)=independentCachedBranchMembers2171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2171
def independentCachedBranchMembers2173 : Finset ℕ := ([222,1590,1628,1748,2606,2716,2764,3102,3150,3188,3222,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2173 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2173 4 (fun x => (if x<2764 then (if x<1748 then (if x<1590 then 0 else (if x<1628 then 1 else 0)) else (if x<2606 then 1 else (if x<2716 then 1 else 0))) else (if x<3188 then (if x<3102 then 1 else (if x<3150 then 0 else 2)) else (if x<3244 then (if x<3222 then 2 else 2) else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2174 : Finset ℕ := ([222,1590,1614,1628,1652,1686,1708,1734,1748,2606,2620,2646,2668,2702,2716,2740,2764,2788,3102,3150,3164,3188,3222,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2174 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2174 1652 4
  · have he : independentCachedBranchMembers2174.erase 1652=independentCachedBranchMembers2172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2172
  · have he : independentCachedBranchMembers2174.filter (independentCachedEdge 1652)=independentCachedBranchMembers2173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2173
def independentCachedBranchMembers2175 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2620,2646,2652,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3132,3150,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2175 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2175 2732 5
  · have he : independentCachedBranchMembers2175.erase 2732=independentCachedBranchMembers2169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2169
  · have he : independentCachedBranchMembers2175.filter (independentCachedEdge 2732)=independentCachedBranchMembers2174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2174
end EntropyDesigns.QuadraticRefinement
