/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch229
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10144 : Finset ℕ := ([18,40,80,144,246,1582,1622,1644,1650,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2710,2732,2738,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10144 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10144 18 4
  · have he : independentCachedBranchMembers10144.erase 18=independentCachedBranchMembers10142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10142
  · have he : independentCachedBranchMembers10144.filter (independentCachedEdge 18)=independentCachedBranchMembers10143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10143
def independentCachedBranchMembers10145 : Finset ℕ := ([40,246,1622,1686,1738,1748,2646,2710,2762,2772,3126,3178,3188,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10145 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10145 4 (fun x => (if x<2762 then (if x<1738 then (if x<1622 then (if x<246 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<2646 then (if x<1748 then 2 else 2) else (if x<2710 then 1 else 0))) else (if x<3188 then (if x<3126 then (if x<2772 then 3 else 3) else (if x<3178 then 1 else 2)) else (if x<3252 then (if x<3242 then 2 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10146 : Finset ℕ := ([12,18,40,80,144,246,1582,1622,1644,1650,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2710,2732,2738,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10146 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10146 12 4
  · have he : independentCachedBranchMembers10146.erase 12=independentCachedBranchMembers10144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10144
  · have he : independentCachedBranchMembers10146.filter (independentCachedEdge 12)=independentCachedBranchMembers10145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10145
def independentCachedBranchMembers10147 : Finset ℕ := ([12,18,40,48,72,80,136,144,238,246,1582,1590,1614,1622,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10147 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10147 3274 5
  · have he : independentCachedBranchMembers10147.erase 3274=independentCachedBranchMembers10125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10125
  · have he : independentCachedBranchMembers10147.filter (independentCachedEdge 3274)=independentCachedBranchMembers10146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10146
def independentCachedBranchMembers10148 : Finset ℕ := ([136,238,1582,1622,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10148 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10148 5 (fun x => (if x<2676 then (if x<1716 then (if x<1622 then (if x<238 then 0 else (if x<1582 then 0 else 1)) else (if x<1678 then 1 else (if x<1706 then 0 else 2))) else (if x<1768 then (if x<1740 then 1 else (if x<1746 then 1 else 2)) else (if x<2638 then (if x<2614 then 0 else 1) else (if x<2666 then 1 else 3)))) else (if x<3158 then (if x<2762 then (if x<2710 then 3 else (if x<2732 then 4 else 0)) else (if x<2800 then (if x<2772 then 0 else 1) else (if x<3118 then 4 else 2))) else (if x<3214 then (if x<3180 then 2 else (if x<3186 then 3 else 3)) else (if x<3252 then (if x<3242 then 4 else 0) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10149 : Finset ℕ := ([238,1716,1740,1768,2614,2638,2666,2710,2762,3180,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10149 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10149 4 (fun x => (if x<2666 then (if x<1768 then (if x<1716 then 0 else (if x<1740 then 1 else 0)) else (if x<2614 then 1 else (if x<2638 then 1 else 0))) else (if x<3180 then (if x<2710 then 1 else (if x<2762 then 2 else 2)) else (if x<3252 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10150 : Finset ℕ := ([80,136,238,1582,1622,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10150 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10150 80 4
  · have he : independentCachedBranchMembers10150.erase 80=independentCachedBranchMembers10148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10148
  · have he : independentCachedBranchMembers10150.filter (independentCachedEdge 80)=independentCachedBranchMembers10149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10149
def independentCachedBranchMembers10151 : Finset ℕ := ([136,1678,1716,1740,2614,2638,2676,2762,2800,3186,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10151 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10151 4 (fun x => (if x<2676 then (if x<1740 then (if x<1678 then 0 else (if x<1716 then 0 else 1)) else (if x<2614 then 1 else (if x<2638 then 1 else 1))) else (if x<3186 then (if x<2762 then 0 else (if x<2800 then 2 else 2)) else (if x<3214 then 0 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10152 : Finset ℕ := ([40,80,136,238,1582,1622,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10152 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10152 40 4
  · have he : independentCachedBranchMembers10152.erase 40=independentCachedBranchMembers10150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10150
  · have he : independentCachedBranchMembers10152.filter (independentCachedEdge 40)=independentCachedBranchMembers10151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10151
def independentCachedBranchMembers10153 : Finset ℕ := ([136,238,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,3118,3158,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10153 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10153 4 (fun x => (if x<2614 then (if x<1716 then (if x<1678 then (if x<238 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3118 then (if x<2666 then (if x<2638 then 2 else 2) else (if x<2676 then 3 else 3)) else (if x<3180 then (if x<3158 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10154 : Finset ℕ := ([40,80,136,238,1582,1622,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10154 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10154 3282 4
  · have he : independentCachedBranchMembers10154.erase 3282=independentCachedBranchMembers10152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10152
  · have he : independentCachedBranchMembers10154.filter (independentCachedEdge 3282)=independentCachedBranchMembers10153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10153
def independentCachedBranchMembers10155 : Finset ℕ := ([40,80,1582,1622,1706,1716,1740,1746,2666,2676,2710,2800,3180,3186,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10155 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10155 4 (fun x => (if x<2666 then (if x<1706 then (if x<1582 then (if x<80 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1740 then (if x<1716 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3180 then (if x<2710 then (if x<2676 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3186 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10156 : Finset ℕ := ([40,80,136,238,1582,1622,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10156 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10156 3276 4
  · have he : independentCachedBranchMembers10156.erase 3276=independentCachedBranchMembers10154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10154
  · have he : independentCachedBranchMembers10156.filter (independentCachedEdge 3276)=independentCachedBranchMembers10155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10155
def independentCachedBranchMembers10157 : Finset ℕ := ([40,80,136,238,1582,1622,1678,1768,2614,2638,2710,2800,3118,3158,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10157 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10157 4 (fun x => (if x<2614 then (if x<1582 then (if x<136 then (if x<80 then 0 else 0) else (if x<238 then 1 else 1)) else (if x<1678 then (if x<1622 then 0 else 0) else (if x<1768 then 1 else 1))) else (if x<3118 then (if x<2710 then (if x<2638 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3158 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10158 : Finset ℕ := ([40,80,136,238,1582,1622,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2738,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10158 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10158 2738 4
  · have he : independentCachedBranchMembers10158.erase 2738=independentCachedBranchMembers10156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10156
  · have he : independentCachedBranchMembers10158.filter (independentCachedEdge 2738)=independentCachedBranchMembers10157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10157
def independentCachedBranchMembers10159 : Finset ℕ := ([40,238,1622,1678,1740,1746,2638,2710,2762,2772,3118,3180,3186,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10159 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10159 4 (fun x => (if x<2762 then (if x<1740 then (if x<1622 then (if x<238 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1746 then 2 else 2) else (if x<2710 then 1 else 1))) else (if x<3186 then (if x<3118 then (if x<2772 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10160 : Finset ℕ := ([40,80,136,238,1582,1622,1650,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2738,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10160 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10160 1650 4
  · have he : independentCachedBranchMembers10160.erase 1650=independentCachedBranchMembers10158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10158
  · have he : independentCachedBranchMembers10160.filter (independentCachedEdge 1650)=independentCachedBranchMembers10159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10159
def independentCachedBranchMembers10161 : Finset ℕ := ([80,136,1582,1740,1746,1768,2614,2762,2772,2800,3158,3180,3186,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10161 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10161 4 (fun x => (if x<2772 then (if x<1746 then (if x<1582 then (if x<136 then 0 else 0) else (if x<1740 then 1 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2762 then 1 else 2))) else (if x<3186 then (if x<3158 then (if x<2800 then 1 else 2) else (if x<3180 then 0 else 3)) else (if x<3242 then (if x<3214 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10162 : Finset ℕ := ([40,80,136,238,1582,1622,1644,1650,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2738,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10162 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10162 1644 4
  · have he : independentCachedBranchMembers10162.erase 1644=independentCachedBranchMembers10160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10160
  · have he : independentCachedBranchMembers10162.filter (independentCachedEdge 1644)=independentCachedBranchMembers10161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10161
def independentCachedBranchMembers10163 : Finset ℕ := ([80,238,1582,1678,1706,1716,2638,2666,2676,2762,2772,2800,3118,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10163 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10163 4 (fun x => (if x<2676 then (if x<1706 then (if x<1582 then (if x<238 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<2638 then (if x<1716 then 2 else 2) else (if x<2666 then 1 else 2))) else (if x<3118 then (if x<2772 then (if x<2762 then 2 else 3) else (if x<2800 then 0 else 3)) else (if x<3242 then (if x<3214 then 1 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10164 : Finset ℕ := ([18,40,80,136,238,1582,1622,1644,1650,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2738,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10164 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10164 18 4
  · have he : independentCachedBranchMembers10164.erase 18=independentCachedBranchMembers10162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10162
  · have he : independentCachedBranchMembers10164.filter (independentCachedEdge 18)=independentCachedBranchMembers10163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10163
def independentCachedBranchMembers10165 : Finset ℕ := ([40,136,1622,1706,1716,1768,2614,2666,2676,2710,2762,2772,3158,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10165 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10165 4 (fun x => (if x<2676 then (if x<1716 then (if x<1622 then (if x<136 then 0 else 1) else (if x<1706 then 0 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2666 then 2 else 2))) else (if x<3158 then (if x<2762 then (if x<2710 then 1 else 0) else (if x<2772 then 3 else 3)) else (if x<3252 then (if x<3242 then 1 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10166 : Finset ℕ := ([12,18,40,80,136,238,1582,1622,1644,1650,1678,1706,1716,1740,1746,1768,2614,2638,2666,2676,2710,2732,2738,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10166 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10166 12 4
  · have he : independentCachedBranchMembers10166.erase 12=independentCachedBranchMembers10164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10164
  · have he : independentCachedBranchMembers10166.filter (independentCachedEdge 12)=independentCachedBranchMembers10165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10165
def independentCachedBranchMembers10167 : Finset ℕ := ([12,18,40,48,72,80,136,144,238,246,1582,1590,1614,1622,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10167 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10167 2740 5
  · have he : independentCachedBranchMembers10167.erase 2740=independentCachedBranchMembers10147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10147
  · have he : independentCachedBranchMembers10167.filter (independentCachedEdge 2740)=independentCachedBranchMembers10166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10166
def independentCachedBranchMembers10168 : Finset ℕ := ([144,246,1590,1614,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10168 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10168 5 (fun x => (if x<2676 then (if x<1716 then (if x<1614 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1686 then 1 else (if x<1706 then 0 else 1))) else (if x<1776 then (if x<1740 then 2 else (if x<1746 then 2 else 1)) else (if x<2646 then (if x<2606 then 0 else 1) else (if x<2666 then 1 else 3)))) else (if x<3150 then (if x<2762 then (if x<2702 then 3 else (if x<2738 then 4 else 0)) else (if x<2792 then (if x<2772 then 1 else 0) else (if x<3126 then 4 else 2))) else (if x<3222 then (if x<3180 then 2 else (if x<3186 then 3 else 3)) else (if x<3252 then (if x<3242 then 4 else 3) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10169 : Finset ℕ := ([246,1706,1746,1776,2606,2646,2676,2702,2772,3186,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10169 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10169 4 (fun x => (if x<2676 then (if x<1776 then (if x<1706 then 0 else (if x<1746 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 1 else 0))) else (if x<3186 then (if x<2702 then 1 else (if x<2772 then 2 else 2)) else (if x<3242 then 0 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10170 : Finset ℕ := ([72,144,246,1590,1614,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10170 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10170 72 4
  · have he : independentCachedBranchMembers10170.erase 72=independentCachedBranchMembers10168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10168
  · have he : independentCachedBranchMembers10170.filter (independentCachedEdge 72)=independentCachedBranchMembers10169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10169
def independentCachedBranchMembers10171 : Finset ℕ := ([144,1686,1706,1746,2606,2646,2666,2772,2792,3180,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound10171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10171 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10171 4 (fun x => (if x<2666 then (if x<1746 then (if x<1686 then 0 else (if x<1706 then 0 else 1)) else (if x<2606 then 1 else (if x<2646 then 1 else 1))) else (if x<3180 then (if x<2772 then 0 else (if x<2792 then 2 else 2)) else (if x<3222 then 0 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10172 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10172 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10172 48 4
  · have he : independentCachedBranchMembers10172.erase 48=independentCachedBranchMembers10170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10170
  · have he : independentCachedBranchMembers10172.filter (independentCachedEdge 48)=independentCachedBranchMembers10171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10171
def independentCachedBranchMembers10173 : Finset ℕ := ([48,72,1590,1614,1706,1716,1740,1746,2666,2676,2702,2792,3180,3186,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10173 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10173 4 (fun x => (if x<2666 then (if x<1706 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1740 then (if x<1716 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3180 then (if x<2702 then (if x<2676 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3186 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10174 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10174 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10174 3282 4
  · have he : independentCachedBranchMembers10174.erase 3282=independentCachedBranchMembers10172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10172
  · have he : independentCachedBranchMembers10174.filter (independentCachedEdge 3282)=independentCachedBranchMembers10173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10173
def independentCachedBranchMembers10175 : Finset ℕ := ([144,246,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,3126,3150,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10175 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10175 4 (fun x => (if x<2606 then (if x<1716 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3126 then (if x<2666 then (if x<2646 then 2 else 2) else (if x<2676 then 3 else 3)) else (if x<3180 then (if x<3150 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
