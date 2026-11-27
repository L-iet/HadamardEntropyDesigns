/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch104
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6144 : Finset ℕ := ([1652,1764,2740,2776,3174,3226] : List ℕ).toFinset
theorem independentCachedBranchBound6144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6144 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6144 3 (fun x => (if x<2776 then (if x<1764 then 0 else (if x<2740 then 1 else 0)) else (if x<3174 then 2 else (if x<3226 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6145 : Finset ℕ := ([40,68,1642,1652,1686,1764,2618,2646,2730,2740,2758,2776,3174,3192,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6145 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6145 40 3
  · have he : independentCachedBranchMembers6145.erase 40=independentCachedBranchMembers6143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6143
  · have he : independentCachedBranchMembers6145.filter (independentCachedEdge 40)=independentCachedBranchMembers6144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6144
def independentCachedBranchMembers6146 : Finset ℕ := ([40,68,136,250,1590,1626,1642,1652,1686,1720,1738,1748,1764,2618,2646,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3242,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6146 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6146 3288 4
  · have he : independentCachedBranchMembers6146.erase 3288=independentCachedBranchMembers6142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6142
  · have he : independentCachedBranchMembers6146.filter (independentCachedEdge 3288)=independentCachedBranchMembers6145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6145
def independentCachedBranchMembers6147 : Finset ℕ := ([250,1590,1626,1642,1652,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6147 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6147 4 (fun x => (if x<2740 then (if x<1642 then (if x<1590 then 0 else (if x<1626 then 1 else 0)) else (if x<2714 then (if x<1652 then 1 else 2) else (if x<2730 then 0 else 2))) else (if x<3130 then (if x<2776 then (if x<2758 then 1 else 3) else (if x<2792 then 3 else 1)) else (if x<3174 then (if x<3158 then 0 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6148 : Finset ℕ := ([1626,1642,2740,2758,3130,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6148 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6148 3 (fun x => (if x<2758 then (if x<1642 then 0 else (if x<2740 then 1 else 0)) else (if x<3130 then 2 else (if x<3192 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6149 : Finset ℕ := ([136,250,1590,1626,1642,1652,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6149 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6149 136 3
  · have he : independentCachedBranchMembers6149.erase 136=independentCachedBranchMembers6147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6147
  · have he : independentCachedBranchMembers6149.filter (independentCachedEdge 136)=independentCachedBranchMembers6148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6148
def independentCachedBranchMembers6150 : Finset ℕ := ([40,68,136,250,1590,1626,1642,1652,1686,1720,1738,1748,1764,2618,2646,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3242,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6150 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6150 3270 4
  · have he : independentCachedBranchMembers6150.erase 3270=independentCachedBranchMembers6146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6146
  · have he : independentCachedBranchMembers6150.filter (independentCachedEdge 3270)=independentCachedBranchMembers6149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6149
def independentCachedBranchMembers6151 : Finset ℕ := ([40,68,136,250,1590,1626,1686,1764,2618,2646,2714,2792,3130,3158,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6151 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6151 4 (fun x => (if x<2618 then (if x<1590 then (if x<136 then (if x<68 then 0 else 0) else (if x<250 then 1 else 1)) else (if x<1686 then (if x<1626 then 2 else 2) else (if x<1764 then 3 else 3))) else (if x<3130 then (if x<2714 then (if x<2646 then 0 else 0) else (if x<2792 then 1 else 1)) else (if x<3226 then (if x<3158 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6152 : Finset ℕ := ([40,68,136,250,1590,1626,1642,1652,1686,1702,1720,1738,1748,1764,2618,2646,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3226,3242,3252,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6152 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6152 1702 4
  · have he : independentCachedBranchMembers6152.erase 1702=independentCachedBranchMembers6150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6150
  · have he : independentCachedBranchMembers6152.filter (independentCachedEdge 1702)=independentCachedBranchMembers6151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6151
def independentCachedBranchMembers6153 : Finset ℕ := ([12,18,34,40,68,80,130,136,192,222,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2764,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6153 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6153 12 5
  · have he : independentCachedBranchMembers6153.erase 12=independentCachedBranchMembers6127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6127
  · have he : independentCachedBranchMembers6153.filter (independentCachedEdge 12)=independentCachedBranchMembers6152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6152
def independentCachedBranchMembers6154 : Finset ℕ := ([136,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3118,3158,3174,3192,3226,3242,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6154 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6154 5 (fun x => (if x<2674 then (if x<1714 then (if x<1614 then (if x<238 then 0 else (if x<1590 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 1 else 0))) else (if x<1764 then (if x<1738 then 2 else (if x<1748 then 0 else 2)) else (if x<2652 then (if x<2618 then 1 else 2) else (if x<2668 then 2 else 3)))) else (if x<3174 then (if x<2776 then (if x<2702 then 3 else (if x<2758 then 0 else 3)) else (if x<3118 then (if x<2792 then 3 else 0) else (if x<3158 then 4 else 4))) else (if x<3242 then (if x<3192 then 1 else (if x<3226 then 3 else 4)) else (if x<3276 then (if x<3252 then 0 else 1) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6155 : Finset ℕ := ([1590,1692,1708,1738,2674,2702,2776,2792,3118,3192,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6155 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6155 4 (fun x => (if x<2776 then (if x<1738 then (if x<1692 then 0 else (if x<1708 then 0 else 1)) else (if x<2674 then 1 else (if x<2702 then 0 else 1))) else (if x<3192 then (if x<2792 then 0 else (if x<3118 then 1 else 2)) else (if x<3252 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6156 : Finset ℕ := ([68,136,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3118,3158,3174,3192,3226,3242,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6156 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6156 68 4
  · have he : independentCachedBranchMembers6156.erase 68=independentCachedBranchMembers6154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6154
  · have he : independentCachedBranchMembers6156.filter (independentCachedEdge 68)=independentCachedBranchMembers6155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6155
def independentCachedBranchMembers6157 : Finset ℕ := ([1614,1708,1738,1764,2668,2702,2758,2792,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6157 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6157 4 (fun x => (if x<2758 then (if x<1764 then (if x<1708 then 0 else (if x<1738 then 0 else 1)) else (if x<2668 then 1 else (if x<2702 then 0 else 0))) else (if x<3192 then (if x<2792 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6158 : Finset ℕ := ([34,68,136,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3118,3158,3174,3192,3226,3242,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6158 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6158 34 4
  · have he : independentCachedBranchMembers6158.erase 34=independentCachedBranchMembers6156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6156
  · have he : independentCachedBranchMembers6158.filter (independentCachedEdge 34)=independentCachedBranchMembers6157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6157
def independentCachedBranchMembers6159 : Finset ℕ := ([34,68,136,238,1590,1614,1692,1764,2618,2652,2702,2792,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6159 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6159 4 (fun x => (if x<2618 then (if x<1590 then (if x<136 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3118 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6160 : Finset ℕ := ([34,68,136,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6160 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6160 3282 4
  · have he : independentCachedBranchMembers6160.erase 3282=independentCachedBranchMembers6158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6158
  · have he : independentCachedBranchMembers6160.filter (independentCachedEdge 3282)=independentCachedBranchMembers6159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6159
def independentCachedBranchMembers6161 : Finset ℕ := ([34,68,136,238,1708,1714,1738,1748,2668,2674,2758,2776,3118,3158,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6161 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6161 4 (fun x => (if x<2668 then (if x<1708 then (if x<136 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3118 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3226 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6162 : Finset ℕ := ([34,68,136,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6162 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6162 3102 4
  · have he : independentCachedBranchMembers6162.erase 3102=independentCachedBranchMembers6160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6160
  · have he : independentCachedBranchMembers6162.filter (independentCachedEdge 3102)=independentCachedBranchMembers6161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6161
def independentCachedBranchMembers6163 : Finset ℕ := ([1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6163 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6163 4 (fun x => (if x<2618 then (if x<1714 then (if x<1692 then (if x<1614 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<2702 then (if x<2668 then (if x<2652 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2776 then (if x<2758 then 2 else 3) else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6164 : Finset ℕ := ([34,68,136,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6164 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6164 3072 4
  · have he : independentCachedBranchMembers6164.erase 3072=independentCachedBranchMembers6162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6162
  · have he : independentCachedBranchMembers6164.filter (independentCachedEdge 3072)=independentCachedBranchMembers6163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6163
def independentCachedBranchMembers6165 : Finset ℕ := ([34,238,1590,1708,1714,1764,2618,2668,2674,2792,3118,3174,3192,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6165 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6165 4 (fun x => (if x<2674 then (if x<1714 then (if x<1590 then (if x<238 then 0 else 0) else (if x<1708 then 1 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2668 then 2 else 2))) else (if x<3192 then (if x<3118 then (if x<2792 then 1 else 1) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6166 : Finset ℕ := ([34,68,136,222,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6166 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6166 222 4
  · have he : independentCachedBranchMembers6166.erase 222=independentCachedBranchMembers6164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6164
  · have he : independentCachedBranchMembers6166.filter (independentCachedEdge 222)=independentCachedBranchMembers6165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6165
def independentCachedBranchMembers6167 : Finset ℕ := ([68,136,1614,1692,1708,1714,2652,2668,2674,2702,3158,3174,3192,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6167 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6167 4 (fun x => (if x<2674 then (if x<1708 then (if x<1614 then (if x<136 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3192 then (if x<3158 then (if x<2702 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3226 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6168 : Finset ℕ := ([34,68,136,192,222,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6168 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6168 192 4
  · have he : independentCachedBranchMembers6168.erase 192=independentCachedBranchMembers6166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6166
  · have he : independentCachedBranchMembers6168.filter (independentCachedEdge 192)=independentCachedBranchMembers6167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6167
def independentCachedBranchMembers6169 : Finset ℕ := ([34,238,1614,1692,1738,1748,2652,2702,2758,2776,3118,3174,3192,3242,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6169 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6169 4 (fun x => (if x<2758 then (if x<1738 then (if x<1614 then (if x<238 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1748 then 2 else 2) else (if x<2702 then 1 else 1))) else (if x<3192 then (if x<3118 then (if x<2776 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6170 : Finset ℕ := ([18,34,68,136,192,222,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6170 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6170 18 4
  · have he : independentCachedBranchMembers6170.erase 18=independentCachedBranchMembers6168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6168
  · have he : independentCachedBranchMembers6170.filter (independentCachedEdge 18)=independentCachedBranchMembers6169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6169
def independentCachedBranchMembers6171 : Finset ℕ := ([68,136,1590,1738,1748,1764,2618,2758,2776,2792,3158,3174,3192,3226,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6171 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6171 4 (fun x => (if x<2776 then (if x<1748 then (if x<1590 then (if x<136 then 0 else 0) else (if x<1738 then 1 else 2)) else (if x<2618 then (if x<1764 then 1 else 2) else (if x<2758 then 1 else 2))) else (if x<3192 then (if x<3158 then (if x<2792 then 1 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3226 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6172 : Finset ℕ := ([12,18,34,68,136,192,222,238,1590,1614,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2702,2758,2776,2792,3072,3102,3118,3158,3174,3192,3226,3242,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6172 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6172 12 4
  · have he : independentCachedBranchMembers6172.erase 12=independentCachedBranchMembers6170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6170
  · have he : independentCachedBranchMembers6172.filter (independentCachedEdge 12)=independentCachedBranchMembers6171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6171
def independentCachedBranchMembers6173 : Finset ℕ := ([12,18,34,40,68,80,130,136,192,222,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2680,2702,2714,2730,2740,2758,2764,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6173 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6173 2680 5
  · have he : independentCachedBranchMembers6173.erase 2680=independentCachedBranchMembers6153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6153
  · have he : independentCachedBranchMembers6173.filter (independentCachedEdge 2680)=independentCachedBranchMembers6172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6172
def independentCachedBranchMembers6174 : Finset ℕ := ([130,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3130,3164,3174,3192,3214,3242,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6174 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6174 5 (fun x => (if x<2674 then (if x<1714 then (if x<1626 then (if x<250 then 0 else (if x<1596 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 1 else 2))) else (if x<1776 then (if x<1738 then 0 else (if x<1748 then 0 else 2)) else (if x<2646 then (if x<2606 then 1 else 2) else (if x<2668 then 2 else 3)))) else (if x<3174 then (if x<2776 then (if x<2714 then 3 else (if x<2758 then 0 else 3)) else (if x<3130 then (if x<2786 then 3 else 0) else (if x<3164 then 4 else 4))) else (if x<3242 then (if x<3192 then 3 else (if x<3214 then 1 else 4)) else (if x<3282 then (if x<3252 then 0 else 1) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6175 : Finset ℕ := ([1596,1686,1714,1738,2668,2714,2758,2786,3130,3174,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6175 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6175 4 (fun x => (if x<2758 then (if x<1738 then (if x<1686 then 0 else (if x<1714 then 0 else 1)) else (if x<2668 then 1 else (if x<2714 then 0 else 1))) else (if x<3174 then (if x<2786 then 0 else (if x<3130 then 1 else 2)) else (if x<3252 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
