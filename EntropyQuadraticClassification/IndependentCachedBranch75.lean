/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch74
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5184 : Finset ℕ := ([40,72,132,250,1594,1626,1642,1652,1686,1734,1752,1768,2614,2646,2680,2714,2730,2740,2762,2772,2788,3130,3162,3178,3188,3222,3238,3256,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5184 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5184 3288 4
  · have he : independentCachedBranchMembers5184.erase 3288=independentCachedBranchMembers5182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5182
  · have he : independentCachedBranchMembers5184.filter (independentCachedEdge 3288)=independentCachedBranchMembers5183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5183
def independentCachedBranchMembers5185 : Finset ℕ := ([72,250,1626,1642,1652,1734,1752,1768,2614,2714,2730,2740,3130,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5185 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5185 4 (fun x => (if x<2614 then (if x<1652 then (if x<1626 then (if x<250 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3130 then (if x<2730 then (if x<2714 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3238 then (if x<3222 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5186 : Finset ℕ := ([40,72,132,250,1594,1626,1642,1652,1686,1734,1752,1768,2614,2646,2680,2714,2730,2740,2762,2772,2788,3130,3162,3178,3188,3222,3238,3256,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5186 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5186 3270 4
  · have he : independentCachedBranchMembers5186.erase 3270=independentCachedBranchMembers5184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5184
  · have he : independentCachedBranchMembers5186.filter (independentCachedEdge 3270)=independentCachedBranchMembers5185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5185
def independentCachedBranchMembers5187 : Finset ℕ := ([40,72,132,250,1594,1626,1686,1768,2614,2646,2714,2788,3130,3162,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5187 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5187 4 (fun x => (if x<2614 then (if x<1594 then (if x<132 then (if x<72 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1686 then (if x<1626 then 0 else 1) else (if x<1768 then 0 else 1))) else (if x<3130 then (if x<2714 then (if x<2646 then 2 else 3) else (if x<2788 then 2 else 3)) else (if x<3222 then (if x<3162 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5188 : Finset ℕ := ([40,72,132,250,1594,1626,1642,1652,1686,1734,1752,1768,2614,2646,2662,2680,2714,2730,2740,2762,2772,2788,3130,3162,3178,3188,3222,3238,3256,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5188 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5188 2662 4
  · have he : independentCachedBranchMembers5188.erase 2662=independentCachedBranchMembers5186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5186
  · have he : independentCachedBranchMembers5188.filter (independentCachedEdge 2662)=independentCachedBranchMembers5187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5187
def independentCachedBranchMembers5189 : Finset ℕ := ([12,18,34,40,66,72,132,144,192,222,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3072,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5189 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5189 12 5
  · have he : independentCachedBranchMembers5189.erase 12=independentCachedBranchMembers5177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5177
  · have he : independentCachedBranchMembers5189.filter (independentCachedEdge 12)=independentCachedBranchMembers5188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5188
def independentCachedBranchMembers5190 : Finset ℕ := ([132,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3118,3162,3178,3188,3222,3238,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5190 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5190 5 (fun x => (if x<2674 then (if x<1714 then (if x<1614 then (if x<238 then 0 else (if x<1594 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 1 else 0))) else (if x<1768 then (if x<1734 then 2 else (if x<1752 then 0 else 2)) else (if x<2652 then (if x<2614 then 1 else 2) else (if x<2668 then 2 else 3)))) else (if x<3178 then (if x<2772 then (if x<2702 then 3 else (if x<2762 then 0 else 3)) else (if x<3118 then (if x<2788 then 3 else 0) else (if x<3162 then 4 else 4))) else (if x<3238 then (if x<3188 then 1 else (if x<3222 then 3 else 4)) else (if x<3276 then (if x<3256 then 0 else 1) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5191 : Finset ℕ := ([1594,1692,1708,1734,2674,2702,2772,2788,3118,3188,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5191 4 (fun x => (if x<2772 then (if x<1734 then (if x<1692 then 0 else (if x<1708 then 0 else 1)) else (if x<2674 then 1 else (if x<2702 then 0 else 1))) else (if x<3188 then (if x<2788 then 0 else (if x<3118 then 1 else 2)) else (if x<3256 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5192 : Finset ℕ := ([72,132,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3118,3162,3178,3188,3222,3238,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5192 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5192 72 4
  · have he : independentCachedBranchMembers5192.erase 72=independentCachedBranchMembers5190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5190
  · have he : independentCachedBranchMembers5192.filter (independentCachedEdge 72)=independentCachedBranchMembers5191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5191
def independentCachedBranchMembers5193 : Finset ℕ := ([1614,1708,1734,1768,2668,2702,2762,2788,3162,3188,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5193 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5193 4 (fun x => (if x<2762 then (if x<1768 then (if x<1708 then 0 else (if x<1734 then 0 else 1)) else (if x<2668 then 1 else (if x<2702 then 0 else 0))) else (if x<3188 then (if x<2788 then 1 else (if x<3162 then 1 else 2)) else (if x<3222 then 2 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5194 : Finset ℕ := ([34,72,132,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3118,3162,3178,3188,3222,3238,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5194 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5194 34 4
  · have he : independentCachedBranchMembers5194.erase 34=independentCachedBranchMembers5192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5192
  · have he : independentCachedBranchMembers5194.filter (independentCachedEdge 34)=independentCachedBranchMembers5193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5193
def independentCachedBranchMembers5195 : Finset ℕ := ([34,72,132,238,1594,1614,1692,1768,2614,2652,2702,2788,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5195 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5195 4 (fun x => (if x<2614 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3118 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5196 : Finset ℕ := ([34,72,132,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5196 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5196 3282 4
  · have he : independentCachedBranchMembers5196.erase 3282=independentCachedBranchMembers5194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5194
  · have he : independentCachedBranchMembers5196.filter (independentCachedEdge 3282)=independentCachedBranchMembers5195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5195
def independentCachedBranchMembers5197 : Finset ℕ := ([34,72,132,238,1708,1714,1734,1752,2668,2674,2762,2772,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5197 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5197 4 (fun x => (if x<2668 then (if x<1708 then (if x<132 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3118 then (if x<2762 then (if x<2674 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5198 : Finset ℕ := ([34,72,132,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5198 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5198 3102 4
  · have he : independentCachedBranchMembers5198.erase 3102=independentCachedBranchMembers5196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5196
  · have he : independentCachedBranchMembers5198.filter (independentCachedEdge 3102)=independentCachedBranchMembers5197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5197
def independentCachedBranchMembers5199 : Finset ℕ := ([1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788] : List ℕ).toFinset
theorem independentCachedBranchBound5199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5199 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5199 4 (fun x => (if x<2614 then (if x<1714 then (if x<1692 then (if x<1614 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<2702 then (if x<2668 then (if x<2652 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2772 then (if x<2762 then 2 else 3) else (if x<2788 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5200 : Finset ℕ := ([34,72,132,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5200 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5200 3072 4
  · have he : independentCachedBranchMembers5200.erase 3072=independentCachedBranchMembers5198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5198
  · have he : independentCachedBranchMembers5200.filter (independentCachedEdge 3072)=independentCachedBranchMembers5199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5199
def independentCachedBranchMembers5201 : Finset ℕ := ([34,238,1594,1708,1714,1768,2614,2668,2674,2788,3118,3178,3188,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5201 4 (fun x => (if x<2674 then (if x<1714 then (if x<1594 then (if x<238 then 0 else 0) else (if x<1708 then 1 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2668 then 2 else 2))) else (if x<3188 then (if x<3118 then (if x<2788 then 1 else 1) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5202 : Finset ℕ := ([34,72,132,222,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5202 222 4
  · have he : independentCachedBranchMembers5202.erase 222=independentCachedBranchMembers5200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5200
  · have he : independentCachedBranchMembers5202.filter (independentCachedEdge 222)=independentCachedBranchMembers5201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5201
def independentCachedBranchMembers5203 : Finset ℕ := ([72,132,1614,1692,1708,1714,2652,2668,2674,2702,3162,3178,3188,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5203 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5203 4 (fun x => (if x<2674 then (if x<1708 then (if x<1614 then (if x<132 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3188 then (if x<3162 then (if x<2702 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3222 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5204 : Finset ℕ := ([34,72,132,192,222,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5204 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5204 192 4
  · have he : independentCachedBranchMembers5204.erase 192=independentCachedBranchMembers5202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5202
  · have he : independentCachedBranchMembers5204.filter (independentCachedEdge 192)=independentCachedBranchMembers5203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5203
def independentCachedBranchMembers5205 : Finset ℕ := ([34,238,1614,1692,1734,1752,2652,2702,2762,2772,3118,3178,3188,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5205 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5205 4 (fun x => (if x<2762 then (if x<1734 then (if x<1614 then (if x<238 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1752 then 2 else 2) else (if x<2702 then 1 else 1))) else (if x<3188 then (if x<3118 then (if x<2772 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5206 : Finset ℕ := ([18,34,72,132,192,222,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5206 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5206 18 4
  · have he : independentCachedBranchMembers5206.erase 18=independentCachedBranchMembers5204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5204
  · have he : independentCachedBranchMembers5206.filter (independentCachedEdge 18)=independentCachedBranchMembers5205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5205
def independentCachedBranchMembers5207 : Finset ℕ := ([72,132,1594,1734,1752,1768,2614,2762,2772,2788,3162,3178,3188,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5207 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5207 4 (fun x => (if x<2772 then (if x<1752 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1734 then 1 else 2)) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2762 then 1 else 2))) else (if x<3188 then (if x<3162 then (if x<2788 then 1 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3222 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5208 : Finset ℕ := ([12,18,34,72,132,192,222,238,1594,1614,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2702,2762,2772,2788,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5208 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5208 12 4
  · have he : independentCachedBranchMembers5208.erase 12=independentCachedBranchMembers5206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5206
  · have he : independentCachedBranchMembers5208.filter (independentCachedEdge 12)=independentCachedBranchMembers5207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5207
def independentCachedBranchMembers5209 : Finset ℕ := ([12,18,34,40,66,72,132,144,192,222,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3072,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5209 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5209 1720 5
  · have he : independentCachedBranchMembers5209.erase 1720=independentCachedBranchMembers5189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5189
  · have he : independentCachedBranchMembers5209.filter (independentCachedEdge 1720)=independentCachedBranchMembers5208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5208
def independentCachedBranchMembers5210 : Finset ℕ := ([144,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3130,3150,3178,3188,3228,3238,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5210 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5210 5 (fun x => (if x<2674 then (if x<1714 then (if x<1626 then (if x<250 then 0 else (if x<1582 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 1 else 2))) else (if x<1762 then (if x<1734 then 0 else (if x<1752 then 2 else 0)) else (if x<2646 then (if x<2620 then 1 else 2) else (if x<2668 then 2 else 3)))) else (if x<3178 then (if x<2772 then (if x<2714 then 3 else (if x<2762 then 0 else 3)) else (if x<3130 then (if x<2800 then 3 else 0) else (if x<3150 then 4 else 4))) else (if x<3238 then (if x<3188 then 1 else (if x<3228 then 3 else 4)) else (if x<3282 then (if x<3256 then 1 else 0) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5211 : Finset ℕ := ([1582,1686,1714,1752,2668,2714,2772,2800,3130,3188,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5211 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5211 4 (fun x => (if x<2772 then (if x<1752 then (if x<1686 then 0 else (if x<1714 then 0 else 1)) else (if x<2668 then 1 else (if x<2714 then 0 else 1))) else (if x<3188 then (if x<2800 then 0 else (if x<3130 then 1 else 2)) else (if x<3238 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5212 : Finset ℕ := ([66,144,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3130,3150,3178,3188,3228,3238,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5212 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5212 66 4
  · have he : independentCachedBranchMembers5212.erase 66=independentCachedBranchMembers5210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5210
  · have he : independentCachedBranchMembers5212.filter (independentCachedEdge 66)=independentCachedBranchMembers5211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5211
def independentCachedBranchMembers5213 : Finset ℕ := ([1626,1714,1752,1762,2674,2714,2762,2800,3150,3188,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound5213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5213 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5213 4 (fun x => (if x<2762 then (if x<1762 then (if x<1714 then 0 else (if x<1752 then 0 else 1)) else (if x<2674 then 1 else (if x<2714 then 0 else 0))) else (if x<3188 then (if x<2800 then 1 else (if x<3150 then 1 else 2)) else (if x<3228 then 2 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5214 : Finset ℕ := ([40,66,144,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3130,3150,3178,3188,3228,3238,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5214 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5214 40 4
  · have he : independentCachedBranchMembers5214.erase 40=independentCachedBranchMembers5212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5212
  · have he : independentCachedBranchMembers5214.filter (independentCachedEdge 40)=independentCachedBranchMembers5213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5213
def independentCachedBranchMembers5215 : Finset ℕ := ([40,66,144,250,1582,1626,1686,1762,2620,2646,2714,2800,3130,3150,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5215 4 (fun x => (if x<2620 then (if x<1582 then (if x<144 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3130 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
