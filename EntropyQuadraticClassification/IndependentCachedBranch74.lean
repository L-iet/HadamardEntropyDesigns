/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch73
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5152 : Finset ℕ := ([40,66,144,250,1594,1614,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2714,2730,2740,2800,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5152 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5152 3102 4
  · have he : independentCachedBranchMembers5152.erase 3102=independentCachedBranchMembers5150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5150
  · have he : independentCachedBranchMembers5152.filter (independentCachedEdge 3102)=independentCachedBranchMembers5151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5151
def independentCachedBranchMembers5153 : Finset ℕ := ([1594,1614,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2714,2730,2740,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5153 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5153 4 (fun x => (if x<2620 then (if x<1714 then (if x<1692 then (if x<1614 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<2714 then (if x<2662 then (if x<2646 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<2740 then (if x<2730 then 2 else 3) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5154 : Finset ℕ := ([40,66,144,250,1594,1614,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2714,2730,2740,2800,3072,3102,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5154 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5154 3072 4
  · have he : independentCachedBranchMembers5154.erase 3072=independentCachedBranchMembers5152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5152
  · have he : independentCachedBranchMembers5154.filter (independentCachedEdge 3072)=independentCachedBranchMembers5153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5153
def independentCachedBranchMembers5155 : Finset ℕ := ([34,40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3072,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5155 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5155 1740 5
  · have he : independentCachedBranchMembers5155.erase 1740=independentCachedBranchMembers5143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5143
  · have he : independentCachedBranchMembers5155.filter (independentCachedEdge 1740)=independentCachedBranchMembers5154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5154
def independentCachedBranchMembers5156 : Finset ℕ := ([34,40,238,250,1582,1594,1642,1652,1708,1714,1762,1768,2614,2620,2662,2668,2674,2680,2730,2788,2800,3118,3130,3178,3188,3238,3256,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5156 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5156 5 (fun x => (if x<2662 then (if x<1652 then (if x<250 then (if x<40 then 0 else (if x<238 then 1 else 0)) else (if x<1594 then (if x<1582 then 1 else 0) else (if x<1642 then 1 else 2))) else (if x<1762 then (if x<1708 then 2 else (if x<1714 then 2 else 2)) else (if x<2614 then (if x<1768 then 0 else 1) else (if x<2620 then 3 else 4)))) else (if x<3118 then (if x<2680 then (if x<2668 then 0 else (if x<2674 then 2 else 2)) else (if x<2788 then (if x<2730 then 1 else 0) else (if x<2800 then 3 else 4))) else (if x<3238 then (if x<3178 then (if x<3130 then 4 else 3) else (if x<3188 then 0 else 3)) else (if x<3298 then (if x<3256 then 0 else 1) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5157 : Finset ℕ := ([40,238,1582,1642,1652,1708,1714,1768,2620,2662,2680,2788,3130,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5157 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5157 4 (fun x => (if x<2620 then (if x<1652 then (if x<1582 then (if x<238 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1714 then (if x<1708 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3130 then (if x<2680 then (if x<2662 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5158 : Finset ℕ := ([34,40,238,250,1582,1594,1642,1652,1708,1714,1762,1768,2614,2620,2662,2668,2674,2680,2730,2788,2800,3118,3130,3178,3188,3238,3250,3256,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5158 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5158 3250 4
  · have he : independentCachedBranchMembers5158.erase 3250=independentCachedBranchMembers5156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5156
  · have he : independentCachedBranchMembers5158.filter (independentCachedEdge 3250)=independentCachedBranchMembers5157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5157
def independentCachedBranchMembers5159 : Finset ℕ := ([34,250,1594,1642,1652,1708,1714,1762,2614,2662,2680,2800,3118,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5159 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5159 4 (fun x => (if x<2614 then (if x<1652 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1714 then (if x<1708 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3118 then (if x<2680 then (if x<2662 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3256 then (if x<3238 then 3 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5160 : Finset ℕ := ([34,40,238,250,1582,1594,1642,1652,1708,1714,1762,1768,2614,2620,2662,2668,2674,2680,2730,2788,2800,3118,3130,3178,3188,3238,3244,3250,3256,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5160 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5160 3244 4
  · have he : independentCachedBranchMembers5160.erase 3244=independentCachedBranchMembers5158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5158
  · have he : independentCachedBranchMembers5160.filter (independentCachedEdge 3244)=independentCachedBranchMembers5159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5159
def independentCachedBranchMembers5161 : Finset ℕ := ([34,40,238,250,1582,1594,1762,1768,2614,2620,2788,2800,3118,3130,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5161 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5161 4 (fun x => (if x<2614 then (if x<1582 then (if x<238 then (if x<40 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1762 then (if x<1594 then 0 else 1) else (if x<1768 then 0 else 1))) else (if x<3118 then (if x<2788 then (if x<2620 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3298 then (if x<3130 then 3 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5162 : Finset ℕ := ([34,40,238,250,1582,1594,1642,1652,1708,1714,1762,1768,2614,2620,2662,2668,2674,2680,2730,2740,2788,2800,3118,3130,3178,3188,3238,3244,3250,3256,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5162 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5162 2740 4
  · have he : independentCachedBranchMembers5162.erase 2740=independentCachedBranchMembers5160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5160
  · have he : independentCachedBranchMembers5162.filter (independentCachedEdge 2740)=independentCachedBranchMembers5161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5161
def independentCachedBranchMembers5163 : Finset ℕ := ([34,40,66,72,132,144,222,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3072,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5163 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5163 222 5
  · have he : independentCachedBranchMembers5163.erase 222=independentCachedBranchMembers5155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5155
  · have he : independentCachedBranchMembers5163.filter (independentCachedEdge 222)=independentCachedBranchMembers5162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5162
def independentCachedBranchMembers5164 : Finset ℕ := ([66,72,132,144,1614,1626,1642,1652,1686,1692,1708,1714,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5164 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5164 5 (fun x => (if x<2674 then (if x<1686 then (if x<1614 then (if x<132 then (if x<72 then 0 else 1) else (if x<144 then 0 else 1)) else (if x<1642 then (if x<1626 then 1 else 0) else (if x<1652 then 2 else 2))) else (if x<2646 then (if x<1708 then (if x<1692 then 1 else 0) else (if x<1714 then 2 else 2)) else (if x<2662 then (if x<2652 then 3 else 4) else (if x<2668 then 4 else 1)))) else (if x<3178 then (if x<2730 then (if x<2702 then (if x<2680 then 0 else 3) else (if x<2714 then 4 else 3)) else (if x<3150 then (if x<2740 then 2 else 0) else (if x<3162 then 4 else 3))) else (if x<3238 then (if x<3222 then (if x<3188 then 0 else 3) else (if x<3228 then 3 else 4)) else (if x<3250 then (if x<3244 then 4 else 0) else (if x<3256 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5165 : Finset ℕ := ([34,40,66,72,132,144,192,222,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3072,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5165 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5165 192 5
  · have he : independentCachedBranchMembers5165.erase 192=independentCachedBranchMembers5163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5163
  · have he : independentCachedBranchMembers5165.filter (independentCachedEdge 192)=independentCachedBranchMembers5164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5164
def independentCachedBranchMembers5166 : Finset ℕ := ([66,238,1582,1614,1642,1652,1692,1734,1752,1762,2620,2652,2662,2702,2730,2740,2762,2772,2800,3118,3150,3178,3188,3228,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5166 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5166 5 (fun x => (if x<2702 then (if x<1692 then (if x<1614 then (if x<238 then 0 else (if x<1582 then 0 else 1)) else (if x<1642 then 0 else (if x<1652 then 2 else 1))) else (if x<1762 then (if x<1734 then 1 else (if x<1752 then 1 else 2)) else (if x<2652 then (if x<2620 then 0 else 1) else (if x<2662 then 3 else 0)))) else (if x<3150 then (if x<2762 then (if x<2730 then 1 else (if x<2740 then 4 else 3)) else (if x<2800 then (if x<2772 then 0 else 1) else (if x<3118 then 4 else 2))) else (if x<3228 then (if x<3178 then 3 else (if x<3188 then 0 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5167 : Finset ℕ := ([238,1652,1734,1762,2620,2652,2702,2730,2762,3188,3238,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5167 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5167 4 (fun x => (if x<2702 then (if x<1762 then (if x<1652 then 0 else (if x<1734 then 1 else 0)) else (if x<2620 then 1 else (if x<2652 then 1 else 2))) else (if x<3188 then (if x<2730 then 0 else (if x<2762 then 1 else 2)) else (if x<3238 then 2 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5168 : Finset ℕ := ([66,144,238,1582,1614,1642,1652,1692,1734,1752,1762,2620,2652,2662,2702,2730,2740,2762,2772,2800,3118,3150,3178,3188,3228,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5168 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5168 144 4
  · have he : independentCachedBranchMembers5168.erase 144=independentCachedBranchMembers5166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5166
  · have he : independentCachedBranchMembers5168.filter (independentCachedEdge 144)=independentCachedBranchMembers5167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5167
def independentCachedBranchMembers5169 : Finset ℕ := ([66,1614,1652,1734,2620,2702,2740,2762,2800,3150,3188,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5169 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5169 4 (fun x => (if x<2740 then (if x<1734 then (if x<1614 then 0 else (if x<1652 then 0 else 1)) else (if x<2620 then 1 else (if x<2702 then 1 else 1))) else (if x<3150 then (if x<2762 then 0 else (if x<2800 then 2 else 2)) else (if x<3188 then 2 else (if x<3256 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5170 : Finset ℕ := ([34,66,144,238,1582,1614,1642,1652,1692,1734,1752,1762,2620,2652,2662,2702,2730,2740,2762,2772,2800,3118,3150,3178,3188,3228,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5170 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5170 34 4
  · have he : independentCachedBranchMembers5170.erase 34=independentCachedBranchMembers5168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5168
  · have he : independentCachedBranchMembers5170.filter (independentCachedEdge 34)=independentCachedBranchMembers5169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5169
def independentCachedBranchMembers5171 : Finset ℕ := ([66,238,1614,1642,1652,1734,1752,1762,2620,2702,2730,2740,3118,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5171 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5171 4 (fun x => (if x<2620 then (if x<1652 then (if x<1614 then (if x<238 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3118 then (if x<2730 then (if x<2702 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3238 then (if x<3228 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5172 : Finset ℕ := ([34,66,144,238,1582,1614,1642,1652,1692,1734,1752,1762,2620,2652,2662,2702,2730,2740,2762,2772,2800,3118,3150,3178,3188,3228,3238,3256,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5172 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5172 3288 4
  · have he : independentCachedBranchMembers5172.erase 3288=independentCachedBranchMembers5170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5170
  · have he : independentCachedBranchMembers5172.filter (independentCachedEdge 3288)=independentCachedBranchMembers5171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5171
def independentCachedBranchMembers5173 : Finset ℕ := ([34,144,1582,1642,1652,1692,1734,1752,2652,2730,2740,2800,3150,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5173 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5173 4 (fun x => (if x<2652 then (if x<1652 then (if x<1582 then (if x<144 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1734 then (if x<1692 then 1 else 0) else (if x<1752 then 1 else 1))) else (if x<3150 then (if x<2740 then (if x<2730 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3256 then (if x<3238 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5174 : Finset ℕ := ([34,66,144,238,1582,1614,1642,1652,1692,1734,1752,1762,2620,2652,2662,2702,2730,2740,2762,2772,2800,3118,3150,3178,3188,3228,3238,3256,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5174 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5174 3270 4
  · have he : independentCachedBranchMembers5174.erase 3270=independentCachedBranchMembers5172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5172
  · have he : independentCachedBranchMembers5174.filter (independentCachedEdge 3270)=independentCachedBranchMembers5173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5173
def independentCachedBranchMembers5175 : Finset ℕ := ([34,66,144,238,1582,1614,1692,1762,2620,2652,2702,2800,3118,3150,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5175 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5175 4 (fun x => (if x<2620 then (if x<1582 then (if x<144 then (if x<66 then 0 else 1) else (if x<238 then 0 else 1)) else (if x<1692 then (if x<1614 then 0 else 1) else (if x<1762 then 0 else 1))) else (if x<3118 then (if x<2702 then (if x<2652 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3228 then (if x<3150 then 2 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5176 : Finset ℕ := ([34,66,144,238,1582,1614,1642,1652,1692,1734,1752,1762,2620,2652,2662,2680,2702,2730,2740,2762,2772,2800,3118,3150,3178,3188,3228,3238,3256,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5176 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5176 2680 4
  · have he : independentCachedBranchMembers5176.erase 2680=independentCachedBranchMembers5174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5174
  · have he : independentCachedBranchMembers5176.filter (independentCachedEdge 2680)=independentCachedBranchMembers5175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5175
def independentCachedBranchMembers5177 : Finset ℕ := ([18,34,40,66,72,132,144,192,222,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3072,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5177 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5177 18 5
  · have he : independentCachedBranchMembers5177.erase 18=independentCachedBranchMembers5165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5165
  · have he : independentCachedBranchMembers5177.filter (independentCachedEdge 18)=independentCachedBranchMembers5176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5176
def independentCachedBranchMembers5178 : Finset ℕ := ([72,250,1594,1626,1642,1652,1686,1734,1752,1768,2614,2646,2680,2714,2730,2740,2762,2772,2788,3130,3162,3178,3188,3222,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5178 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5178 5 (fun x => (if x<2714 then (if x<1686 then (if x<1626 then (if x<250 then 0 else (if x<1594 then 0 else 1)) else (if x<1642 then 0 else (if x<1652 then 2 else 1))) else (if x<1768 then (if x<1734 then 1 else (if x<1752 then 2 else 1)) else (if x<2646 then (if x<2614 then 0 else 1) else (if x<2680 then 3 else 0)))) else (if x<3162 then (if x<2762 then (if x<2730 then 1 else (if x<2740 then 4 else 3)) else (if x<2788 then (if x<2772 then 0 else 1) else (if x<3130 then 4 else 2))) else (if x<3222 then (if x<3178 then 3 else (if x<3188 then 0 else 3)) else (if x<3256 then (if x<3238 then 2 else 4) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5179 : Finset ℕ := ([250,1652,1752,1768,2614,2646,2714,2730,2762,3188,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5179 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5179 4 (fun x => (if x<2714 then (if x<1768 then (if x<1652 then 0 else (if x<1752 then 1 else 0)) else (if x<2614 then 1 else (if x<2646 then 1 else 2))) else (if x<3188 then (if x<2730 then 0 else (if x<2762 then 1 else 2)) else (if x<3256 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5180 : Finset ℕ := ([72,132,250,1594,1626,1642,1652,1686,1734,1752,1768,2614,2646,2680,2714,2730,2740,2762,2772,2788,3130,3162,3178,3188,3222,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5180 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5180 132 4
  · have he : independentCachedBranchMembers5180.erase 132=independentCachedBranchMembers5178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5178
  · have he : independentCachedBranchMembers5180.filter (independentCachedEdge 132)=independentCachedBranchMembers5179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5179
def independentCachedBranchMembers5181 : Finset ℕ := ([72,1626,1652,1752,2614,2714,2740,2762,2788,3162,3188,3238] : List ℕ).toFinset
theorem independentCachedBranchBound5181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5181 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5181 4 (fun x => (if x<2740 then (if x<1752 then (if x<1626 then 0 else (if x<1652 then 0 else 1)) else (if x<2614 then 1 else (if x<2714 then 1 else 1))) else (if x<3162 then (if x<2762 then 0 else (if x<2788 then 2 else 2)) else (if x<3188 then 2 else (if x<3238 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5182 : Finset ℕ := ([40,72,132,250,1594,1626,1642,1652,1686,1734,1752,1768,2614,2646,2680,2714,2730,2740,2762,2772,2788,3130,3162,3178,3188,3222,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5182 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5182 40 4
  · have he : independentCachedBranchMembers5182.erase 40=independentCachedBranchMembers5180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5180
  · have he : independentCachedBranchMembers5182.filter (independentCachedEdge 40)=independentCachedBranchMembers5181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5181
def independentCachedBranchMembers5183 : Finset ℕ := ([40,132,1594,1642,1652,1686,1734,1752,2646,2730,2740,2788,3162,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5183 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5183 4 (fun x => (if x<2646 then (if x<1652 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1734 then (if x<1686 then 1 else 0) else (if x<1752 then 1 else 1))) else (if x<3162 then (if x<2740 then (if x<2730 then 2 else 3) else (if x<2788 then 2 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
