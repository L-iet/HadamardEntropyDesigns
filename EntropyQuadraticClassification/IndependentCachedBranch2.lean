/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch1
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers256 : Finset ℕ := ([1590,1642,1678,1746,2620,2638,2674,2710,2730,2762,2776,2788,3130,3188,3244,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers256 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers256 5 (fun x => (if x<2730 then (if x<2620 then (if x<1678 then (if x<1642 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2674 then (if x<2638 then 1 else 1) else (if x<2710 then 0 else 0))) else (if x<3130 then (if x<2776 then (if x<2762 then 1 else 0) else (if x<2788 then 1 else 1)) else (if x<3244 then (if x<3188 then 2 else 2) else (if x<3276 then 2 else (if x<3298 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers257 : Finset ℕ := ([1590,1628,1642,1678,1686,1720,1746,1764,2620,2638,2674,2680,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers257 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers257 1686 5
  · have he : independentCachedBranchMembers257.erase 1686=independentCachedBranchMembers255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound255
  · have he : independentCachedBranchMembers257.filter (independentCachedEdge 1686)=independentCachedBranchMembers256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound256
def independentCachedBranchMembers258 : Finset ℕ := ([1590,1628,1720,1746,2620,2638,2674,2710,2730,2738,2776,2788,3226,3238,3276,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers258 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers258 5 (fun x => (if x<2730 then (if x<2620 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2674 then (if x<2638 then 0 else 1) else (if x<2710 then 1 else 1))) else (if x<3226 then (if x<2776 then (if x<2738 then 1 else 0) else (if x<2788 then 0 else 1)) else (if x<3276 then (if x<3238 then 2 else 2) else (if x<3284 then 2 else (if x<3304 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers259 : Finset ℕ := ([1590,1596,1628,1642,1678,1686,1720,1746,1764,2620,2638,2674,2680,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers259 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers259 1596 5
  · have he : independentCachedBranchMembers259.erase 1596=independentCachedBranchMembers257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound257
  · have he : independentCachedBranchMembers259.filter (independentCachedEdge 1596)=independentCachedBranchMembers258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound258
def independentCachedBranchMembers260 : Finset ℕ := ([1596,1678,1720,1746,1764,2620,2674,2716,2730,2788,3102,3130,3188,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers260 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers260 5 (fun x => (if x<2788 then (if x<1764 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2674 then (if x<2620 then 0 else 1) else (if x<2716 then 2 else (if x<2730 then 3 else 2)))) else (if x<3226 then (if x<3130 then (if x<3102 then 2 else 0) else (if x<3188 then 2 else 0)) else (if x<3270 then (if x<3244 then 3 else 0) else (if x<3284 then 0 else (if x<3298 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers261 : Finset ℕ := ([72,1590,1596,1628,1642,1678,1686,1720,1746,1764,2620,2638,2674,2680,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers261 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers261 72 5
  · have he : independentCachedBranchMembers261.erase 72=independentCachedBranchMembers259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound259
  · have he : independentCachedBranchMembers261.filter (independentCachedEdge 72)=independentCachedBranchMembers260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound260
def independentCachedBranchMembers262 : Finset ℕ := ([1628,1642,1686,1746,1764,2710,2716,2730,2776,2788,3102,3180,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers262 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers262 5 (fun x => (if x<2788 then (if x<1764 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1746 then 1 else 0)) else (if x<2716 then (if x<2710 then 0 else 2) else (if x<2730 then 1 else (if x<2776 then 2 else 2)))) else (if x<3238 then (if x<3180 then (if x<3102 then 2 else 1) else (if x<3226 then 0 else 2)) else (if x<3284 then (if x<3244 then 2 else 3) else (if x<3298 then 0 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers263 : Finset ℕ := ([48,72,1590,1596,1628,1642,1678,1686,1720,1746,1764,2620,2638,2674,2680,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers263 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers263 48 5
  · have he : independentCachedBranchMembers263.erase 48=independentCachedBranchMembers261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound261
  · have he : independentCachedBranchMembers263.filter (independentCachedEdge 48)=independentCachedBranchMembers262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound262
def independentCachedBranchMembers264 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2620,2674,2710,2738,2762,2776,3180,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers264 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers264 5 (fun x => (if x<2710 then (if x<1720 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 0 else 0)) else (if x<1764 then (if x<1746 then 0 else 0) else (if x<2620 then 0 else (if x<2674 then 1 else 1)))) else (if x<3226 then (if x<2762 then (if x<2738 then 1 else 2) else (if x<2776 then 2 else (if x<3180 then 1 else 3))) else (if x<3270 then (if x<3244 then 2 else 4) else (if x<3284 then 3 else (if x<3298 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers265 : Finset ℕ := ([48,72,1590,1596,1628,1642,1678,1686,1720,1746,1764,2614,2620,2638,2674,2680,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers265 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers265 2614 5
  · have he : independentCachedBranchMembers265.erase 2614=independentCachedBranchMembers263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound263
  · have he : independentCachedBranchMembers265.filter (independentCachedEdge 2614)=independentCachedBranchMembers264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound264
def independentCachedBranchMembers266 : Finset ℕ := ([1590,1596,1628,1642,1678,1720,1746,1764,2638,2674,2680,2710,2716,2730,2762,3130,3180,3252,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers266 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers266 5 (fun x => (if x<2680 then (if x<1720 then (if x<1628 then (if x<1596 then 0 else 1) else (if x<1642 then 0 else (if x<1678 then 0 else 0))) else (if x<1764 then (if x<1746 then 0 else 0) else (if x<2638 then 0 else (if x<2674 then 2 else 2)))) else (if x<3130 then (if x<2716 then (if x<2710 then 1 else 2) else (if x<2730 then 1 else (if x<2762 then 2 else 1))) else (if x<3284 then (if x<3180 then 3 else (if x<3252 then 3 else 3)) else (if x<3298 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers267 : Finset ℕ := ([1596,1678,1720,1746,1764,2674,2716,2730,3130,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers267 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers267 4 (fun x => (if x<2674 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<1746 then 1 else (if x<1764 then 1 else 0))) else (if x<3130 then (if x<2716 then 2 else (if x<2730 then 3 else 2)) else (if x<3284 then 2 else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers268 : Finset ℕ := ([72,1590,1596,1628,1642,1678,1720,1746,1764,2638,2674,2680,2710,2716,2730,2762,3130,3180,3252,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers268 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers268 72 4
  · have he : independentCachedBranchMembers268.erase 72=independentCachedBranchMembers266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound266
  · have he : independentCachedBranchMembers268.filter (independentCachedEdge 72)=independentCachedBranchMembers267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound267
def independentCachedBranchMembers269 : Finset ℕ := ([48,72,1590,1596,1628,1642,1678,1686,1720,1746,1764,2614,2620,2638,2674,2680,2702,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers269 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers269 2702 5
  · have he : independentCachedBranchMembers269.erase 2702=independentCachedBranchMembers265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound265
  · have he : independentCachedBranchMembers269.filter (independentCachedEdge 2702)=independentCachedBranchMembers268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound268
def independentCachedBranchMembers270 : Finset ℕ := ([1590,1628,1642,1678,1686,1720,1746,1764,2620,2638,2680,2716,2730,2738,2776,3130,3226,3244,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers270 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers270 5 (fun x => (if x<2680 then (if x<1720 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 0 else (if x<1686 then 0 else 1))) else (if x<1764 then (if x<1746 then 0 else 0) else (if x<2620 then 0 else (if x<2638 then 2 else 2)))) else (if x<3130 then (if x<2730 then (if x<2716 then 1 else 1) else (if x<2738 then 2 else (if x<2776 then 1 else 2))) else (if x<3252 then (if x<3226 then 3 else (if x<3244 then 4 else 3)) else (if x<3270 then 4 else (if x<3304 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers271 : Finset ℕ := ([1628,1642,1686,1746,1764,2716,2730,2776,3226,3244,3304] : List ℕ).toFinset
theorem independentCachedBranchBound271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers271 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers271 4 (fun x => (if x<2716 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1746 then 1 else (if x<1764 then 0 else 0))) else (if x<3226 then (if x<2730 then 1 else (if x<2776 then 2 else 2)) else (if x<3244 then 1 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers272 : Finset ℕ := ([48,1590,1628,1642,1678,1686,1720,1746,1764,2620,2638,2680,2716,2730,2738,2776,3130,3226,3244,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers272 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers272 48 4
  · have he : independentCachedBranchMembers272.erase 48=independentCachedBranchMembers270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound270
  · have he : independentCachedBranchMembers272.filter (independentCachedEdge 48)=independentCachedBranchMembers271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound271
def independentCachedBranchMembers273 : Finset ℕ := ([48,72,1590,1596,1628,1642,1678,1686,1720,1746,1764,2614,2620,2638,2652,2674,2680,2702,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers273 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers273 2652 5
  · have he : independentCachedBranchMembers273.erase 2652=independentCachedBranchMembers269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound269
  · have he : independentCachedBranchMembers273.filter (independentCachedEdge 2652)=independentCachedBranchMembers272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound272
def independentCachedBranchMembers274 : Finset ℕ := ([48,72,1596,1628,1642,1678,1686,1720,2614,2638,2680,2716,2730,2738,2762,2788,3130,3180,3188,3238,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers274 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers274 5 (fun x => (if x<2716 then (if x<1678 then (if x<1596 then (if x<72 then 0 else 0) else (if x<1628 then 1 else (if x<1642 then 2 else 1))) else (if x<2614 then (if x<1686 then 1 else (if x<1720 then 2 else 2)) else (if x<2638 then 0 else (if x<2680 then 0 else 0)))) else (if x<3130 then (if x<2738 then (if x<2730 then 1 else 3) else (if x<2762 then 2 else (if x<2788 then 1 else 3))) else (if x<3238 then (if x<3180 then 3 else (if x<3188 then 4 else 3)) else (if x<3270 then 3 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers275 : Finset ℕ := ([48,72,1590,1596,1628,1642,1678,1686,1692,1720,1746,1764,2614,2620,2638,2652,2674,2680,2702,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers275 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers275 1692 5
  · have he : independentCachedBranchMembers275.erase 1692=independentCachedBranchMembers273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound273
  · have he : independentCachedBranchMembers275.filter (independentCachedEdge 1692)=independentCachedBranchMembers274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound274
def independentCachedBranchMembers276 : Finset ℕ := ([1628,1642,1678,1720,2614,2620,2638,2674,2680,2710,2716,2730,2776,2788,3130,3188,3226,3238,3244,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers276 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers276 5 (fun x => (if x<2730 then (if x<2620 then (if x<1678 then (if x<1642 then 0 else 0) else (if x<1720 then 0 else (if x<2614 then 0 else 1))) else (if x<2680 then (if x<2638 then 2 else (if x<2674 then 0 else 2)) else (if x<2710 then 0 else (if x<2716 then 2 else 0)))) else (if x<3226 then (if x<2788 then (if x<2776 then 0 else 2) else (if x<3130 then 1 else (if x<3188 then 1 else 1))) else (if x<3284 then (if x<3238 then 3 else (if x<3244 then 1 else 3)) else (if x<3298 then 3 else (if x<3304 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers277 : Finset ℕ := ([48,72,1590,1596,1614,1628,1642,1678,1686,1692,1720,1746,1764,2614,2620,2638,2652,2674,2680,2702,2710,2716,2730,2738,2762,2776,2788,3102,3130,3180,3188,3226,3238,3244,3252,3270,3276,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers277 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers277 1614 5
  · have he : independentCachedBranchMembers277.erase 1614=independentCachedBranchMembers275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound275
  · have he : independentCachedBranchMembers277.filter (independentCachedEdge 1614)=independentCachedBranchMembers276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound276
def independentCachedBranchMembers278 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2788,2792,2800,3102,3118,3130,3158,3164,3178,3180,3186,3188,3192,3214,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers278 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers278 3300 6
  · have he : independentCachedBranchMembers278.erase 3300=independentCachedBranchMembers246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound246
  · have he : independentCachedBranchMembers278.filter (independentCachedEdge 3300)=independentCachedBranchMembers277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound277
def independentCachedBranchMembers279 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2650,2680,2716,2730,2738,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers279 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers279 6 (fun x => (if x<2788 then (if x<1768 then (if x<1692 then (if x<1614 then 0 else (if x<1652 then 0 else 0)) else (if x<1702 then 0 else (if x<1746 then 0 else 0))) else (if x<2716 then (if x<2650 then 0 else (if x<2680 then 1 else 2)) else (if x<2738 then (if x<2730 then 1 else 1) else (if x<2762 then 2 else 2)))) else (if x<3226 then (if x<3164 then (if x<2800 then 2 else (if x<3102 then 1 else 3)) else (if x<3186 then (if x<3178 then 4 else 3) else (if x<3214 then 4 else 5))) else (if x<3256 then (if x<3244 then 4 else (if x<3252 then 3 else 4)) else (if x<3288 then (if x<3284 then 5 else 5) else (if x<3298 then 3 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers280 : Finset ℕ := ([1652,1702,1746,2650,2680,2730,2800,3164,3186,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers280 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers280 5 (fun x => (if x<2800 then (if x<2650 then (if x<1702 then 0 else (if x<1746 then 0 else 0)) else (if x<2680 then 1 else (if x<2730 then 2 else 1))) else (if x<3214 then (if x<3164 then 1 else (if x<3186 then 2 else 2)) else (if x<3284 then (if x<3244 then 3 else 4) else (if x<3288 then 3 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers281 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2650,2680,2716,2730,2738,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers281 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers281 3276 5
  · have he : independentCachedBranchMembers281.erase 3276=independentCachedBranchMembers279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound279
  · have he : independentCachedBranchMembers281.filter (independentCachedEdge 3276)=independentCachedBranchMembers280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound280
def independentCachedBranchMembers282 : Finset ℕ := ([1614,1692,1746,2738,2762,3164,3178,3214,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers282 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers282 5 (fun x => (if x<3178 then (if x<2738 then (if x<1692 then 0 else (if x<1746 then 0 else 0)) else (if x<2762 then 1 else (if x<3164 then 1 else 2))) else (if x<3244 then (if x<3214 then 2 else (if x<3226 then 2 else 1)) else (if x<3284 then (if x<3256 then 3 else 2) else (if x<3298 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers283 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2614,2650,2680,2716,2730,2738,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers283 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers283 2614 5
  · have he : independentCachedBranchMembers283.erase 2614=independentCachedBranchMembers281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound281
  · have he : independentCachedBranchMembers283.filter (independentCachedEdge 2614)=independentCachedBranchMembers282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound282
def independentCachedBranchMembers284 : Finset ℕ := ([1652,1692,1768,2680,2762,2788,3102,3164,3178,3186,3226,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers284 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers284 5 (fun x => (if x<3164 then (if x<2680 then (if x<1692 then 0 else (if x<1768 then 0 else 0)) else (if x<2788 then (if x<2762 then 1 else 1) else (if x<3102 then 1 else 2))) else (if x<3226 then (if x<3178 then 3 else (if x<3186 then 2 else 3)) else (if x<3252 then (if x<3244 then 3 else 2) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers285 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2614,2650,2680,2716,2730,2738,2758,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers285 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers285 2758 5
  · have he : independentCachedBranchMembers285.erase 2758=independentCachedBranchMembers283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound283
  · have he : independentCachedBranchMembers285.filter (independentCachedEdge 2758)=independentCachedBranchMembers284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound284
def independentCachedBranchMembers286 : Finset ℕ := ([1594,1692,1702,2680,2738,2788,3102,3186,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers286 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers286 5 (fun x => (if x<3186 then (if x<2680 then (if x<1692 then 0 else (if x<1702 then 0 else 0)) else (if x<2788 then (if x<2738 then 1 else 1) else (if x<3102 then 1 else 2))) else (if x<3256 then (if x<3214 then 2 else (if x<3252 then 3 else 2)) else (if x<3288 then (if x<3284 then 3 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers287 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2614,2650,2668,2680,2716,2730,2738,2758,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers287 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers287 2668 5
  · have he : independentCachedBranchMembers287.erase 2668=independentCachedBranchMembers285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound285
  · have he : independentCachedBranchMembers287.filter (independentCachedEdge 2668)=independentCachedBranchMembers286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound286
def independentCachedBranchMembers288 : Finset ℕ := ([1614,1652,1746,1768,2614,2650,2668,2716,2730,2758,2762,2800,3164,3178,3226,3244,3276] : List ℕ).toFinset
theorem independentCachedBranchBound288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers288 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers288 5 (fun x => (if x<2730 then (if x<2614 then (if x<1746 then (if x<1652 then 0 else 0) else (if x<1768 then 0 else 0)) else (if x<2668 then (if x<2650 then 1 else 1) else (if x<2716 then 0 else 1))) else (if x<3164 then (if x<2762 then (if x<2758 then 1 else 1) else (if x<2800 then 0 else 0)) else (if x<3226 then (if x<3178 then 2 else 2) else (if x<3244 then 2 else (if x<3276 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers289 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,1776,2614,2650,2668,2680,2716,2730,2738,2758,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers289 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers289 1776 5
  · have he : independentCachedBranchMembers289.erase 1776=independentCachedBranchMembers287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound287
  · have he : independentCachedBranchMembers289.filter (independentCachedEdge 1776)=independentCachedBranchMembers288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound288
def independentCachedBranchMembers290 : Finset ℕ := ([1594,1614,1702,1746,2614,2650,2668,2716,2730,2738,2758,2800,3214,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers290 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers290 5 (fun x => (if x<2730 then (if x<2614 then (if x<1702 then (if x<1614 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2668 then (if x<2650 then 1 else 0) else (if x<2716 then 1 else 1))) else (if x<3214 then (if x<2758 then (if x<2738 then 1 else 0) else (if x<2800 then 0 else 1)) else (if x<3276 then (if x<3256 then 2 else 2) else (if x<3284 then 3 else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers291 : Finset ℕ := ([1594,1614,1626,1652,1692,1702,1746,1768,1776,2614,2650,2668,2680,2716,2730,2738,2758,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers291 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers291 1626 5
  · have he : independentCachedBranchMembers291.erase 1626=independentCachedBranchMembers289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound289
  · have he : independentCachedBranchMembers291.filter (independentCachedEdge 1626)=independentCachedBranchMembers290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound290
def independentCachedBranchMembers292 : Finset ℕ := ([1594,1652,1692,1746,1776,2716,2730,2758,2788,2800,3102,3186,3214,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers292 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers292 5 (fun x => (if x<2800 then (if x<1776 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2730 then (if x<2716 then 1 else 2) else (if x<2758 then 2 else (if x<2788 then 2 else 1)))) else (if x<3226 then (if x<3186 then (if x<3102 then 2 else 1) else (if x<3214 then 0 else 2)) else (if x<3256 then (if x<3244 then 0 else 3) else (if x<3284 then 2 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers293 : Finset ℕ := ([72,1594,1614,1626,1652,1692,1702,1746,1768,1776,2614,2650,2668,2680,2716,2730,2738,2758,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers293 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers293 72 5
  · have he : independentCachedBranchMembers293.erase 72=independentCachedBranchMembers291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound291
  · have he : independentCachedBranchMembers293.filter (independentCachedEdge 72)=independentCachedBranchMembers292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound292
def independentCachedBranchMembers294 : Finset ℕ := ([1626,1692,1702,1746,1768,2650,2668,2716,2730,2788,3102,3164,3178,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers294 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers294 5 (fun x => (if x<2788 then (if x<1768 then (if x<1702 then (if x<1692 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2668 then (if x<2650 then 0 else 1) else (if x<2716 then 2 else (if x<2730 then 2 else 2)))) else (if x<3226 then (if x<3164 then (if x<3102 then 3 else 0) else (if x<3178 then 2 else 0)) else (if x<3284 then (if x<3244 then 2 else 0) else (if x<3288 then 3 else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers295 : Finset ℕ := ([48,72,1594,1614,1626,1652,1692,1702,1746,1768,1776,2614,2650,2668,2680,2716,2730,2738,2758,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers295 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers295 48 5
  · have he : independentCachedBranchMembers295.erase 48=independentCachedBranchMembers293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound293
  · have he : independentCachedBranchMembers295.filter (independentCachedEdge 48)=independentCachedBranchMembers294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound294
def independentCachedBranchMembers296 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2650,2668,2738,2758,2762,2800,3186,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers296 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers296 5 (fun x => (if x<2738 then (if x<1702 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1692 then 0 else 0)) else (if x<1768 then (if x<1746 then 0 else 0) else (if x<2650 then 0 else (if x<2668 then 1 else 1)))) else (if x<3226 then (if x<2762 then (if x<2758 then 2 else 1) else (if x<2800 then 2 else (if x<3186 then 1 else 3))) else (if x<3284 then (if x<3244 then 2 else 4) else (if x<3288 then 3 else (if x<3298 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers297 : Finset ℕ := ([48,72,1594,1614,1626,1652,1692,1702,1746,1768,1776,2614,2638,2650,2668,2680,2716,2730,2738,2758,2762,2788,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers297 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers297 2638 5
  · have he : independentCachedBranchMembers297.erase 2638=independentCachedBranchMembers295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound295
  · have he : independentCachedBranchMembers297.filter (independentCachedEdge 2638)=independentCachedBranchMembers296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound296
def independentCachedBranchMembers298 : Finset ℕ := ([1594,1614,1626,1652,1692,1702,1746,1768,2614,2668,2680,2730,2762,2788,2800,3164,3186,3214,3226,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers298 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers298 5 (fun x => (if x<2680 then (if x<1702 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else (if x<1692 then 0 else 0))) else (if x<1768 then (if x<1746 then 0 else 0) else (if x<2614 then 0 else (if x<2668 then 2 else 2)))) else (if x<3164 then (if x<2762 then (if x<2730 then 1 else 2) else (if x<2788 then 1 else (if x<2800 then 1 else 2))) else (if x<3226 then (if x<3186 then 3 else (if x<3214 then 3 else 4)) else (if x<3252 then 3 else (if x<3284 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers299 : Finset ℕ := ([1626,1692,1702,1746,1768,2668,2730,2788,3164,3226,3284] : List ℕ).toFinset
theorem independentCachedBranchBound299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers299 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers299 4 (fun x => (if x<2668 then (if x<1702 then (if x<1692 then 0 else 0) else (if x<1746 then 1 else (if x<1768 then 1 else 0))) else (if x<3164 then (if x<2730 then 2 else (if x<2788 then 2 else 3)) else (if x<3226 then 2 else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers300 : Finset ℕ := ([48,1594,1614,1626,1652,1692,1702,1746,1768,2614,2668,2680,2730,2762,2788,2800,3164,3186,3214,3226,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers300 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers300 48 4
  · have he : independentCachedBranchMembers300.erase 48=independentCachedBranchMembers298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound298
  · have he : independentCachedBranchMembers300.filter (independentCachedEdge 48)=independentCachedBranchMembers299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound299
def independentCachedBranchMembers301 : Finset ℕ := ([48,72,1594,1614,1626,1652,1692,1702,1746,1768,1776,2614,2638,2650,2668,2680,2716,2730,2738,2758,2762,2788,2792,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers301 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers301 2792 5
  · have he : independentCachedBranchMembers301.erase 2792=independentCachedBranchMembers297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound297
  · have he : independentCachedBranchMembers301.filter (independentCachedEdge 2792)=independentCachedBranchMembers300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound300
def independentCachedBranchMembers302 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,1776,2614,2650,2680,2730,2738,2758,2788,3164,3214,3244,3252,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers302 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers302 5 (fun x => (if x<2680 then (if x<1746 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1692 then 0 else (if x<1702 then 0 else 0))) else (if x<1776 then (if x<1768 then 0 else 0) else (if x<2614 then 1 else (if x<2650 then 2 else 2)))) else (if x<3164 then (if x<2738 then (if x<2730 then 1 else 2) else (if x<2758 then 1 else (if x<2788 then 2 else 1))) else (if x<3252 then (if x<3214 then 3 else (if x<3244 then 3 else 4)) else (if x<3288 then 3 else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers303 : Finset ℕ := ([1594,1652,1692,1746,1776,2730,2758,2788,3214,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers303 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers303 4 (fun x => (if x<2730 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1746 then 0 else (if x<1776 then 0 else 1))) else (if x<3214 then (if x<2758 then 2 else (if x<2788 then 2 else 1)) else (if x<3244 then 2 else (if x<3298 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers304 : Finset ℕ := ([72,1594,1614,1652,1692,1702,1746,1768,1776,2614,2650,2680,2730,2738,2758,2788,3164,3214,3244,3252,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers304 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers304 72 4
  · have he : independentCachedBranchMembers304.erase 72=independentCachedBranchMembers302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound302
  · have he : independentCachedBranchMembers304.filter (independentCachedEdge 72)=independentCachedBranchMembers303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound303
def independentCachedBranchMembers305 : Finset ℕ := ([48,72,1594,1614,1626,1652,1692,1702,1746,1768,1776,2614,2618,2638,2650,2668,2680,2716,2730,2738,2758,2762,2788,2792,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers305 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers305 2618 5
  · have he : independentCachedBranchMembers305.erase 2618=independentCachedBranchMembers301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound301
  · have he : independentCachedBranchMembers305.filter (independentCachedEdge 2618)=independentCachedBranchMembers304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound304
def independentCachedBranchMembers306 : Finset ℕ := ([48,72,1594,1626,1652,1702,1768,1776,2614,2638,2680,2716,2730,2738,2762,2788,3164,3178,3186,3214,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers306 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers306 5 (fun x => (if x<2716 then (if x<1702 then (if x<1594 then (if x<72 then 0 else 0) else (if x<1626 then 1 else (if x<1652 then 2 else 1))) else (if x<2614 then (if x<1768 then 1 else (if x<1776 then 1 else 2)) else (if x<2638 then 0 else (if x<2680 then 0 else 0)))) else (if x<3164 then (if x<2738 then (if x<2730 then 3 else 1) else (if x<2762 then 3 else (if x<2788 then 3 else 1))) else (if x<3214 then (if x<3178 then 4 else (if x<3186 then 4 else 2)) else (if x<3256 then 4 else (if x<3288 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers307 : Finset ℕ := ([48,72,1594,1614,1626,1652,1692,1702,1746,1764,1768,1776,2614,2618,2638,2650,2668,2680,2716,2730,2738,2758,2762,2788,2792,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers307 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers307 1764 5
  · have he : independentCachedBranchMembers307.erase 1764=independentCachedBranchMembers305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound305
  · have he : independentCachedBranchMembers307.filter (independentCachedEdge 1764)=independentCachedBranchMembers306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound306
def independentCachedBranchMembers308 : Finset ℕ := ([1594,1652,1702,1768,2614,2638,2650,2668,2680,2716,2730,2758,2788,2800,3164,3178,3214,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers308 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers308 5 (fun x => (if x<2758 then (if x<2638 then (if x<1702 then (if x<1652 then 0 else 0) else (if x<1768 then 0 else (if x<2614 then 0 else 0))) else (if x<2680 then (if x<2650 then 1 else (if x<2668 then 2 else 2)) else (if x<2716 then 0 else (if x<2730 then 1 else 0)))) else (if x<3214 then (if x<2800 then (if x<2788 then 2 else 0) else (if x<3164 then 2 else (if x<3178 then 1 else 1))) else (if x<3256 then (if x<3226 then 1 else (if x<3244 then 3 else 3)) else (if x<3284 then 1 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers309 : Finset ℕ := ([48,72,1590,1594,1614,1626,1652,1692,1702,1746,1764,1768,1776,2614,2618,2638,2650,2668,2680,2716,2730,2738,2758,2762,2788,2792,2800,3102,3164,3178,3186,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers309 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers309 1590 5
  · have he : independentCachedBranchMembers309.erase 1590=independentCachedBranchMembers307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound307
  · have he : independentCachedBranchMembers309.filter (independentCachedEdge 1590)=independentCachedBranchMembers308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound308
def independentCachedBranchMembers310 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2788,2792,2800,3102,3118,3130,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers310 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers310 3228 6
  · have he : independentCachedBranchMembers310.erase 3228=independentCachedBranchMembers278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound278
  · have he : independentCachedBranchMembers310.filter (independentCachedEdge 3228)=independentCachedBranchMembers309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound309
def independentCachedBranchMembers311 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2614,2620,2638,2680,2710,2730,2732,2772,2788,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers311 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers311 6 (fun x => (if x<2772 then (if x<2614 then (if x<1692 then (if x<1614 then 0 else (if x<1652 then 0 else 0)) else (if x<1746 then (if x<1702 then 0 else 0) else (if x<1768 then 0 else 0))) else (if x<2680 then (if x<2620 then 1 else (if x<2638 then 2 else 1)) else (if x<2730 then (if x<2710 then 1 else 2) else (if x<2732 then 1 else 3)))) else (if x<3180 then (if x<3118 then (if x<2788 then 3 else (if x<3102 then 1 else 2)) else (if x<3164 then (if x<3158 then 3 else 3) else (if x<3178 then 4 else 4))) else (if x<3256 then (if x<3250 then (if x<3214 then 2 else 4) else (if x<3252 then 5 else 2)) else (if x<3274 then (if x<3270 then 4 else 2) else (if x<3276 then 5 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers312 : Finset ℕ := ([1594,1614,1652,2614,2680,2772,3102,3158,3178,3180,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers312 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers312 5 (fun x => (if x<3158 then (if x<2614 then (if x<1614 then 0 else (if x<1652 then 0 else 0)) else (if x<2772 then (if x<2680 then 1 else 1) else (if x<3102 then 1 else 2))) else (if x<3214 then (if x<3178 then 3 else (if x<3180 then 2 else 3)) else (if x<3252 then (if x<3250 then 3 else 2) else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers313 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2614,2620,2638,2680,2710,2730,2732,2772,2776,2788,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers313 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers313 2776 5
  · have he : independentCachedBranchMembers313.erase 2776=independentCachedBranchMembers311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound311
  · have he : independentCachedBranchMembers313.filter (independentCachedEdge 2776)=independentCachedBranchMembers312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound312
def independentCachedBranchMembers314 : Finset ℕ := ([1614,1702,1768,2614,2680,2732,3102,3118,3164,3180,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers314 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers314 5 (fun x => (if x<3118 then (if x<2614 then (if x<1702 then 0 else (if x<1768 then 0 else 0)) else (if x<2732 then (if x<2680 then 1 else 1) else (if x<3102 then 1 else 2))) else (if x<3252 then (if x<3164 then 3 else (if x<3180 then 3 else 2)) else (if x<3270 then (if x<3256 then 2 else 3) else (if x<3274 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers315 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2614,2620,2638,2674,2680,2710,2730,2732,2772,2776,2788,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers315 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers315 2674 5
  · have he : independentCachedBranchMembers315.erase 2674=independentCachedBranchMembers313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound313
  · have he : independentCachedBranchMembers315.filter (independentCachedEdge 2674)=independentCachedBranchMembers314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound314
def independentCachedBranchMembers316 : Finset ℕ := ([1692,1702,1746,1768,2620,2638,2674,2710,2730,2732,2776,2788,3118,3164,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers316 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers316 5 (fun x => (if x<2730 then (if x<2620 then (if x<1746 then (if x<1702 then 0 else 0) else (if x<1768 then 0 else 0)) else (if x<2674 then (if x<2638 then 1 else 1) else (if x<2710 then 1 else 0))) else (if x<3118 then (if x<2776 then (if x<2732 then 1 else 0) else (if x<2788 then 0 else 1)) else (if x<3256 then (if x<3164 then 2 else 2) else (if x<3274 then 2 else (if x<3276 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers317 : Finset ℕ := ([1594,1614,1652,1686,1692,1702,1746,1768,2614,2620,2638,2674,2680,2710,2730,2732,2772,2776,2788,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers317 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers317 1686 5
  · have he : independentCachedBranchMembers317.erase 1686=independentCachedBranchMembers315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound315
  · have he : independentCachedBranchMembers317.filter (independentCachedEdge 1686)=independentCachedBranchMembers316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound316
def independentCachedBranchMembers318 : Finset ℕ := ([1594,1652,1692,1746,2620,2638,2674,2710,2730,2772,2776,2788,3158,3178,3214,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers318 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers318 5 (fun x => (if x<2730 then (if x<2620 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2674 then (if x<2638 then 0 else 1) else (if x<2710 then 0 else 1))) else (if x<3158 then (if x<2776 then (if x<2772 then 1 else 0) else (if x<2788 then 1 else 1)) else (if x<3214 then (if x<3178 then 2 else 2) else (if x<3250 then 2 else (if x<3276 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers319 : Finset ℕ := ([1594,1596,1614,1652,1686,1692,1702,1746,1768,2614,2620,2638,2674,2680,2710,2730,2732,2772,2776,2788,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers319 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers319 1596 5
  · have he : independentCachedBranchMembers319.erase 1596=independentCachedBranchMembers317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound317
  · have he : independentCachedBranchMembers319.filter (independentCachedEdge 1596)=independentCachedBranchMembers318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound318
def independentCachedBranchMembers320 : Finset ℕ := ([1594,1614,1686,1702,1746,2614,2638,2674,2710,2730,3102,3118,3158,3178,3214,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers320 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers320 5 (fun x => (if x<2730 then (if x<1746 then (if x<1686 then (if x<1614 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<2638 then (if x<2614 then 1 else 2) else (if x<2674 then 2 else (if x<2710 then 3 else 1)))) else (if x<3178 then (if x<3118 then (if x<3102 then 2 else 0) else (if x<3158 then 2 else 2)) else (if x<3250 then (if x<3214 then 0 else 3) else (if x<3270 then 0 else (if x<3274 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers321 : Finset ℕ := ([252,1594,1596,1614,1652,1686,1692,1702,1746,1768,2614,2620,2638,2674,2680,2710,2730,2732,2772,2776,2788,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers321 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers321 252 5
  · have he : independentCachedBranchMembers321.erase 252=independentCachedBranchMembers319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound319
  · have he : independentCachedBranchMembers321.filter (independentCachedEdge 252)=independentCachedBranchMembers320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound320
def independentCachedBranchMembers322 : Finset ℕ := ([1596,1614,1652,1746,1768,2614,2620,2638,2730,2776,3102,3118,3158,3164,3180,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers322 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers322 5 (fun x => (if x<2776 then (if x<1768 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2620 then (if x<2614 then 0 else 2) else (if x<2638 then 1 else (if x<2730 then 2 else 2)))) else (if x<3164 then (if x<3118 then (if x<3102 then 3 else 0) else (if x<3158 then 2 else 2)) else (if x<3250 then (if x<3180 then 3 else 0) else (if x<3256 then 2 else (if x<3274 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers323 : Finset ℕ := ([132,252,1594,1596,1614,1652,1686,1692,1702,1746,1768,2614,2620,2638,2674,2680,2710,2730,2732,2772,2776,2788,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers323 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers323 132 5
  · have he : independentCachedBranchMembers323.erase 132=independentCachedBranchMembers321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound321
  · have he : independentCachedBranchMembers323.filter (independentCachedEdge 132)=independentCachedBranchMembers322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound322
def independentCachedBranchMembers324 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2620,2674,2710,2732,2772,2776,3118,3158,3180,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers324 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers324 5 (fun x => (if x<2710 then (if x<1702 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1692 then 0 else 0)) else (if x<1768 then (if x<1746 then 0 else 0) else (if x<2620 then 0 else (if x<2674 then 1 else 1)))) else (if x<3158 then (if x<2772 then (if x<2732 then 1 else 2) else (if x<2776 then 2 else (if x<3118 then 1 else 2))) else (if x<3250 then (if x<3180 then 2 else 3) else (if x<3270 then 4 else (if x<3274 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers325 : Finset ℕ := ([132,252,1594,1596,1614,1652,1686,1692,1702,1746,1768,2614,2620,2638,2674,2680,2710,2716,2730,2732,2772,2776,2788,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers325 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers325 2716 5
  · have he : independentCachedBranchMembers325.erase 2716=independentCachedBranchMembers323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound323
  · have he : independentCachedBranchMembers325.filter (independentCachedEdge 2716)=independentCachedBranchMembers324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound324
def independentCachedBranchMembers326 : Finset ℕ := ([1594,1596,1614,1652,1692,1702,1746,1768,2614,2680,2710,2730,2732,2776,2788,3118,3164,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers326 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers326 5 (fun x => (if x<2710 then (if x<1702 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1652 then 0 else (if x<1692 then 0 else 0))) else (if x<1768 then (if x<1746 then 0 else 0) else (if x<2614 then 0 else (if x<2680 then 1 else 1)))) else (if x<3118 then (if x<2732 then (if x<2730 then 2 else 2) else (if x<2776 then 1 else (if x<2788 then 2 else 2))) else (if x<3250 then (if x<3164 then 3 else (if x<3214 then 3 else 4)) else (if x<3252 then 4 else (if x<3270 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers327 : Finset ℕ := ([1596,1614,1652,1746,1768,2614,2730,2776,3118,3164,3250] : List ℕ).toFinset
theorem independentCachedBranchBound327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers327 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers327 4 (fun x => (if x<2614 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1746 then 1 else (if x<1768 then 1 else 0))) else (if x<3118 then (if x<2730 then 2 else (if x<2776 then 2 else 3)) else (if x<3164 then 2 else (if x<3250 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers328 : Finset ℕ := ([132,1594,1596,1614,1652,1692,1702,1746,1768,2614,2680,2710,2730,2732,2776,2788,3118,3164,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers328 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers328 132 4
  · have he : independentCachedBranchMembers328.erase 132=independentCachedBranchMembers326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound326
  · have he : independentCachedBranchMembers328.filter (independentCachedEdge 132)=independentCachedBranchMembers327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound327
def independentCachedBranchMembers329 : Finset ℕ := ([132,252,1594,1596,1614,1652,1686,1692,1702,1746,1768,2614,2620,2638,2674,2680,2710,2716,2730,2732,2772,2776,2788,2792,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers329 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers329 2792 5
  · have he : independentCachedBranchMembers329.erase 2792=independentCachedBranchMembers325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound325
  · have he : independentCachedBranchMembers329.filter (independentCachedEdge 2792)=independentCachedBranchMembers328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound328
def independentCachedBranchMembers330 : Finset ℕ := ([1594,1614,1652,1692,1702,1746,1768,2614,2620,2674,2680,2730,2772,2788,3158,3164,3180,3214,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers330 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers330 5 (fun x => (if x<2680 then (if x<1746 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1692 then 0 else (if x<1702 then 0 else 0))) else (if x<2614 then (if x<1768 then 0 else 0) else (if x<2620 then 1 else (if x<2674 then 2 else 2)))) else (if x<3164 then (if x<2772 then (if x<2730 then 1 else 1) else (if x<2788 then 2 else (if x<3158 then 1 else 3))) else (if x<3214 then (if x<3180 then 4 else 3) else (if x<3252 then 3 else (if x<3274 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers331 : Finset ℕ := ([1692,1702,1746,1768,2620,2674,2730,2788,3164,3274] : List ℕ).toFinset
theorem independentCachedBranchBound331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers331 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers331 4 (fun x => (if x<2674 then (if x<1746 then (if x<1702 then 0 else 0) else (if x<1768 then 0 else (if x<2620 then 0 else 1))) else (if x<2788 then (if x<2730 then 1 else 1) else (if x<3164 then 1 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers332 : Finset ℕ := ([1594,1614,1652,1686,1692,1702,1746,1768,2614,2620,2674,2680,2730,2772,2788,3158,3164,3180,3214,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers332 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers332 1686 4
  · have he : independentCachedBranchMembers332.erase 1686=independentCachedBranchMembers330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound330
  · have he : independentCachedBranchMembers332.filter (independentCachedEdge 1686)=independentCachedBranchMembers331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound331
def independentCachedBranchMembers333 : Finset ℕ := ([1594,1614,1686,1702,1746,2614,2674,2730,3158,3214,3274] : List ℕ).toFinset
theorem independentCachedBranchBound333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers333 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers333 4 (fun x => (if x<2614 then (if x<1686 then (if x<1614 then 0 else 0) else (if x<1702 then 0 else (if x<1746 then 1 else 1))) else (if x<3158 then (if x<2674 then 2 else (if x<2730 then 3 else 2)) else (if x<3214 then 2 else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers334 : Finset ℕ := ([252,1594,1614,1652,1686,1692,1702,1746,1768,2614,2620,2674,2680,2730,2772,2788,3158,3164,3180,3214,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers334 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers334 252 4
  · have he : independentCachedBranchMembers334.erase 252=independentCachedBranchMembers332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound332
  · have he : independentCachedBranchMembers334.filter (independentCachedEdge 252)=independentCachedBranchMembers333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound333
def independentCachedBranchMembers335 : Finset ℕ := ([132,252,1594,1596,1614,1652,1686,1692,1702,1746,1768,2614,2618,2620,2638,2674,2680,2710,2716,2730,2732,2772,2776,2788,2792,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers335 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers335 2618 5
  · have he : independentCachedBranchMembers335.erase 2618=independentCachedBranchMembers329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound329
  · have he : independentCachedBranchMembers335.filter (independentCachedEdge 2618)=independentCachedBranchMembers334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound334
def independentCachedBranchMembers336 : Finset ℕ := ([1594,1652,1702,1768,2614,2620,2638,2674,2680,2710,2716,2730,2776,2788,3118,3158,3164,3178,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers336 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers336 5 (fun x => (if x<2730 then (if x<2620 then (if x<1702 then (if x<1652 then 0 else 0) else (if x<1768 then 0 else (if x<2614 then 0 else 0))) else (if x<2680 then (if x<2638 then 1 else (if x<2674 then 1 else 1)) else (if x<2710 then 0 else (if x<2716 then 1 else 2)))) else (if x<3164 then (if x<2788 then (if x<2776 then 0 else 1) else (if x<3118 then 0 else (if x<3158 then 3 else 3))) else (if x<3250 then (if x<3178 then 2 else (if x<3214 then 2 else 2)) else (if x<3256 then 3 else (if x<3274 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers337 : Finset ℕ := ([132,252,1594,1596,1614,1652,1686,1692,1702,1746,1764,1768,2614,2618,2620,2638,2674,2680,2710,2716,2730,2732,2772,2776,2788,2792,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers337 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers337 1764 5
  · have he : independentCachedBranchMembers337.erase 1764=independentCachedBranchMembers335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound335
  · have he : independentCachedBranchMembers337.filter (independentCachedEdge 1764)=independentCachedBranchMembers336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound336
def independentCachedBranchMembers338 : Finset ℕ := ([132,252,1594,1596,1652,1686,1702,1768,2614,2638,2680,2716,2730,2732,2772,2788,3164,3178,3180,3214,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers338 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers338 5 (fun x => (if x<2716 then (if x<1686 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1596 then 1 else (if x<1652 then 2 else 1))) else (if x<2614 then (if x<1702 then 1 else (if x<1768 then 2 else 2)) else (if x<2638 then 1 else (if x<2680 then 3 else 0)))) else (if x<3164 then (if x<2732 then (if x<2730 then 0 else 3) else (if x<2772 then 2 else (if x<2788 then 1 else 0))) else (if x<3214 then (if x<3178 then 3 else (if x<3180 then 3 else 4)) else (if x<3256 then 3 else (if x<3270 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers339 : Finset ℕ := ([132,252,1590,1594,1596,1614,1652,1686,1692,1702,1746,1764,1768,2614,2618,2620,2638,2674,2680,2710,2716,2730,2732,2772,2776,2788,2792,3102,3118,3158,3164,3178,3180,3214,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers339 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers339 1590 5
  · have he : independentCachedBranchMembers339.erase 1590=independentCachedBranchMembers337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound337
  · have he : independentCachedBranchMembers339.filter (independentCachedEdge 1590)=independentCachedBranchMembers338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound338
def independentCachedBranchMembers340 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2788,2792,2800,3102,3118,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers340 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers340 3150 6
  · have he : independentCachedBranchMembers340.erase 3150=independentCachedBranchMembers310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound310
  · have he : independentCachedBranchMembers340.filter (independentCachedEdge 3150)=independentCachedBranchMembers339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound339
def independentCachedBranchMembers341 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2614,2638,2650,2680,2716,2730,2732,2772,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers341 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers341 6 (fun x => (if x<2772 then (if x<2614 then (if x<1678 then (if x<1628 then 0 else (if x<1642 then 0 else 0)) else (if x<1746 then (if x<1720 then 0 else 0) else (if x<1764 then 0 else 0))) else (if x<2680 then (if x<2638 then 1 else (if x<2650 then 1 else 2)) else (if x<2730 then (if x<2716 then 1 else 1) else (if x<2732 then 1 else 3)))) else (if x<3188 then (if x<3118 then (if x<2800 then 2 else (if x<3102 then 3 else 4)) else (if x<3158 then (if x<3130 then 3 else 2) else (if x<3186 then 2 else 3))) else (if x<3274 then (if x<3250 then (if x<3238 then 4 else 4) else (if x<3252 then 5 else 2)) else (if x<3288 then (if x<3276 then 5 else 4) else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers342 : Finset ℕ := ([1590,1628,1642,2638,2680,2772,3102,3118,3186,3188,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers342 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers342 5 (fun x => (if x<3118 then (if x<2638 then (if x<1628 then 0 else (if x<1642 then 0 else 0)) else (if x<2772 then (if x<2680 then 1 else 1) else (if x<3102 then 1 else 2))) else (if x<3250 then (if x<3186 then 3 else (if x<3188 then 2 else 3)) else (if x<3288 then (if x<3252 then 3 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers343 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2614,2638,2650,2680,2716,2730,2732,2758,2772,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers343 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers343 2758 5
  · have he : independentCachedBranchMembers343.erase 2758=independentCachedBranchMembers341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound341
  · have he : independentCachedBranchMembers343.filter (independentCachedEdge 2758)=independentCachedBranchMembers342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound342
def independentCachedBranchMembers344 : Finset ℕ := ([1590,1678,1720,2638,2680,2732,3102,3130,3158,3186,3238,3252,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers344 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers344 5 (fun x => (if x<3130 then (if x<2638 then (if x<1678 then 0 else (if x<1720 then 0 else 0)) else (if x<2732 then (if x<2680 then 1 else 1) else (if x<3102 then 1 else 2))) else (if x<3238 then (if x<3158 then 3 else (if x<3186 then 3 else 2)) else (if x<3274 then (if x<3252 then 2 else 3) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers345 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2614,2638,2650,2668,2680,2716,2730,2732,2758,2772,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers345 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers345 2668 5
  · have he : independentCachedBranchMembers345.erase 2668=independentCachedBranchMembers343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound343
  · have he : independentCachedBranchMembers345.filter (independentCachedEdge 2668)=independentCachedBranchMembers344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound344
def independentCachedBranchMembers346 : Finset ℕ := ([1678,1720,1746,1764,2614,2650,2668,2716,2730,2732,2758,2800,3130,3158,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers346 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers346 5 (fun x => (if x<2730 then (if x<2614 then (if x<1746 then (if x<1720 then 0 else 0) else (if x<1764 then 0 else 0)) else (if x<2668 then (if x<2650 then 1 else 1) else (if x<2716 then 1 else 1))) else (if x<3130 then (if x<2758 then (if x<2732 then 1 else 0) else (if x<2800 then 0 else 0)) else (if x<3238 then (if x<3158 then 2 else 2) else (if x<3274 then 2 else (if x<3276 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers347 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,1776,2614,2638,2650,2668,2680,2716,2730,2732,2758,2772,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers347 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers347 1776 5
  · have he : independentCachedBranchMembers347.erase 1776=independentCachedBranchMembers345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound345
  · have he : independentCachedBranchMembers347.filter (independentCachedEdge 1776)=independentCachedBranchMembers346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound346
def independentCachedBranchMembers348 : Finset ℕ := ([1628,1642,1746,1764,2614,2650,2668,2716,2730,2758,2772,2800,3118,3188,3250,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers348 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers348 5 (fun x => (if x<2730 then (if x<2614 then (if x<1746 then (if x<1642 then 0 else 0) else (if x<1764 then 0 else 0)) else (if x<2668 then (if x<2650 then 1 else 0) else (if x<2716 then 0 else 1))) else (if x<3118 then (if x<2772 then (if x<2758 then 1 else 1) else (if x<2800 then 0 else 1)) else (if x<3250 then (if x<3188 then 2 else 2) else (if x<3276 then 2 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers349 : Finset ℕ := ([1590,1626,1628,1642,1678,1720,1746,1764,1776,2614,2638,2650,2668,2680,2716,2730,2732,2758,2772,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers349 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers349 1626 5
  · have he : independentCachedBranchMembers349.erase 1626=independentCachedBranchMembers347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound347
  · have he : independentCachedBranchMembers349.filter (independentCachedEdge 1626)=independentCachedBranchMembers348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound348
def independentCachedBranchMembers350 : Finset ℕ := ([1590,1626,1642,1678,1746,2614,2638,2650,2730,2758,3102,3118,3130,3158,3186,3238,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers350 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers350 5 (fun x => (if x<2758 then (if x<1746 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1678 then 1 else 0)) else (if x<2638 then (if x<2614 then 1 else 2) else (if x<2650 then 2 else (if x<2730 then 1 else 2)))) else (if x<3158 then (if x<3118 then (if x<3102 then 3 else 0) else (if x<3130 then 2 else 3)) else (if x<3238 then (if x<3186 then 2 else 0) else (if x<3250 then 0 else (if x<3274 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers351 : Finset ℕ := ([252,1590,1626,1628,1642,1678,1720,1746,1764,1776,2614,2638,2650,2668,2680,2716,2730,2732,2758,2772,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers351 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers351 252 5
  · have he : independentCachedBranchMembers351.erase 252=independentCachedBranchMembers349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound349
  · have he : independentCachedBranchMembers351.filter (independentCachedEdge 252)=independentCachedBranchMembers350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound350
def independentCachedBranchMembers352 : Finset ℕ := ([1590,1628,1720,1746,1776,2614,2638,2668,2730,2800,3102,3118,3158,3188,3250,3274,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers352 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers352 5 (fun x => (if x<2800 then (if x<1776 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2638 then (if x<2614 then 1 else 2) else (if x<2668 then 1 else (if x<2730 then 2 else 2)))) else (if x<3188 then (if x<3118 then (if x<3102 then 2 else 1) else (if x<3158 then 2 else 0)) else (if x<3274 then (if x<3250 then 2 else 0) else (if x<3288 then 3 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers353 : Finset ℕ := ([132,252,1590,1626,1628,1642,1678,1720,1746,1764,1776,2614,2638,2650,2668,2680,2716,2730,2732,2758,2772,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers353 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers353 132 5
  · have he : independentCachedBranchMembers353.erase 132=independentCachedBranchMembers351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound351
  · have he : independentCachedBranchMembers353.filter (independentCachedEdge 132)=independentCachedBranchMembers352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound352
def independentCachedBranchMembers354 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2650,2668,2732,2758,2772,2800,3118,3158,3186,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers354 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers354 5 (fun x => (if x<2732 then (if x<1720 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 0 else 0)) else (if x<1764 then (if x<1746 then 0 else 0) else (if x<2650 then 0 else (if x<2668 then 1 else 1)))) else (if x<3158 then (if x<2772 then (if x<2758 then 2 else 1) else (if x<2800 then 2 else (if x<3118 then 1 else 2))) else (if x<3250 then (if x<3186 then 2 else 3) else (if x<3274 then 4 else (if x<3288 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers355 : Finset ℕ := ([132,252,1590,1626,1628,1642,1678,1720,1746,1764,1776,2614,2638,2650,2668,2680,2716,2730,2732,2758,2772,2788,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers355 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers355 2788 5
  · have he : independentCachedBranchMembers355.erase 2788=independentCachedBranchMembers353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound353
  · have he : independentCachedBranchMembers355.filter (independentCachedEdge 2788)=independentCachedBranchMembers354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound354
def independentCachedBranchMembers356 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,2638,2680,2716,2730,2732,2758,2800,3130,3158,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers356 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers356 5 (fun x => (if x<2730 then (if x<1746 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 0 else (if x<1720 then 0 else 0))) else (if x<2638 then (if x<1764 then 0 else 0) else (if x<2680 then 1 else (if x<2716 then 1 else 1)))) else (if x<3158 then (if x<2758 then (if x<2732 then 1 else 2) else (if x<2800 then 2 else (if x<3130 then 2 else 3))) else (if x<3252 then (if x<3250 then 3 else 4) else (if x<3288 then 3 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers357 : Finset ℕ := ([1628,1642,1746,1764,2716,2730,2758,2800,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers357 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers357 4 (fun x => (if x<2730 then (if x<1746 then (if x<1642 then 0 else 0) else (if x<1764 then 0 else (if x<2716 then 0 else 1))) else (if x<2800 then (if x<2758 then 1 else 1) else (if x<3250 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers358 : Finset ℕ := ([1590,1626,1628,1642,1678,1720,1746,1764,2638,2680,2716,2730,2732,2758,2800,3130,3158,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers358 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers358 1626 4
  · have he : independentCachedBranchMembers358.erase 1626=independentCachedBranchMembers356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound356
  · have he : independentCachedBranchMembers358.filter (independentCachedEdge 1626)=independentCachedBranchMembers357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound357
def independentCachedBranchMembers359 : Finset ℕ := ([1590,1626,1642,1678,1746,2638,2730,2758,3130,3158,3250] : List ℕ).toFinset
theorem independentCachedBranchBound359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers359 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers359 4 (fun x => (if x<2638 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1678 then 1 else (if x<1746 then 0 else 1))) else (if x<3130 then (if x<2730 then 2 else (if x<2758 then 2 else 3)) else (if x<3158 then 3 else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers360 : Finset ℕ := ([252,1590,1626,1628,1642,1678,1720,1746,1764,2638,2680,2716,2730,2732,2758,2800,3130,3158,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers360 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers360 252 4
  · have he : independentCachedBranchMembers360.erase 252=independentCachedBranchMembers358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound358
  · have he : independentCachedBranchMembers360.filter (independentCachedEdge 252)=independentCachedBranchMembers359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound359
def independentCachedBranchMembers361 : Finset ℕ := ([132,252,1590,1626,1628,1642,1678,1720,1746,1764,1776,2614,2638,2650,2668,2680,2702,2716,2730,2732,2758,2772,2788,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers361 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers361 2702 5
  · have he : independentCachedBranchMembers361.erase 2702=independentCachedBranchMembers355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound355
  · have he : independentCachedBranchMembers361.filter (independentCachedEdge 2702)=independentCachedBranchMembers360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound360
def independentCachedBranchMembers362 : Finset ℕ := ([1590,1628,1642,1678,1720,1746,1764,1776,2638,2650,2668,2680,2716,2730,2772,3118,3130,3186,3252,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers362 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers362 5 (fun x => (if x<2668 then (if x<1746 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1678 then 0 else (if x<1720 then 0 else 0))) else (if x<1776 then (if x<1764 then 0 else 0) else (if x<2638 then 1 else (if x<2650 then 1 else 2)))) else (if x<3118 then (if x<2716 then (if x<2680 then 2 else 1) else (if x<2730 then 2 else (if x<2772 then 2 else 1))) else (if x<3252 then (if x<3130 then 3 else (if x<3186 then 4 else 3)) else (if x<3274 then 3 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers363 : Finset ℕ := ([1590,1628,1720,1746,1776,2638,2668,2730,3118,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers363 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers363 4 (fun x => (if x<2638 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<1746 then 0 else (if x<1776 then 0 else 1))) else (if x<3118 then (if x<2668 then 1 else (if x<2730 then 2 else 2)) else (if x<3274 then 1 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers364 : Finset ℕ := ([132,1590,1628,1642,1678,1720,1746,1764,1776,2638,2650,2668,2680,2716,2730,2772,3118,3130,3186,3252,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers364 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers364 132 4
  · have he : independentCachedBranchMembers364.erase 132=independentCachedBranchMembers362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound362
  · have he : independentCachedBranchMembers364.filter (independentCachedEdge 132)=independentCachedBranchMembers363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound363
def independentCachedBranchMembers365 : Finset ℕ := ([132,252,1590,1626,1628,1642,1678,1720,1746,1764,1776,2614,2638,2650,2652,2668,2680,2702,2716,2730,2732,2758,2772,2788,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers365 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers365 2652 5
  · have he : independentCachedBranchMembers365.erase 2652=independentCachedBranchMembers361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound361
  · have he : independentCachedBranchMembers365.filter (independentCachedEdge 2652)=independentCachedBranchMembers364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound364
def independentCachedBranchMembers366 : Finset ℕ := ([1628,1642,1678,1720,2614,2638,2650,2668,2680,2716,2730,2758,2788,2800,3118,3130,3158,3188,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers366 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers366 5 (fun x => (if x<2758 then (if x<2638 then (if x<1678 then (if x<1642 then 0 else 0) else (if x<1720 then 0 else (if x<2614 then 0 else 1))) else (if x<2680 then (if x<2650 then 0 else (if x<2668 then 1 else 1)) else (if x<2716 then 0 else (if x<2730 then 0 else 0)))) else (if x<3158 then (if x<2800 then (if x<2788 then 1 else 2) else (if x<3118 then 1 else (if x<3130 then 3 else 2))) else (if x<3250 then (if x<3188 then 3 else (if x<3238 then 2 else 2)) else (if x<3274 then 3 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers367 : Finset ℕ := ([132,252,1590,1626,1628,1642,1678,1692,1720,1746,1764,1776,2614,2638,2650,2652,2668,2680,2702,2716,2730,2732,2758,2772,2788,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers367 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers367 1692 5
  · have he : independentCachedBranchMembers367.erase 1692=independentCachedBranchMembers365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound365
  · have he : independentCachedBranchMembers367.filter (independentCachedEdge 1692)=independentCachedBranchMembers366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound366
def independentCachedBranchMembers368 : Finset ℕ := ([132,252,1626,1628,1642,1678,1720,1776,2614,2638,2680,2716,2730,2732,2772,2788,3130,3186,3188,3238,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers368 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers368 5 (fun x => (if x<2716 then (if x<1678 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1628 then 1 else (if x<1642 then 2 else 2))) else (if x<2614 then (if x<1720 then 1 else (if x<1776 then 1 else 2)) else (if x<2638 then 3 else (if x<2680 then 1 else 0)))) else (if x<3130 then (if x<2732 then (if x<2730 then 0 else 3) else (if x<2772 then 1 else (if x<2788 then 2 else 0))) else (if x<3238 then (if x<3186 then 3 else (if x<3188 then 4 else 3)) else (if x<3288 then 3 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers369 : Finset ℕ := ([132,252,1590,1614,1626,1628,1642,1678,1692,1720,1746,1764,1776,2614,2638,2650,2652,2668,2680,2702,2716,2730,2732,2758,2772,2788,2800,3102,3118,3130,3158,3186,3188,3238,3250,3252,3274,3276,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers369 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers369 1614 5
  · have he : independentCachedBranchMembers369.erase 1614=independentCachedBranchMembers367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound367
  · have he : independentCachedBranchMembers369.filter (independentCachedEdge 1614)=independentCachedBranchMembers368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound368
def independentCachedBranchMembers370 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers370 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers370 3126 6
  · have he : independentCachedBranchMembers370.erase 3126=independentCachedBranchMembers340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound340
  · have he : independentCachedBranchMembers370.filter (independentCachedEdge 3126)=independentCachedBranchMembers369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound369
def independentCachedBranchMembers371 : Finset ℕ := ([48,252,1652,1686,1720,1740,2620,2652,2662,2674,2716,2730,2738,2758,2762,2788,2792,2800,3126,3130,3150,3158,3180,3188,3192,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers371 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers371 6 (fun x => (if x<2800 then (if x<2662 then (if x<1720 then (if x<1652 then (if x<252 then 0 else 0) else (if x<1686 then 0 else 1)) else (if x<2620 then (if x<1740 then 0 else 0) else (if x<2652 then 2 else 3))) else (if x<2738 then (if x<2716 then (if x<2674 then 2 else 3) else (if x<2730 then 1 else 2)) else (if x<2762 then (if x<2758 then 1 else 1) else (if x<2788 then 3 else (if x<2792 then 3 else 1))))) else (if x<3214 then (if x<3158 then (if x<3130 then (if x<3126 then 2 else 4) else (if x<3150 then 5 else 4)) else (if x<3188 then (if x<3180 then 5 else 5) else (if x<3192 then 2 else 4))) else (if x<3256 then (if x<3244 then (if x<3226 then 5 else 4) else (if x<3252 then 4 else 5)) else (if x<3284 then (if x<3276 then 2 else 3) else (if x<3288 then 4 else (if x<3298 then 5 else 2)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers372 : Finset ℕ := ([48,252,2620,2662,2716,2730,2738,2758,2792,2800,3126,3180,3188,3214,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers372 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers372 5 (fun x => (if x<2800 then (if x<2716 then (if x<2620 then (if x<252 then 0 else 0) else (if x<2662 then 0 else 1)) else (if x<2738 then (if x<2730 then 2 else 1) else (if x<2758 then 2 else (if x<2792 then 2 else 2)))) else (if x<3214 then (if x<3180 then (if x<3126 then 0 else 3) else (if x<3188 then 3 else 0)) else (if x<3276 then (if x<3256 then 3 else 0) else (if x<3284 then 2 else (if x<3298 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers373 : Finset ℕ := ([48,252,1626,1652,1686,1720,1740,2620,2652,2662,2674,2716,2730,2738,2758,2762,2788,2792,2800,3126,3130,3150,3158,3180,3188,3192,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers373 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers373 1626 5
  · have he : independentCachedBranchMembers373.erase 1626=independentCachedBranchMembers371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound371
  · have he : independentCachedBranchMembers373.filter (independentCachedEdge 1626)=independentCachedBranchMembers372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound372
def independentCachedBranchMembers374 : Finset ℕ := ([1652,1720,2620,2652,2662,2730,2738,2762,2792,2800,3126,3150,3158,3180,3188,3226,3256,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers374 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers374 5 (fun x => (if x<2800 then (if x<2662 then (if x<2620 then (if x<1720 then 0 else 0) else (if x<2652 then 0 else 1)) else (if x<2738 then (if x<2730 then 0 else 0) else (if x<2762 then 2 else (if x<2792 then 1 else 2)))) else (if x<3188 then (if x<3150 then (if x<3126 then 0 else 2) else (if x<3158 then 1 else (if x<3180 then 3 else 2))) else (if x<3256 then (if x<3226 then 1 else 3) else (if x<3288 then 2 else (if x<3298 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers375 : Finset ℕ := ([48,132,252,1626,1652,1686,1720,1740,2620,2652,2662,2674,2716,2730,2738,2758,2762,2788,2792,2800,3126,3130,3150,3158,3180,3188,3192,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers375 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers375 132 5
  · have he : independentCachedBranchMembers375.erase 132=independentCachedBranchMembers373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound373
  · have he : independentCachedBranchMembers375.filter (independentCachedEdge 132)=independentCachedBranchMembers374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound374
def independentCachedBranchMembers376 : Finset ℕ := ([252,1652,1686,1740,2620,2652,2662,2738,2788,2792,3126,3130,3158,3180,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers376 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers376 5 (fun x => (if x<3126 then (if x<2652 then (if x<1686 then (if x<1652 then 0 else 0) else (if x<1740 then 1 else (if x<2620 then 0 else 2))) else (if x<2738 then (if x<2662 then 0 else 2) else (if x<2788 then 1 else (if x<2792 then 0 else 1)))) else (if x<3252 then (if x<3158 then (if x<3130 then 1 else 3) else (if x<3180 then 3 else (if x<3214 then 0 else 3))) else (if x<3284 then (if x<3256 then 3 else 2) else (if x<3288 then 0 else (if x<3298 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers377 : Finset ℕ := ([48,132,252,1626,1652,1678,1686,1720,1740,2620,2652,2662,2674,2716,2730,2738,2758,2762,2788,2792,2800,3126,3130,3150,3158,3180,3188,3192,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers377 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers377 1678 5
  · have he : independentCachedBranchMembers377.erase 1678=independentCachedBranchMembers375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound375
  · have he : independentCachedBranchMembers377.filter (independentCachedEdge 1678)=independentCachedBranchMembers376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound376
def independentCachedBranchMembers378 : Finset ℕ := ([252,1626,1720,1740,2652,2662,2716,2762,2792,2800,3130,3150,3158,3180,3188,3214,3244,3252,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers378 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers378 5 (fun x => (if x<3130 then (if x<2662 then (if x<1720 then (if x<1626 then 0 else 1) else (if x<1740 then 0 else (if x<2652 then 0 else 1))) else (if x<2762 then (if x<2716 then 2 else 0) else (if x<2792 then 1 else (if x<2800 then 0 else 2)))) else (if x<3214 then (if x<3158 then (if x<3150 then 3 else 1) else (if x<3180 then 3 else (if x<3188 then 3 else 2))) else (if x<3252 then (if x<3244 then 3 else 0) else (if x<3288 then 3 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers379 : Finset ℕ := ([48,132,252,1594,1626,1652,1678,1686,1720,1740,2620,2652,2662,2674,2716,2730,2738,2758,2762,2788,2792,2800,3126,3130,3150,3158,3180,3188,3192,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers379 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers379 1594 5
  · have he : independentCachedBranchMembers379.erase 1594=independentCachedBranchMembers377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound377
  · have he : independentCachedBranchMembers379.filter (independentCachedEdge 1594)=independentCachedBranchMembers378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound378
def independentCachedBranchMembers380 : Finset ℕ := ([1594,1652,1678,1720,2620,2662,2674,2716,2730,2758,2788,2800,3130,3158,3188,3214,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers380 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers380 5 (fun x => (if x<2788 then (if x<2662 then (if x<1678 then (if x<1652 then 0 else 0) else (if x<1720 then 1 else (if x<2620 then 1 else 0))) else (if x<2716 then (if x<2674 then 2 else 0) else (if x<2730 then 1 else (if x<2758 then 0 else 1)))) else (if x<3214 then (if x<3130 then (if x<2800 then 0 else 1) else (if x<3158 then 3 else (if x<3188 then 2 else 3))) else (if x<3256 then (if x<3226 then 4 else (if x<3244 then 2 else 3)) else (if x<3284 then 4 else (if x<3298 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers381 : Finset ℕ := ([48,72,132,252,1594,1626,1652,1678,1686,1720,1740,2620,2652,2662,2674,2716,2730,2738,2758,2762,2788,2792,2800,3126,3130,3150,3158,3180,3188,3192,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers381 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers381 72 5
  · have he : independentCachedBranchMembers381.erase 72=independentCachedBranchMembers379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound379
  · have he : independentCachedBranchMembers381.filter (independentCachedEdge 72)=independentCachedBranchMembers380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound380
def independentCachedBranchMembers382 : Finset ℕ := ([132,252,1626,1678,1720,1740,2620,2674,2716,2730,2788,2792,3126,3130,3150,3188,3192,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers382 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers382 5 (fun x => (if x<2792 then (if x<1740 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1678 then 1 else (if x<1720 then 1 else 1))) else (if x<2716 then (if x<2620 then 0 else (if x<2674 then 2 else 2)) else (if x<2730 then 0 else (if x<2788 then 2 else 0)))) else (if x<3192 then (if x<3130 then (if x<3126 then 3 else 3) else (if x<3150 then 2 else (if x<3188 then 1 else 2))) else (if x<3284 then (if x<3226 then 1 else (if x<3244 then 1 else 0)) else (if x<3288 then 0 else (if x<3298 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers383 : Finset ℕ := ([48,72,132,252,1594,1614,1626,1652,1678,1686,1720,1740,2620,2652,2662,2674,2716,2730,2738,2758,2762,2788,2792,2800,3126,3130,3150,3158,3180,3188,3192,3214,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers383 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers383 1614 5
  · have he : independentCachedBranchMembers383.erase 1614=independentCachedBranchMembers381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound381
  · have he : independentCachedBranchMembers383.filter (independentCachedEdge 1614)=independentCachedBranchMembers382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound382
end EntropyDesigns.QuadraticRefinement
