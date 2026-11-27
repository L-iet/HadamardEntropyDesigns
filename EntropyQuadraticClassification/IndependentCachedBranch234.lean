/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch233
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10272 : Finset ℕ := ([18,72,136,246,1590,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10272 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10272 3304 4
  · have he : independentCachedBranchMembers10272.erase 3304=independentCachedBranchMembers10270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10270
  · have he : independentCachedBranchMembers10272.filter (independentCachedEdge 3304)=independentCachedBranchMembers10271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10271
def independentCachedBranchMembers10273 : Finset ℕ := ([136,1686,1708,1740,2614,2646,2668,2770,2792,3186,3222,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10273 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10273 4 (fun x => (if x<2668 then (if x<1740 then (if x<1686 then 0 else (if x<1708 then 1 else 0)) else (if x<2614 then 1 else (if x<2646 then 1 else 0))) else (if x<3186 then (if x<2770 then 1 else (if x<2792 then 2 else 2)) else (if x<3222 then 0 else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10274 : Finset ℕ := ([18,72,136,246,1590,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10274 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10274 2710 4
  · have he : independentCachedBranchMembers10274.erase 2710=independentCachedBranchMembers10272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10272
  · have he : independentCachedBranchMembers10274.filter (independentCachedEdge 2710)=independentCachedBranchMembers10273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10273
def independentCachedBranchMembers10275 : Finset ℕ := ([72,1590,1686,1708,1746,1768,2646,2668,2764,3158,3180,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10275 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10275 4 (fun x => (if x<2646 then (if x<1708 then (if x<1590 then 0 else (if x<1686 then 0 else 1)) else (if x<1746 then 1 else (if x<1768 then 2 else 2))) else (if x<3158 then (if x<2668 then 1 else (if x<2764 then 1 else 0)) else (if x<3180 then 2 else (if x<3250 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10276 : Finset ℕ := ([18,72,136,246,1590,1622,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10276 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10276 1622 4
  · have he : independentCachedBranchMembers10276.erase 1622=independentCachedBranchMembers10274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10274
  · have he : independentCachedBranchMembers10276.filter (independentCachedEdge 1622)=independentCachedBranchMembers10275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10275
def independentCachedBranchMembers10277 : Finset ℕ := ([72,136,246,1590,1714,1740,2614,2674,2764,3126,3186,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10277 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10277 4 (fun x => (if x<2614 then (if x<1590 then (if x<136 then 0 else (if x<246 then 1 else 2)) else (if x<1714 then 0 else (if x<1740 then 2 else 1))) else (if x<3126 then (if x<2674 then 1 else (if x<2764 then 2 else 0)) else (if x<3186 then 2 else (if x<3250 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10278 : Finset ℕ := ([18,40,72,136,246,1590,1622,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10278 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10278 40 4
  · have he : independentCachedBranchMembers10278.erase 40=independentCachedBranchMembers10276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10276
  · have he : independentCachedBranchMembers10278.filter (independentCachedEdge 40)=independentCachedBranchMembers10277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10277
def independentCachedBranchMembers10279 : Finset ℕ := ([72,136,1590,1740,1746,1768,2614,2764,2770,2792,3158,3180,3186,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10279 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10279 4 (fun x => (if x<2770 then (if x<1746 then (if x<1590 then (if x<136 then 0 else 1) else (if x<1740 then 0 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2764 then 1 else 0))) else (if x<3186 then (if x<3158 then (if x<2792 then 3 else 3) else (if x<3180 then 2 else 2)) else (if x<3244 then (if x<3222 then 1 else 3) else (if x<3250 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10280 : Finset ℕ := ([18,40,72,136,246,1590,1622,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10280 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10280 3282 4
  · have he : independentCachedBranchMembers10280.erase 3282=independentCachedBranchMembers10278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10278
  · have he : independentCachedBranchMembers10280.filter (independentCachedEdge 3282)=independentCachedBranchMembers10279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10279
def independentCachedBranchMembers10281 : Finset ℕ := ([40,246,1622,1686,1740,1746,2646,2710,2764,2770,3126,3180,3186,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10281 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10281 4 (fun x => (if x<2764 then (if x<1740 then (if x<1622 then (if x<246 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<2646 then (if x<1746 then 2 else 2) else (if x<2710 then 1 else 0))) else (if x<3186 then (if x<3126 then (if x<2770 then 3 else 3) else (if x<3180 then 1 else 2)) else (if x<3250 then (if x<3244 then 2 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10282 : Finset ℕ := ([18,40,72,136,246,1590,1622,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10282 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10282 3276 4
  · have he : independentCachedBranchMembers10282.erase 3276=independentCachedBranchMembers10280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10280
  · have he : independentCachedBranchMembers10282.filter (independentCachedEdge 3276)=independentCachedBranchMembers10281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10281
def independentCachedBranchMembers10283 : Finset ℕ := ([40,136,1622,1708,1714,1768,2614,2668,2674,2710,2764,2770,3158,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10283 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10283 4 (fun x => (if x<2674 then (if x<1714 then (if x<1622 then (if x<136 then 0 else 1) else (if x<1708 then 0 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2668 then 2 else 2))) else (if x<3158 then (if x<2764 then (if x<2710 then 1 else 0) else (if x<2770 then 3 else 3)) else (if x<3250 then (if x<3244 then 1 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10284 : Finset ℕ := ([18,40,72,136,246,1590,1622,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2738,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10284 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10284 2738 4
  · have he : independentCachedBranchMembers10284.erase 2738=independentCachedBranchMembers10282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10282
  · have he : independentCachedBranchMembers10284.filter (independentCachedEdge 2738)=independentCachedBranchMembers10283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10283
def independentCachedBranchMembers10285 : Finset ℕ := ([72,246,1590,1686,1708,1714,2646,2668,2674,2764,2770,2792,3126,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10285 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10285 4 (fun x => (if x<2674 then (if x<1708 then (if x<1590 then (if x<246 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<2646 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3126 then (if x<2770 then (if x<2764 then 2 else 0) else (if x<2792 then 3 else 3)) else (if x<3244 then (if x<3222 then 1 else 3) else (if x<3250 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10286 : Finset ℕ := ([18,40,72,136,246,1590,1622,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2732,2738,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10286 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10286 2732 4
  · have he : independentCachedBranchMembers10286.erase 2732=independentCachedBranchMembers10284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10284
  · have he : independentCachedBranchMembers10286.filter (independentCachedEdge 2732)=independentCachedBranchMembers10285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10285
def independentCachedBranchMembers10287 : Finset ℕ := ([40,72,1590,1622,1708,1714,1740,1746,2668,2674,2710,2792,3180,3186,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10287 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10287 4 (fun x => (if x<2668 then (if x<1708 then (if x<1590 then (if x<72 then 0 else 1) else (if x<1622 then 1 else 0)) else (if x<1740 then (if x<1714 then 2 else 2) else (if x<1746 then 3 else 3))) else (if x<3180 then (if x<2710 then (if x<2674 then 2 else 2) else (if x<2792 then 0 else 1)) else (if x<3222 then (if x<3186 then 3 else 3) else (if x<3304 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10288 : Finset ℕ := ([18,40,72,136,246,1590,1622,1650,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2732,2738,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10288 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10288 1650 4
  · have he : independentCachedBranchMembers10288.erase 1650=independentCachedBranchMembers10286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10286
  · have he : independentCachedBranchMembers10288.filter (independentCachedEdge 1650)=independentCachedBranchMembers10287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10287
def independentCachedBranchMembers10289 : Finset ℕ := ([246,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,3126,3158,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10289 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10289 4 (fun x => (if x<2614 then (if x<1714 then (if x<1686 then 0 else (if x<1708 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 2) else (if x<1768 then 2 else 3))) else (if x<3126 then (if x<2668 then (if x<2646 then 0 else 3) else (if x<2674 then 1 else 1)) else (if x<3180 then (if x<3158 then 3 else 0) else (if x<3186 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10290 : Finset ℕ := ([246,1686,1714,1746,2668,3180] : List ℕ).toFinset
theorem independentCachedBranchBound10290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10290 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10290 3 (fun x => (if x<1746 then (if x<1686 then 0 else (if x<1714 then 0 else 1)) else (if x<2668 then 2 else (if x<3180 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10291 : Finset ℕ := ([136,246,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,3126,3158,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10291 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10291 136 3
  · have he : independentCachedBranchMembers10291.erase 136=independentCachedBranchMembers10289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10289
  · have he : independentCachedBranchMembers10291.filter (independentCachedEdge 136)=independentCachedBranchMembers10290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10290
def independentCachedBranchMembers10292 : Finset ℕ := ([18,40,72,136,246,1590,1622,1644,1650,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2732,2738,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10292 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10292 1644 4
  · have he : independentCachedBranchMembers10292.erase 1644=independentCachedBranchMembers10288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10288
  · have he : independentCachedBranchMembers10292.filter (independentCachedEdge 1644)=independentCachedBranchMembers10291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10291
def independentCachedBranchMembers10293 : Finset ℕ := ([40,72,136,246,1590,1622,1686,1768,2614,2646,2710,2792,3126,3158,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10293 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10293 4 (fun x => (if x<2614 then (if x<1590 then (if x<136 then (if x<72 then 0 else 1) else (if x<246 then 2 else 3)) else (if x<1686 then (if x<1622 then 1 else 0) else (if x<1768 then 3 else 2))) else (if x<3126 then (if x<2710 then (if x<2646 then 2 else 3) else (if x<2792 then 0 else 1)) else (if x<3222 then (if x<3158 then 3 else 2) else (if x<3304 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10294 : Finset ℕ := ([12,18,40,72,136,246,1590,1622,1644,1650,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2710,2732,2738,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10294 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10294 12 4
  · have he : independentCachedBranchMembers10294.erase 12=independentCachedBranchMembers10292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10292
  · have he : independentCachedBranchMembers10294.filter (independentCachedEdge 12)=independentCachedBranchMembers10293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10293
def independentCachedBranchMembers10295 : Finset ℕ := ([10,12,18,20,40,48,72,80,136,144,238,246,1582,1590,1614,1622,1642,1644,1650,1652,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10295 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10295 10 5
  · have he : independentCachedBranchMembers10295.erase 10=independentCachedBranchMembers10267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10267
  · have he : independentCachedBranchMembers10295.filter (independentCachedEdge 10)=independentCachedBranchMembers10294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10294
def independentCachedBranchMembers10296 : Finset ℕ := ([10,12,18,20,24,34,36,40,48,66,68,72,80,96,126,130,132,136,144,160,190,192,222,238,246,250,252,1536,1566,1582,1590,1594,1596,1614,1622,1626,1628,1638,1642,1644,1650,1652,1656,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10296 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10296 24 6
  · have he : independentCachedBranchMembers10296.erase 24=independentCachedBranchMembers9936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9936
  · have he : independentCachedBranchMembers10296.filter (independentCachedEdge 24)=independentCachedBranchMembers10295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10295
def independentCachedBranchMembers10297 : Finset ℕ := ([12,18,36,66,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2770,2788,3130,3164,3180,3186,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10297 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10297 6 (fun x => (if x<2666 then (if x<1692 then (if x<1596 then (if x<36 then (if x<18 then 0 else 0) else (if x<66 then 1 else 1)) else (if x<1644 then (if x<1626 then 1 else 1) else (if x<1650 then 0 else 0))) else (if x<1748 then (if x<1714 then (if x<1708 then 2 else 3) else (if x<1738 then 2 else 2)) else (if x<2620 then (if x<1764 then 3 else 2) else (if x<2650 then 4 else 4)))) else (if x<3164 then (if x<2738 then (if x<2716 then (if x<2676 then 5 else 5) else (if x<2732 then 3 else 0)) else (if x<2788 then (if x<2770 then 0 else 1) else (if x<3130 then 3 else 4))) else (if x<3244 then (if x<3186 then (if x<3180 then 4 else 5) else (if x<3226 then 5 else 2)) else (if x<3276 then (if x<3252 then 1 else 2) else (if x<3282 then 0 else (if x<3298 then 0 else 2)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10298 : Finset ℕ := ([18,66,1626,1650,1714,1738,2650,2666,2738,2770,3130,3186,3226,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10298 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10298 5 (fun x => (if x<2666 then (if x<1650 then (if x<66 then 0 else (if x<1626 then 1 else 0)) else (if x<1738 then (if x<1714 then 1 else 0) else (if x<2650 then 1 else 1))) else (if x<3186 then (if x<2770 then (if x<2738 then 2 else 2) else (if x<3130 then 0 else 2)) else (if x<3282 then (if x<3226 then 0 else 0) else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10299 : Finset ℕ := ([12,18,36,66,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2770,2788,3130,3164,3180,3186,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10299 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10299 252 5
  · have he : independentCachedBranchMembers10299.erase 252=independentCachedBranchMembers10297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10297
  · have he : independentCachedBranchMembers10299.filter (independentCachedEdge 252)=independentCachedBranchMembers10298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10298
def independentCachedBranchMembers10300 : Finset ℕ := ([12,36,1596,1644,1714,1738,2620,2676,2738,2770,3164,3180,3226,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10300 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10300 5 (fun x => (if x<2676 then (if x<1644 then (if x<36 then 0 else (if x<1596 then 1 else 0)) else (if x<1738 then (if x<1714 then 1 else 0) else (if x<2620 then 1 else 1))) else (if x<3180 then (if x<2770 then (if x<2738 then 2 else 2) else (if x<3164 then 0 else 2)) else (if x<3282 then (if x<3226 then 0 else 2) else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10301 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2770,2788,3130,3164,3180,3186,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10301 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10301 132 5
  · have he : independentCachedBranchMembers10301.erase 132=independentCachedBranchMembers10299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10299
  · have he : independentCachedBranchMembers10301.filter (independentCachedEdge 132)=independentCachedBranchMembers10300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10300
def independentCachedBranchMembers10302 : Finset ℕ := ([12,18,66,132,1626,1692,1708,1714,2650,2666,2676,2716,2732,2738,2770,3164,3180,3186,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10302 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10302 5 (fun x => (if x<2676 then (if x<1692 then (if x<66 then (if x<18 then 0 else 0) else (if x<132 then 1 else (if x<1626 then 1 else 1))) else (if x<1714 then (if x<1708 then 1 else 0) else (if x<2650 then 0 else (if x<2666 then 2 else 1)))) else (if x<3164 then (if x<2732 then (if x<2716 then 2 else 2) else (if x<2738 then 1 else (if x<2770 then 2 else 0))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3226 then 0 else (if x<3252 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10303 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2770,2788,3130,3164,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10303 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10303 3188 5
  · have he : independentCachedBranchMembers10303.erase 3188=independentCachedBranchMembers10301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10301
  · have he : independentCachedBranchMembers10303.filter (independentCachedEdge 3188)=independentCachedBranchMembers10302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10302
end EntropyDesigns.QuadraticRefinement
