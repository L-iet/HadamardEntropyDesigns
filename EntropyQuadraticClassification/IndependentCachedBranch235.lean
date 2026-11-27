/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch234
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10304 : Finset ℕ := ([12,18,36,252,1596,1708,1714,1764,2620,2666,2676,2732,2738,2770,2788,3130,3180,3186,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10304 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10304 5 (fun x => (if x<2676 then (if x<1708 then (if x<36 then (if x<18 then 0 else 0) else (if x<252 then 1 else (if x<1596 then 1 else 1))) else (if x<1764 then (if x<1714 then 0 else 0) else (if x<2620 then 1 else (if x<2666 then 2 else 2)))) else (if x<3130 then (if x<2738 then (if x<2732 then 1 else 1) else (if x<2770 then 2 else (if x<2788 then 0 else 2))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3252 then 0 else (if x<3298 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10305 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2716,2732,2738,2770,2788,3130,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10305 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10305 3178 5
  · have he : independentCachedBranchMembers10305.erase 3178=independentCachedBranchMembers10303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10303
  · have he : independentCachedBranchMembers10305.filter (independentCachedEdge 3178)=independentCachedBranchMembers10304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10304
def independentCachedBranchMembers10306 : Finset ℕ := ([36,252,1596,1644,1650,1738,1748,1764,2650,2666,2676,2716,2732,2738,2770,3164,3180,3186,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10306 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10306 5 (fun x => (if x<2676 then (if x<1738 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<1764 then (if x<1748 then 1 else 1) else (if x<2650 then 0 else (if x<2666 then 2 else 1)))) else (if x<3164 then (if x<2732 then (if x<2716 then 0 else 2) else (if x<2738 then 0 else (if x<2770 then 2 else 1))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3226 then 2 else (if x<3252 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10307 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2674,2676,2716,2732,2738,2770,2788,3130,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10307 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10307 2674 5
  · have he : independentCachedBranchMembers10307.erase 2674=independentCachedBranchMembers10305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10305
  · have he : independentCachedBranchMembers10307.filter (independentCachedEdge 2674)=independentCachedBranchMembers10306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10306
def independentCachedBranchMembers10308 : Finset ℕ := ([66,132,1626,1644,1650,1692,1738,1748,2620,2666,2676,2732,2738,2770,2788,3130,3180,3186,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10308 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10308 5 (fun x => (if x<2676 then (if x<1692 then (if x<1626 then (if x<132 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<2620 then 1 else (if x<2666 then 2 else 0)))) else (if x<3130 then (if x<2738 then (if x<2732 then 1 else 0) else (if x<2770 then 2 else (if x<2788 then 1 else 2))) else (if x<3186 then (if x<3180 then 2 else 2) else (if x<3252 then 0 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10309 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2668,2674,2676,2716,2732,2738,2770,2788,3130,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10309 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10309 2668 5
  · have he : independentCachedBranchMembers10309.erase 2668=independentCachedBranchMembers10307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10307
  · have he : independentCachedBranchMembers10309.filter (independentCachedEdge 2668)=independentCachedBranchMembers10308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10308
def independentCachedBranchMembers10310 : Finset ℕ := ([12,252,1596,1626,1644,1692,1714,1748,2620,2650,2668,2676,2716,2738,3130,3164,3178,3186,3226,3244,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10310 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10310 5 (fun x => (if x<2676 then (if x<1692 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1626 then 0 else (if x<1644 then 1 else 1))) else (if x<2620 then (if x<1714 then 1 else (if x<1748 then 2 else 2)) else (if x<2650 then 3 else (if x<2668 then 3 else 0)))) else (if x<3178 then (if x<2738 then (if x<2716 then 4 else 0) else (if x<3130 then 3 else (if x<3164 then 2 else 0))) else (if x<3244 then (if x<3186 then 1 else (if x<3226 then 4 else 1)) else (if x<3252 then 0 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10311 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2668,2674,2676,2716,2732,2738,2770,2788,3130,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10311 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10311 3162 5
  · have he : independentCachedBranchMembers10311.erase 3162=independentCachedBranchMembers10309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10309
  · have he : independentCachedBranchMembers10311.filter (independentCachedEdge 3162)=independentCachedBranchMembers10310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10310
def independentCachedBranchMembers10312 : Finset ℕ := ([18,132,1596,1626,1650,1714,1748,1764,2620,2650,2666,2674,2738,2788,3130,3164,3180,3188,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10312 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10312 5 (fun x => (if x<2674 then (if x<1714 then (if x<1596 then (if x<132 then 0 else 0) else (if x<1626 then 1 else (if x<1650 then 0 else 1))) else (if x<2620 then (if x<1748 then 2 else (if x<1764 then 1 else 2)) else (if x<2650 then 3 else (if x<2666 then 3 else 4)))) else (if x<3180 then (if x<2788 then (if x<2738 then 0 else 3) else (if x<3130 then 0 else (if x<3164 then 0 else 3))) else (if x<3252 then (if x<3188 then 2 else (if x<3244 then 1 else 0)) else (if x<3282 then 2 else (if x<3298 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10313 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2668,2674,2676,2716,2732,2738,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10313 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10313 3132 5
  · have he : independentCachedBranchMembers10313.erase 3132=independentCachedBranchMembers10311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10311
  · have he : independentCachedBranchMembers10313.filter (independentCachedEdge 3132)=independentCachedBranchMembers10312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10312
def independentCachedBranchMembers10314 : Finset ℕ := ([12,18,132,252,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2770,3130,3164,3180,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10314 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10314 5 (fun x => (if x<1764 then (if x<1650 then (if x<132 then (if x<18 then 0 else 0) else (if x<252 then 1 else (if x<1644 then 1 else 0))) else (if x<1714 then (if x<1692 then 0 else (if x<1708 then 1 else 2)) else (if x<1738 then 2 else (if x<1748 then 2 else 2)))) else (if x<2770 then (if x<2650 then (if x<2620 then 1 else 3) else (if x<2666 then 3 else (if x<2676 then 4 else 4))) else (if x<3180 then (if x<3130 then 0 else (if x<3164 then 3 else 3)) else (if x<3186 then 4 else (if x<3244 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10315 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10315 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10315 2762 5
  · have he : independentCachedBranchMembers10315.erase 2762=independentCachedBranchMembers10313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10313
  · have he : independentCachedBranchMembers10315.filter (independentCachedEdge 2762)=independentCachedBranchMembers10314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10314
def independentCachedBranchMembers10316 : Finset ℕ := ([18,36,66,132,1650,1708,1738,1764,2620,2650,2668,2676,2716,2738,3130,3164,3178,3186,3226,3244,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10316 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10316 5 (fun x => (if x<2676 then (if x<1708 then (if x<66 then (if x<36 then 0 else 0) else (if x<132 then 1 else (if x<1650 then 1 else 1))) else (if x<2620 then (if x<1738 then 0 else (if x<1764 then 2 else 2)) else (if x<2650 then 3 else (if x<2668 then 0 else 0)))) else (if x<3178 then (if x<2738 then (if x<2716 then 2 else 1) else (if x<3130 then 3 else (if x<3164 then 3 else 3))) else (if x<3244 then (if x<3186 then 1 else (if x<3226 then 4 else 2)) else (if x<3252 then 1 else (if x<3282 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10317 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10317 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10317 2652 5
  · have he : independentCachedBranchMembers10317.erase 2652=independentCachedBranchMembers10315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10315
  · have he : independentCachedBranchMembers10317.filter (independentCachedEdge 2652)=independentCachedBranchMembers10316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10316
def independentCachedBranchMembers10318 : Finset ℕ := ([12,36,66,252,1644,1692,1708,1738,2620,2650,2666,2674,2738,2788,3130,3164,3180,3188,3244,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10318 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10318 5 (fun x => (if x<2674 then (if x<1692 then (if x<66 then (if x<36 then 0 else 1) else (if x<252 then 0 else (if x<1644 then 1 else 1))) else (if x<2620 then (if x<1708 then 0 else (if x<1738 then 2 else 2)) else (if x<2650 then 0 else (if x<2666 then 2 else 3)))) else (if x<3180 then (if x<2788 then (if x<2738 then 0 else 3) else (if x<3130 then 1 else (if x<3164 then 3 else 4))) else (if x<3252 then (if x<3188 then 3 else (if x<3244 then 1 else 0)) else (if x<3282 then 2 else (if x<3298 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10319 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1748,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10319 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10319 2618 5
  · have he : independentCachedBranchMembers10319.erase 2618=independentCachedBranchMembers10317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10317
  · have he : independentCachedBranchMembers10319.filter (independentCachedEdge 2618)=independentCachedBranchMembers10318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10318
def independentCachedBranchMembers10320 : Finset ℕ := ([132,252,1596,1626,1644,1650,1708,1714,1738,1748,2618,2652,2666,2676,2716,2770,2788,3130,3164,3178,3188,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10320 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10320 5 (fun x => (if x<2666 then (if x<1708 then (if x<1626 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1748 then (if x<1714 then 0 else (if x<1738 then 1 else 2)) else (if x<2618 then 0 else (if x<2652 then 1 else 1)))) else (if x<3164 then (if x<2770 then (if x<2676 then 2 else (if x<2716 then 2 else 0)) else (if x<2788 then 1 else (if x<3130 then 0 else 3))) else (if x<3252 then (if x<3178 then 3 else (if x<3188 then 4 else 4)) else (if x<3276 then 0 else (if x<3282 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10321 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1746,1748,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10321 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10321 1746 5
  · have he : independentCachedBranchMembers10321.erase 1746=independentCachedBranchMembers10319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10319
  · have he : independentCachedBranchMembers10321.filter (independentCachedEdge 1746)=independentCachedBranchMembers10320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10320
def independentCachedBranchMembers10322 : Finset ℕ := ([36,66,1644,1650,1692,1708,1714,1738,1748,1764,2620,2650,2666,2676,2770,3132,3162,3178,3188,3226,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10322 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10322 5 (fun x => (if x<2666 then (if x<1714 then (if x<1650 then (if x<66 then 0 else (if x<1644 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 2 else 0))) else (if x<1764 then (if x<1738 then 2 else (if x<1748 then 0 else 1)) else (if x<2620 then 2 else (if x<2650 then 0 else 0)))) else (if x<3188 then (if x<3132 then (if x<2676 then 1 else (if x<2770 then 1 else 1)) else (if x<3162 then 3 else (if x<3178 then 3 else 4))) else (if x<3276 then (if x<3226 then 4 else (if x<3252 then 2 else 0)) else (if x<3282 then 2 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10323 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1738,1740,1746,1748,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10323 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10323 1740 5
  · have he : independentCachedBranchMembers10323.erase 1740=independentCachedBranchMembers10321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10321
  · have he : independentCachedBranchMembers10323.filter (independentCachedEdge 1740)=independentCachedBranchMembers10322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10322
def independentCachedBranchMembers10324 : Finset ℕ := ([12,18,1596,1626,1692,1708,1714,1738,1748,1764,2618,2652,2668,2674,2770,3130,3164,3180,3186,3226,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10324 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10324 5 (fun x => (if x<2668 then (if x<1714 then (if x<1626 then (if x<18 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 2 else 0))) else (if x<1764 then (if x<1738 then 0 else (if x<1748 then 2 else 1)) else (if x<2618 then 2 else (if x<2652 then 1 else 1)))) else (if x<3186 then (if x<3130 then (if x<2674 then 0 else (if x<2770 then 0 else 1)) else (if x<3164 then 3 else (if x<3180 then 3 else 4))) else (if x<3276 then (if x<3226 then 4 else (if x<3252 then 2 else 2)) else (if x<3282 then 0 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10325 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1708,1714,1716,1738,1740,1746,1748,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10325 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10325 1716 5
  · have he : independentCachedBranchMembers10325.erase 1716=independentCachedBranchMembers10323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10323
  · have he : independentCachedBranchMembers10325.filter (independentCachedEdge 1716)=independentCachedBranchMembers10324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10324
def independentCachedBranchMembers10326 : Finset ℕ := ([12,18,36,66,132,252,1708,1714,1738,1748,2620,2650,2668,2674,2716,2770,2788,3132,3162,3180,3186,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10326 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10326 5 (fun x => (if x<2668 then (if x<1708 then (if x<66 then (if x<18 then 0 else (if x<36 then 0 else 1)) else (if x<132 then 1 else (if x<252 then 2 else 2))) else (if x<1748 then (if x<1714 then 0 else (if x<1738 then 0 else 1)) else (if x<2620 then 2 else (if x<2650 then 1 else 1)))) else (if x<3162 then (if x<2770 then (if x<2674 then 0 else (if x<2716 then 0 else 2)) else (if x<2788 then 3 else (if x<3132 then 2 else 3))) else (if x<3252 then (if x<3180 then 3 else (if x<3186 then 4 else 4)) else (if x<3276 then 1 else (if x<3282 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10327 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1706,1708,1714,1716,1738,1740,1746,1748,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10327 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10327 1706 5
  · have he : independentCachedBranchMembers10327.erase 1706=independentCachedBranchMembers10325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10325
  · have he : independentCachedBranchMembers10327.filter (independentCachedEdge 1706)=independentCachedBranchMembers10326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10326
def independentCachedBranchMembers10328 : Finset ℕ := ([18,36,1596,1650,1692,1706,1714,1738,1746,1764,2618,2650,2668,2676,2732,3130,3162,3180,3188,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10328 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10328 5 (fun x => (if x<2668 then (if x<1714 then (if x<1650 then (if x<36 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1706 then 2 else 1))) else (if x<1764 then (if x<1738 then 2 else (if x<1746 then 2 else 0)) else (if x<2618 then 0 else (if x<2650 then 1 else 0)))) else (if x<3188 then (if x<3130 then (if x<2676 then 0 else (if x<2732 then 1 else 1)) else (if x<3162 then 3 else (if x<3180 then 4 else 3))) else (if x<3252 then (if x<3226 then 4 else (if x<3244 then 0 else 0)) else (if x<3276 then 2 else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10329 : Finset ℕ := ([18,1650,1706,1714,1738,1746,2618,2650,3130,3162,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10329 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10329 4 (fun x => (if x<2618 then (if x<1714 then (if x<1650 then 0 else (if x<1706 then 0 else 1)) else (if x<1738 then 2 else (if x<1746 then 2 else 1))) else (if x<3162 then (if x<2650 then 0 else (if x<3130 then 3 else 3)) else (if x<3226 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10330 : Finset ℕ := ([18,36,252,1596,1650,1692,1706,1714,1738,1746,1764,2618,2650,2668,2676,2732,3130,3162,3180,3188,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10330 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10330 252 4
  · have he : independentCachedBranchMembers10330.erase 252=independentCachedBranchMembers10328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10328
  · have he : independentCachedBranchMembers10330.filter (independentCachedEdge 252)=independentCachedBranchMembers10329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10329
def independentCachedBranchMembers10331 : Finset ℕ := ([36,1596,1706,1714,1738,1746,2668,2676,3180,3188,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10331 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10331 4 (fun x => (if x<2668 then (if x<1714 then (if x<1596 then 0 else (if x<1706 then 0 else 1)) else (if x<1738 then 2 else (if x<1746 then 2 else 1))) else (if x<3188 then (if x<2676 then 0 else (if x<3180 then 3 else 3)) else (if x<3226 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10332 : Finset ℕ := ([18,36,132,252,1596,1650,1692,1706,1714,1738,1746,1764,2618,2650,2668,2676,2732,3130,3162,3180,3188,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10332 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10332 132 4
  · have he : independentCachedBranchMembers10332.erase 132=independentCachedBranchMembers10330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10330
  · have he : independentCachedBranchMembers10332.filter (independentCachedEdge 132)=independentCachedBranchMembers10331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10331
def independentCachedBranchMembers10333 : Finset ℕ := ([12,18,36,66,132,252,1596,1626,1644,1650,1692,1706,1708,1714,1716,1738,1740,1746,1748,1762,1764,2618,2620,2650,2652,2666,2668,2674,2676,2716,2732,2738,2762,2770,2788,3130,3132,3162,3164,3178,3180,3186,3188,3226,3244,3252,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10333 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10333 1762 5
  · have he : independentCachedBranchMembers10333.erase 1762=independentCachedBranchMembers10327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10327
  · have he : independentCachedBranchMembers10333.filter (independentCachedEdge 1762)=independentCachedBranchMembers10332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10332
def independentCachedBranchMembers10334 : Finset ℕ := ([12,66,1626,1644,1692,1706,1714,1738,1746,1764,2620,2652,2666,2674,2732,3132,3164,3178,3186,3226,3244,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10334 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10334 5 (fun x => (if x<2666 then (if x<1714 then (if x<1644 then (if x<66 then 0 else (if x<1626 then 0 else 1)) else (if x<1692 then 1 else (if x<1706 then 0 else 1))) else (if x<1764 then (if x<1738 then 2 else (if x<1746 then 2 else 0)) else (if x<2620 then 2 else (if x<2652 then 0 else 1)))) else (if x<3186 then (if x<3132 then (if x<2674 then 1 else (if x<2732 then 0 else 1)) else (if x<3164 then 3 else (if x<3178 then 4 else 3))) else (if x<3252 then (if x<3226 then 4 else (if x<3244 then 2 else 0)) else (if x<3276 then 2 else (if x<3298 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10335 : Finset ℕ := ([66,1626,1706,1714,1738,1746,2666,2674,3178,3186,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10335 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10335 4 (fun x => (if x<2666 then (if x<1714 then (if x<1626 then 0 else (if x<1706 then 0 else 1)) else (if x<1738 then 2 else (if x<1746 then 2 else 1))) else (if x<3186 then (if x<2674 then 0 else (if x<3178 then 3 else 3)) else (if x<3226 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
