/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch142
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7360 : Finset ℕ := ([12,40,252,1596,1644,1708,1720,1740,1752,1768,2620,2652,2668,2680,2716,2732,2792,3132,3164,3180,3192,3244,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7360 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7360 1768 4
  · have he : independentCachedBranchMembers7360.erase 1768=independentCachedBranchMembers7358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7358
  · have he : independentCachedBranchMembers7360.filter (independentCachedEdge 1768)=independentCachedBranchMembers7359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7359
def independentCachedBranchMembers7361 : Finset ℕ := ([40,1596,1708,1720,1740,1752,2668,2680,2716,2792,3180,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7361 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7361 4 (fun x => (if x<2668 then (if x<1720 then (if x<1596 then 0 else (if x<1708 then 0 else 1)) else (if x<1740 then 2 else (if x<1752 then 2 else 1))) else (if x<2792 then (if x<2680 then 0 else (if x<2716 then 3 else 1)) else (if x<3180 then 1 else (if x<3192 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7362 : Finset ℕ := ([12,40,252,1596,1644,1692,1708,1720,1740,1752,1768,2620,2652,2668,2680,2716,2732,2792,3132,3164,3180,3192,3244,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7362 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7362 1692 4
  · have he : independentCachedBranchMembers7362.erase 1692=independentCachedBranchMembers7360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7360
  · have he : independentCachedBranchMembers7362.filter (independentCachedEdge 1692)=independentCachedBranchMembers7361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7361
def independentCachedBranchMembers7363 : Finset ℕ := ([12,40,1596,1644,2620,2652,2668,2680,3132,3164,3180,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7363 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7363 4 (fun x => (if x<2668 then (if x<1644 then (if x<40 then 0 else (if x<1596 then 1 else 0)) else (if x<2620 then 1 else (if x<2652 then 1 else 0))) else (if x<3164 then (if x<2680 then 2 else (if x<3132 then 3 else 2)) else (if x<3180 then 3 else (if x<3192 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7364 : Finset ℕ := ([12,40,136,252,1596,1644,1692,1708,1720,1740,1752,1768,2620,2652,2668,2680,2716,2732,2792,3132,3164,3180,3192,3244,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7364 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7364 136 4
  · have he : independentCachedBranchMembers7364.erase 136=independentCachedBranchMembers7362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7362
  · have he : independentCachedBranchMembers7364.filter (independentCachedEdge 136)=independentCachedBranchMembers7363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7363
def independentCachedBranchMembers7365 : Finset ℕ := ([12,18,40,66,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7365 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7365 246 5
  · have he : independentCachedBranchMembers7365.erase 246=independentCachedBranchMembers7357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7357
  · have he : independentCachedBranchMembers7365.filter (independentCachedEdge 246)=independentCachedBranchMembers7364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7364
def independentCachedBranchMembers7366 : Finset ℕ := ([18,66,136,1622,1650,1708,1720,1740,1752,2614,2646,2662,2674,2716,2732,2792,3126,3158,3174,3186,3244,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7366 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7366 5 (fun x => (if x<2662 then (if x<1708 then (if x<136 then (if x<66 then 0 else 1) else (if x<1622 then 0 else (if x<1650 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1740 then 1 else 0)) else (if x<2614 then 2 else (if x<2646 then 0 else 1)))) else (if x<3158 then (if x<2732 then (if x<2674 then 3 else (if x<2716 then 4 else 1)) else (if x<2792 then 0 else (if x<3126 then 2 else 3))) else (if x<3244 then (if x<3174 then 4 else (if x<3186 then 1 else 0)) else (if x<3256 then 1 else (if x<3276 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7367 : Finset ℕ := ([66,1622,1708,1720,1740,1752,2662,2674,2716,2792,3174,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7367 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7367 4 (fun x => (if x<2662 then (if x<1720 then (if x<1622 then 0 else (if x<1708 then 0 else 1)) else (if x<1740 then 2 else (if x<1752 then 2 else 1))) else (if x<2792 then (if x<2674 then 0 else (if x<2716 then 3 else 1)) else (if x<3174 then 1 else (if x<3186 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7368 : Finset ℕ := ([18,66,136,1622,1650,1708,1720,1740,1752,1768,2614,2646,2662,2674,2716,2732,2792,3126,3158,3174,3186,3244,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7368 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7368 1768 4
  · have he : independentCachedBranchMembers7368.erase 1768=independentCachedBranchMembers7366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7366
  · have he : independentCachedBranchMembers7368.filter (independentCachedEdge 1768)=independentCachedBranchMembers7367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7367
def independentCachedBranchMembers7369 : Finset ℕ := ([18,1650,1708,1720,1740,1752,2614,2646,2716,2792,3126,3158] : List ℕ).toFinset
theorem independentCachedBranchBound7369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7369 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7369 4 (fun x => (if x<2614 then (if x<1720 then (if x<1650 then 0 else (if x<1708 then 0 else 1)) else (if x<1740 then 2 else (if x<1752 then 2 else 1))) else (if x<2792 then (if x<2646 then 0 else (if x<2716 then 3 else 1)) else (if x<3126 then 1 else (if x<3158 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7370 : Finset ℕ := ([18,66,136,1622,1650,1692,1708,1720,1740,1752,1768,2614,2646,2662,2674,2716,2732,2792,3126,3158,3174,3186,3244,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7370 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7370 1692 4
  · have he : independentCachedBranchMembers7370.erase 1692=independentCachedBranchMembers7368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7368
  · have he : independentCachedBranchMembers7370.filter (independentCachedEdge 1692)=independentCachedBranchMembers7369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7369
def independentCachedBranchMembers7371 : Finset ℕ := ([18,66,1622,1650,2614,2646,2662,2674,3126,3158,3174,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7371 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7371 4 (fun x => (if x<2662 then (if x<1650 then (if x<66 then 0 else (if x<1622 then 1 else 0)) else (if x<2614 then 1 else (if x<2646 then 0 else 1))) else (if x<3158 then (if x<2674 then 2 else (if x<3126 then 3 else 2)) else (if x<3174 then 3 else (if x<3186 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7372 : Finset ℕ := ([18,66,136,252,1622,1650,1692,1708,1720,1740,1752,1768,2614,2646,2662,2674,2716,2732,2792,3126,3158,3174,3186,3244,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7372 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7372 252 4
  · have he : independentCachedBranchMembers7372.erase 252=independentCachedBranchMembers7370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7370
  · have he : independentCachedBranchMembers7372.filter (independentCachedEdge 252)=independentCachedBranchMembers7371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7371
def independentCachedBranchMembers7373 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7373 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7373 130 5
  · have he : independentCachedBranchMembers7373.erase 130=independentCachedBranchMembers7365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7365
  · have he : independentCachedBranchMembers7373.filter (independentCachedEdge 130)=independentCachedBranchMembers7372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7372
def independentCachedBranchMembers7374 : Finset ℕ := ([12,66,130,246,1596,1650,1692,1702,1714,1734,1746,1768,2620,2652,2662,2674,2716,2738,2758,2770,2792,3126,3158,3180,3192,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7374 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7374 5 (fun x => (if x<2674 then (if x<1702 then (if x<246 then (if x<66 then 0 else (if x<130 then 0 else 1)) else (if x<1650 then (if x<1596 then 1 else 0) else (if x<1692 then 0 else 2))) else (if x<1768 then (if x<1734 then (if x<1714 then 1 else 2) else (if x<1746 then 2 else 1)) else (if x<2652 then (if x<2620 then 2 else 3) else (if x<2662 then 4 else 3)))) else (if x<3158 then (if x<2758 then (if x<2716 then 4 else (if x<2738 then 0 else 1)) else (if x<2792 then (if x<2770 then 1 else 0) else (if x<3126 then 3 else 3))) else (if x<3244 then (if x<3192 then (if x<3180 then 4 else 3) else (if x<3222 then 4 else 1)) else (if x<3276 then (if x<3256 then 0 else 2) else (if x<3298 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7375 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7375 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7375 3304 5
  · have he : independentCachedBranchMembers7375.erase 3304=independentCachedBranchMembers7373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7373
  · have he : independentCachedBranchMembers7375.filter (independentCachedEdge 3304)=independentCachedBranchMembers7374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7374
def independentCachedBranchMembers7376 : Finset ℕ := ([18,40,66,136,252,1596,1622,1644,1650,1692,1702,1720,1740,1746,1768,2620,2646,2668,2674,2716,2792,3126,3164,3174,3192,3222,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7376 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7376 5 (fun x => (if x<1768 then (if x<1644 then (if x<136 then (if x<40 then 0 else (if x<66 then 0 else 1)) else (if x<1596 then (if x<252 then 1 else 2) else (if x<1622 then 2 else 0))) else (if x<1702 then (if x<1650 then 0 else (if x<1692 then 1 else 3)) else (if x<1740 then (if x<1720 then 3 else 1) else (if x<1746 then 2 else 3)))) else (if x<3126 then (if x<2668 then (if x<2620 then 3 else (if x<2646 then 4 else 1)) else (if x<2716 then (if x<2674 then 2 else 4) else (if x<2792 then 1 else 0))) else (if x<3192 then (if x<3164 then 4 else (if x<3174 then 2 else 1)) else (if x<3244 then (if x<3222 then 4 else 0) else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7377 : Finset ℕ := ([40,136,1622,1702,1720,1768,2646,2792,3126,3174,3192,3222] : List ℕ).toFinset
theorem independentCachedBranchBound7377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7377 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7377 4 (fun x => (if x<2646 then (if x<1702 then (if x<136 then 0 else (if x<1622 then 1 else 0)) else (if x<1720 then 2 else (if x<1768 then 1 else 2))) else (if x<3174 then (if x<2792 then 1 else (if x<3126 then 0 else 2)) else (if x<3192 then 1 else (if x<3222 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7378 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1702,1720,1740,1746,1768,2620,2646,2668,2674,2716,2792,3126,3164,3174,3192,3222,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7378 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7378 12 4
  · have he : independentCachedBranchMembers7378.erase 12=independentCachedBranchMembers7376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7376
  · have he : independentCachedBranchMembers7378.filter (independentCachedEdge 12)=independentCachedBranchMembers7377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7377
def independentCachedBranchMembers7379 : Finset ℕ := ([136,252,1692,1702,1720,1740,1746,1768,2620,2646,2668,2674,3126,3164,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7379 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7379 4 (fun x => (if x<2620 then (if x<1720 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3126 then (if x<2668 then (if x<2646 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3174 then (if x<3164 then 2 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7380 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1702,1720,1740,1746,1768,2620,2646,2668,2674,2716,2770,2792,3126,3164,3174,3192,3222,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7380 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7380 2770 4
  · have he : independentCachedBranchMembers7380.erase 2770=independentCachedBranchMembers7378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7378
  · have he : independentCachedBranchMembers7380.filter (independentCachedEdge 2770)=independentCachedBranchMembers7379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7379
def independentCachedBranchMembers7381 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3238,3244,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7381 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7381 3238 5
  · have he : independentCachedBranchMembers7381.erase 3238=independentCachedBranchMembers7375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7375
  · have he : independentCachedBranchMembers7381.filter (independentCachedEdge 3238)=independentCachedBranchMembers7380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7380
def independentCachedBranchMembers7382 : Finset ℕ := ([18,40,130,246,1622,1644,1692,1702,1714,1734,1746,1768,2614,2646,2668,2680,2716,2738,2758,2770,2792,3132,3164,3174,3186,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7382 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7382 5 (fun x => (if x<2680 then (if x<1702 then (if x<246 then (if x<40 then 0 else (if x<130 then 0 else 1)) else (if x<1644 then (if x<1622 then 1 else 0) else (if x<1692 then 0 else 2))) else (if x<1768 then (if x<1734 then (if x<1714 then 1 else 2) else (if x<1746 then 2 else 1)) else (if x<2646 then (if x<2614 then 2 else 3) else (if x<2668 then 4 else 3)))) else (if x<3164 then (if x<2758 then (if x<2716 then 4 else (if x<2738 then 3 else 1)) else (if x<2792 then (if x<2770 then 1 else 0) else (if x<3132 then 0 else 3))) else (if x<3244 then (if x<3186 then (if x<3174 then 4 else 3) else (if x<3222 then 4 else 0)) else (if x<3276 then (if x<3256 then 0 else 2) else (if x<3298 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7383 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7383 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7383 3228 5
  · have he : independentCachedBranchMembers7383.erase 3228=independentCachedBranchMembers7381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7381
  · have he : independentCachedBranchMembers7383.filter (independentCachedEdge 3228)=independentCachedBranchMembers7382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7382
def independentCachedBranchMembers7384 : Finset ℕ := ([18,40,136,252,1622,1644,1686,1708,1720,1740,1752,1762,2620,2652,2662,2674,2716,2738,2758,2770,2792,3126,3158,3180,3192,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7384 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7384 5 (fun x => (if x<2674 then (if x<1708 then (if x<252 then (if x<40 then 0 else (if x<136 then 0 else 1)) else (if x<1644 then (if x<1622 then 1 else 0) else (if x<1686 then 0 else 2))) else (if x<1762 then (if x<1740 then (if x<1720 then 1 else 2) else (if x<1752 then 2 else 1)) else (if x<2652 then (if x<2620 then 2 else 3) else (if x<2662 then 4 else 3)))) else (if x<3158 then (if x<2758 then (if x<2716 then 4 else (if x<2738 then 1 else 2)) else (if x<2792 then (if x<2770 then 2 else 0) else (if x<3126 then 0 else 3))) else (if x<3244 then (if x<3192 then (if x<3180 then 4 else 3) else (if x<3222 then 4 else 0)) else (if x<3276 then (if x<3256 then 0 else 1) else (if x<3298 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7385 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7385 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7385 2786 5
  · have he : independentCachedBranchMembers7385.erase 2786=independentCachedBranchMembers7383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7383
  · have he : independentCachedBranchMembers7385.filter (independentCachedEdge 2786)=independentCachedBranchMembers7384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7384
def independentCachedBranchMembers7386 : Finset ℕ := ([66,130,246,1596,1622,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2716,2770,2792,3132,3158,3180,3186,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7386 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7386 5 (fun x => (if x<2652 then (if x<1708 then (if x<1596 then (if x<130 then 0 else (if x<246 then 1 else 0)) else (if x<1622 then 1 else (if x<1686 then 0 else 1))) else (if x<1752 then (if x<1714 then 2 else (if x<1734 then 2 else 2)) else (if x<1762 then 2 else (if x<2614 then 0 else 3)))) else (if x<3132 then (if x<2716 then (if x<2662 then 3 else (if x<2680 then 0 else 1)) else (if x<2770 then 4 else (if x<2792 then 0 else 4))) else (if x<3186 then (if x<3158 then 3 else (if x<3180 then 3 else 1)) else (if x<3222 then 0 else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7387 : Finset ℕ := ([246,1714,1752,1762,2614,2652,2662,2716,3186,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7387 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7387 4 (fun x => (if x<2652 then (if x<1752 then (if x<1714 then 0 else 0) else (if x<1762 then 1 else (if x<2614 then 1 else 0))) else (if x<2716 then (if x<2662 then 1 else 1) else (if x<3186 then 2 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7388 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2716,2770,2792,3132,3158,3180,3186,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7388 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7388 40 4
  · have he : independentCachedBranchMembers7388.erase 40=independentCachedBranchMembers7386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7386
  · have he : independentCachedBranchMembers7388.filter (independentCachedEdge 40)=independentCachedBranchMembers7387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7387
def independentCachedBranchMembers7389 : Finset ℕ := ([40,130,1622,1708,1714,1762,2652,2792,3132,3180,3186,3222] : List ℕ).toFinset
theorem independentCachedBranchBound7389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7389 4 (fun x => (if x<2652 then (if x<1708 then (if x<130 then 0 else (if x<1622 then 0 else 1)) else (if x<1714 then 2 else (if x<1762 then 1 else 2))) else (if x<3180 then (if x<2792 then 1 else (if x<3132 then 2 else 0)) else (if x<3186 then 3 else (if x<3222 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7390 : Finset ℕ := ([40,66,130,246,1596,1622,1650,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2716,2770,2792,3132,3158,3180,3186,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7390 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7390 1650 4
  · have he : independentCachedBranchMembers7390.erase 1650=independentCachedBranchMembers7388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7388
  · have he : independentCachedBranchMembers7390.filter (independentCachedEdge 1650)=independentCachedBranchMembers7389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7389
def independentCachedBranchMembers7391 : Finset ℕ := ([66,246,1596,1686,1708,1714,2614,2716,3158,3180,3186,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7391 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7391 4 (fun x => (if x<2614 then (if x<1686 then (if x<246 then 0 else (if x<1596 then 0 else 1)) else (if x<1708 then 1 else (if x<1714 then 2 else 2))) else (if x<3180 then (if x<2716 then 1 else (if x<3158 then 1 else 0)) else (if x<3186 then 2 else (if x<3298 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
