/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch141
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7328 : Finset ℕ := ([12,252,1596,1622,1644,1692,1714,1752,2620,2646,2668,2680,2716,2738,3126,3164,3174,3186,3222,3244,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7328 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7328 5 (fun x => (if x<2680 then (if x<1692 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1622 then 0 else (if x<1644 then 1 else 1))) else (if x<2620 then (if x<1714 then 1 else (if x<1752 then 2 else 2)) else (if x<2646 then 3 else (if x<2668 then 3 else 0)))) else (if x<3174 then (if x<2738 then (if x<2716 then 4 else 0) else (if x<3126 then 3 else (if x<3164 then 2 else 0))) else (if x<3244 then (if x<3186 then 1 else (if x<3222 then 4 else 1)) else (if x<3256 then 0 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7329 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2668,2674,2680,2716,2732,2738,2770,2792,3126,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7329 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7329 3158 5
  · have he : independentCachedBranchMembers7329.erase 3158=independentCachedBranchMembers7327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7327
  · have he : independentCachedBranchMembers7329.filter (independentCachedEdge 3158)=independentCachedBranchMembers7328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7328
def independentCachedBranchMembers7330 : Finset ℕ := ([18,136,1596,1622,1650,1714,1752,1768,2620,2646,2662,2674,2738,2792,3126,3164,3180,3192,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7330 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7330 5 (fun x => (if x<2674 then (if x<1714 then (if x<1596 then (if x<136 then 0 else 0) else (if x<1622 then 1 else (if x<1650 then 0 else 1))) else (if x<2620 then (if x<1752 then 2 else (if x<1768 then 1 else 2)) else (if x<2646 then 3 else (if x<2662 then 3 else 4)))) else (if x<3180 then (if x<2792 then (if x<2738 then 0 else 3) else (if x<3126 then 0 else (if x<3164 then 0 else 3))) else (if x<3256 then (if x<3192 then 2 else (if x<3244 then 1 else 0)) else (if x<3282 then 2 else (if x<3298 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7331 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2668,2674,2680,2716,2732,2738,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7331 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7331 3132 5
  · have he : independentCachedBranchMembers7331.erase 3132=independentCachedBranchMembers7329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7329
  · have he : independentCachedBranchMembers7331.filter (independentCachedEdge 3132)=independentCachedBranchMembers7330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7330
def independentCachedBranchMembers7332 : Finset ℕ := ([12,18,136,252,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2770,3126,3164,3180,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound7332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7332 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7332 5 (fun x => (if x<1768 then (if x<1650 then (if x<136 then (if x<18 then 0 else 0) else (if x<252 then 1 else (if x<1644 then 1 else 0))) else (if x<1714 then (if x<1692 then 0 else (if x<1708 then 1 else 2)) else (if x<1734 then 2 else (if x<1752 then 2 else 2)))) else (if x<2770 then (if x<2646 then (if x<2620 then 1 else 3) else (if x<2662 then 3 else (if x<2680 then 4 else 4))) else (if x<3180 then (if x<3126 then 0 else (if x<3164 then 3 else 3)) else (if x<3186 then 4 else (if x<3244 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7333 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7333 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7333 2758 5
  · have he : independentCachedBranchMembers7333.erase 2758=independentCachedBranchMembers7331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7331
  · have he : independentCachedBranchMembers7333.filter (independentCachedEdge 2758)=independentCachedBranchMembers7332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7332
def independentCachedBranchMembers7334 : Finset ℕ := ([18,40,66,136,1650,1708,1734,1768,2620,2646,2668,2680,2716,2738,3126,3164,3174,3186,3222,3244,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7334 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7334 5 (fun x => (if x<2680 then (if x<1708 then (if x<66 then (if x<40 then 0 else 0) else (if x<136 then 1 else (if x<1650 then 1 else 1))) else (if x<2620 then (if x<1734 then 0 else (if x<1768 then 2 else 2)) else (if x<2646 then 3 else (if x<2668 then 0 else 0)))) else (if x<3174 then (if x<2738 then (if x<2716 then 2 else 1) else (if x<3126 then 3 else (if x<3164 then 3 else 3))) else (if x<3244 then (if x<3186 then 1 else (if x<3222 then 4 else 2)) else (if x<3256 then 1 else (if x<3282 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7335 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7335 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7335 2652 5
  · have he : independentCachedBranchMembers7335.erase 2652=independentCachedBranchMembers7333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7333
  · have he : independentCachedBranchMembers7335.filter (independentCachedEdge 2652)=independentCachedBranchMembers7334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7334
def independentCachedBranchMembers7336 : Finset ℕ := ([12,40,66,252,1644,1692,1708,1734,2620,2646,2662,2674,2738,2792,3126,3164,3180,3192,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7336 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7336 5 (fun x => (if x<2674 then (if x<1692 then (if x<66 then (if x<40 then 0 else 1) else (if x<252 then 0 else (if x<1644 then 1 else 1))) else (if x<2620 then (if x<1708 then 0 else (if x<1734 then 2 else 2)) else (if x<2646 then 0 else (if x<2662 then 2 else 3)))) else (if x<3180 then (if x<2792 then (if x<2738 then 0 else 3) else (if x<3126 then 1 else (if x<3164 then 3 else 4))) else (if x<3256 then (if x<3192 then 3 else (if x<3244 then 1 else 0)) else (if x<3282 then 2 else (if x<3298 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7337 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7337 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7337 2614 5
  · have he : independentCachedBranchMembers7337.erase 2614=independentCachedBranchMembers7335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7335
  · have he : independentCachedBranchMembers7337.filter (independentCachedEdge 2614)=independentCachedBranchMembers7336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7336
def independentCachedBranchMembers7338 : Finset ℕ := ([136,252,1596,1622,1644,1650,1708,1714,1734,1752,2614,2652,2662,2680,2716,2770,2792,3126,3164,3174,3192,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7338 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7338 5 (fun x => (if x<2662 then (if x<1708 then (if x<1622 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1752 then (if x<1714 then 0 else (if x<1734 then 1 else 2)) else (if x<2614 then 0 else (if x<2652 then 1 else 1)))) else (if x<3164 then (if x<2770 then (if x<2680 then 2 else (if x<2716 then 2 else 0)) else (if x<2792 then 1 else (if x<3126 then 0 else 3))) else (if x<3256 then (if x<3174 then 3 else (if x<3192 then 4 else 4)) else (if x<3276 then 0 else (if x<3282 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7339 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1746,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7339 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7339 1746 5
  · have he : independentCachedBranchMembers7339.erase 1746=independentCachedBranchMembers7337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7337
  · have he : independentCachedBranchMembers7339.filter (independentCachedEdge 1746)=independentCachedBranchMembers7338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7338
def independentCachedBranchMembers7340 : Finset ℕ := ([40,66,1644,1650,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2770,3132,3158,3174,3192,3222,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7340 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7340 5 (fun x => (if x<2662 then (if x<1714 then (if x<1650 then (if x<66 then 0 else (if x<1644 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 2 else 0))) else (if x<1768 then (if x<1734 then 2 else (if x<1752 then 0 else 1)) else (if x<2620 then 2 else (if x<2646 then 0 else 0)))) else (if x<3192 then (if x<3132 then (if x<2680 then 1 else (if x<2770 then 1 else 1)) else (if x<3158 then 3 else (if x<3174 then 3 else 4))) else (if x<3276 then (if x<3222 then 4 else (if x<3256 then 2 else 0)) else (if x<3282 then 2 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7341 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1734,1740,1746,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7341 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7341 1740 5
  · have he : independentCachedBranchMembers7341.erase 1740=independentCachedBranchMembers7339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7339
  · have he : independentCachedBranchMembers7341.filter (independentCachedEdge 1740)=independentCachedBranchMembers7340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7340
def independentCachedBranchMembers7342 : Finset ℕ := ([12,18,1596,1622,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2770,3126,3164,3180,3186,3222,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7342 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7342 5 (fun x => (if x<2668 then (if x<1714 then (if x<1622 then (if x<18 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 2 else 0))) else (if x<1768 then (if x<1734 then 0 else (if x<1752 then 2 else 1)) else (if x<2614 then 2 else (if x<2652 then 1 else 1)))) else (if x<3186 then (if x<3126 then (if x<2674 then 0 else (if x<2770 then 0 else 1)) else (if x<3164 then 3 else (if x<3180 then 3 else 4))) else (if x<3276 then (if x<3222 then 4 else (if x<3256 then 2 else 2)) else (if x<3282 then 0 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7343 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1708,1714,1720,1734,1740,1746,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7343 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7343 1720 5
  · have he : independentCachedBranchMembers7343.erase 1720=independentCachedBranchMembers7341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7341
  · have he : independentCachedBranchMembers7343.filter (independentCachedEdge 1720)=independentCachedBranchMembers7342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7342
def independentCachedBranchMembers7344 : Finset ℕ := ([12,18,40,66,136,252,1708,1714,1734,1752,2620,2646,2668,2674,2716,2770,2792,3132,3158,3180,3186,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7344 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7344 5 (fun x => (if x<2668 then (if x<1708 then (if x<66 then (if x<18 then 0 else (if x<40 then 0 else 1)) else (if x<136 then 1 else (if x<252 then 2 else 2))) else (if x<1752 then (if x<1714 then 0 else (if x<1734 then 0 else 1)) else (if x<2620 then 2 else (if x<2646 then 1 else 1)))) else (if x<3158 then (if x<2770 then (if x<2674 then 0 else (if x<2716 then 0 else 2)) else (if x<2792 then 3 else (if x<3132 then 2 else 3))) else (if x<3256 then (if x<3180 then 3 else (if x<3186 then 4 else 4)) else (if x<3276 then 1 else (if x<3282 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7345 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1702,1708,1714,1720,1734,1740,1746,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7345 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7345 1702 5
  · have he : independentCachedBranchMembers7345.erase 1702=independentCachedBranchMembers7343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7343
  · have he : independentCachedBranchMembers7345.filter (independentCachedEdge 1702)=independentCachedBranchMembers7344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7344
def independentCachedBranchMembers7346 : Finset ℕ := ([18,40,1596,1650,1692,1702,1714,1734,1746,1768,2614,2646,2668,2680,2732,3126,3158,3180,3192,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7346 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7346 5 (fun x => (if x<2668 then (if x<1714 then (if x<1650 then (if x<40 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 2 else 1))) else (if x<1768 then (if x<1734 then 2 else (if x<1746 then 2 else 0)) else (if x<2614 then 0 else (if x<2646 then 1 else 0)))) else (if x<3192 then (if x<3126 then (if x<2680 then 0 else (if x<2732 then 1 else 1)) else (if x<3158 then 3 else (if x<3180 then 4 else 3))) else (if x<3256 then (if x<3222 then 4 else (if x<3244 then 0 else 0)) else (if x<3276 then 2 else (if x<3298 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7347 : Finset ℕ := ([18,1650,1702,1714,1734,1746,2614,2646,3126,3158,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7347 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7347 4 (fun x => (if x<2614 then (if x<1714 then (if x<1650 then 0 else (if x<1702 then 0 else 1)) else (if x<1734 then 2 else (if x<1746 then 2 else 1))) else (if x<3158 then (if x<2646 then 0 else (if x<3126 then 3 else 3)) else (if x<3222 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7348 : Finset ℕ := ([18,40,252,1596,1650,1692,1702,1714,1734,1746,1768,2614,2646,2668,2680,2732,3126,3158,3180,3192,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7348 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7348 252 4
  · have he : independentCachedBranchMembers7348.erase 252=independentCachedBranchMembers7346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7346
  · have he : independentCachedBranchMembers7348.filter (independentCachedEdge 252)=independentCachedBranchMembers7347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7347
def independentCachedBranchMembers7349 : Finset ℕ := ([40,1596,1702,1714,1734,1746,2668,2680,3180,3192,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7349 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7349 4 (fun x => (if x<2668 then (if x<1714 then (if x<1596 then 0 else (if x<1702 then 0 else 1)) else (if x<1734 then 2 else (if x<1746 then 2 else 1))) else (if x<3192 then (if x<2680 then 0 else (if x<3180 then 3 else 3)) else (if x<3222 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7350 : Finset ℕ := ([18,40,136,252,1596,1650,1692,1702,1714,1734,1746,1768,2614,2646,2668,2680,2732,3126,3158,3180,3192,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7350 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7350 136 4
  · have he : independentCachedBranchMembers7350.erase 136=independentCachedBranchMembers7348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7348
  · have he : independentCachedBranchMembers7350.filter (independentCachedEdge 136)=independentCachedBranchMembers7349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7349
def independentCachedBranchMembers7351 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7351 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7351 1762 5
  · have he : independentCachedBranchMembers7351.erase 1762=independentCachedBranchMembers7345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7345
  · have he : independentCachedBranchMembers7351.filter (independentCachedEdge 1762)=independentCachedBranchMembers7350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7350
def independentCachedBranchMembers7352 : Finset ℕ := ([12,66,1622,1644,1692,1702,1714,1734,1746,1768,2620,2652,2662,2674,2732,3132,3164,3174,3186,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7352 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7352 5 (fun x => (if x<2662 then (if x<1714 then (if x<1644 then (if x<66 then 0 else (if x<1622 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 0 else 1))) else (if x<1768 then (if x<1734 then 2 else (if x<1746 then 2 else 0)) else (if x<2620 then 2 else (if x<2652 then 0 else 1)))) else (if x<3186 then (if x<3132 then (if x<2674 then 1 else (if x<2732 then 0 else 1)) else (if x<3164 then 3 else (if x<3174 then 4 else 3))) else (if x<3256 then (if x<3222 then 4 else (if x<3244 then 2 else 0)) else (if x<3276 then 2 else (if x<3298 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7353 : Finset ℕ := ([66,1622,1702,1714,1734,1746,2662,2674,3174,3186,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7353 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7353 4 (fun x => (if x<2662 then (if x<1714 then (if x<1622 then 0 else (if x<1702 then 0 else 1)) else (if x<1734 then 2 else (if x<1746 then 2 else 1))) else (if x<3186 then (if x<2674 then 0 else (if x<3174 then 3 else 3)) else (if x<3222 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7354 : Finset ℕ := ([12,66,252,1622,1644,1692,1702,1714,1734,1746,1768,2620,2652,2662,2674,2732,3132,3164,3174,3186,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7354 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7354 252 4
  · have he : independentCachedBranchMembers7354.erase 252=independentCachedBranchMembers7352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7352
  · have he : independentCachedBranchMembers7354.filter (independentCachedEdge 252)=independentCachedBranchMembers7353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7353
def independentCachedBranchMembers7355 : Finset ℕ := ([12,1644,1702,1714,1734,1746,2620,2652,3132,3164,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7355 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7355 4 (fun x => (if x<2620 then (if x<1714 then (if x<1644 then 0 else (if x<1702 then 0 else 1)) else (if x<1734 then 2 else (if x<1746 then 2 else 1))) else (if x<3164 then (if x<2652 then 0 else (if x<3132 then 3 else 3)) else (if x<3222 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7356 : Finset ℕ := ([12,66,136,252,1622,1644,1692,1702,1714,1734,1746,1768,2620,2652,2662,2674,2732,3132,3164,3174,3186,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7356 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7356 136 4
  · have he : independentCachedBranchMembers7356.erase 136=independentCachedBranchMembers7354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7354
  · have he : independentCachedBranchMembers7356.filter (independentCachedEdge 136)=independentCachedBranchMembers7355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7355
def independentCachedBranchMembers7357 : Finset ℕ := ([12,18,40,66,136,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3244,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7357 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7357 1686 5
  · have he : independentCachedBranchMembers7357.erase 1686=independentCachedBranchMembers7351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7351
  · have he : independentCachedBranchMembers7357.filter (independentCachedEdge 1686)=independentCachedBranchMembers7356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7356
def independentCachedBranchMembers7358 : Finset ℕ := ([12,40,252,1596,1644,1708,1720,1740,1752,2620,2652,2668,2680,2716,2732,2792,3132,3164,3180,3192,3244,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7358 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7358 5 (fun x => (if x<2668 then (if x<1708 then (if x<252 then (if x<40 then 0 else 1) else (if x<1596 then 0 else (if x<1644 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1740 then 1 else 0)) else (if x<2620 then 2 else (if x<2652 then 1 else 0)))) else (if x<3164 then (if x<2732 then (if x<2680 then 3 else (if x<2716 then 4 else 2)) else (if x<2792 then 0 else (if x<3132 then 1 else 3))) else (if x<3244 then (if x<3180 then 4 else (if x<3192 then 0 else 1)) else (if x<3256 then 1 else (if x<3276 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7359 : Finset ℕ := ([12,1644,1708,1720,1740,1752,2620,2652,2716,2792,3132,3164] : List ℕ).toFinset
theorem independentCachedBranchBound7359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7359 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7359 4 (fun x => (if x<2620 then (if x<1720 then (if x<1644 then 0 else (if x<1708 then 0 else 1)) else (if x<1740 then 2 else (if x<1752 then 2 else 1))) else (if x<2792 then (if x<2652 then 0 else (if x<2716 then 3 else 1)) else (if x<3132 then 1 else (if x<3164 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
