/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch143
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7392 : Finset ℕ := ([40,66,130,246,1596,1622,1644,1650,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2716,2770,2792,3132,3158,3180,3186,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7392 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7392 1644 4
  · have he : independentCachedBranchMembers7392.erase 1644=independentCachedBranchMembers7390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7390
  · have he : independentCachedBranchMembers7392.filter (independentCachedEdge 1644)=independentCachedBranchMembers7391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7391
def independentCachedBranchMembers7393 : Finset ℕ := ([66,130,1596,1734,1752,1762,2652,2662,2680,2716,3132,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7393 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7393 4 (fun x => (if x<2652 then (if x<1734 then (if x<130 then 0 else (if x<1596 then 1 else 0)) else (if x<1752 then 1 else (if x<1762 then 2 else 2))) else (if x<2716 then (if x<2662 then 2 else (if x<2680 then 2 else 1)) else (if x<3132 then 0 else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7394 : Finset ℕ := ([18,40,66,130,246,1596,1622,1644,1650,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2716,2770,2792,3132,3158,3180,3186,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7394 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7394 18 4
  · have he : independentCachedBranchMembers7394.erase 18=independentCachedBranchMembers7392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7392
  · have he : independentCachedBranchMembers7394.filter (independentCachedEdge 18)=independentCachedBranchMembers7393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7393
def independentCachedBranchMembers7395 : Finset ℕ := ([40,246,1622,1686,1734,1752,2614,2662,2680,2792,3158,3222] : List ℕ).toFinset
theorem independentCachedBranchBound7395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7395 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7395 4 (fun x => (if x<2614 then (if x<1686 then (if x<246 then 0 else (if x<1622 then 1 else 0)) else (if x<1734 then 1 else (if x<1752 then 2 else 2))) else (if x<2792 then (if x<2662 then 1 else (if x<2680 then 2 else 2)) else (if x<3158 then 0 else (if x<3222 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7396 : Finset ℕ := ([12,18,40,66,130,246,1596,1622,1644,1650,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2716,2770,2792,3132,3158,3180,3186,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7396 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7396 12 4
  · have he : independentCachedBranchMembers7396.erase 12=independentCachedBranchMembers7394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7394
  · have he : independentCachedBranchMembers7396.filter (independentCachedEdge 12)=independentCachedBranchMembers7395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7395
def independentCachedBranchMembers7397 : Finset ℕ := ([130,246,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,3132,3158,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7397 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7397 4 (fun x => (if x<2614 then (if x<1714 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3132 then (if x<2662 then (if x<2652 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3180 then (if x<3158 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7398 : Finset ℕ := ([12,18,40,66,130,246,1596,1622,1644,1650,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2716,2770,2792,3132,3158,3180,3186,3222,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7398 3244 4
  · have he : independentCachedBranchMembers7398.erase 3244=independentCachedBranchMembers7396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7396
  · have he : independentCachedBranchMembers7398.filter (independentCachedEdge 3244)=independentCachedBranchMembers7397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7397
def independentCachedBranchMembers7399 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2716,2732,2738,2758,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7399 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7399 2776 5
  · have he : independentCachedBranchMembers7399.erase 2776=independentCachedBranchMembers7385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7385
  · have he : independentCachedBranchMembers7399.filter (independentCachedEdge 2776)=independentCachedBranchMembers7398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7398
def independentCachedBranchMembers7400 : Finset ℕ := ([12,66,136,252,1596,1650,1686,1708,1720,1740,1752,1762,2614,2646,2668,2680,2716,2738,2758,2770,2792,3132,3164,3174,3186,3222,3244,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7400 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7400 5 (fun x => (if x<2680 then (if x<1708 then (if x<252 then (if x<66 then 0 else (if x<136 then 0 else 1)) else (if x<1650 then (if x<1596 then 1 else 0) else (if x<1686 then 0 else 2))) else (if x<1762 then (if x<1740 then (if x<1720 then 1 else 2) else (if x<1752 then 2 else 1)) else (if x<2646 then (if x<2614 then 2 else 3) else (if x<2668 then 4 else 3)))) else (if x<3164 then (if x<2758 then (if x<2716 then 4 else (if x<2738 then 0 else 2)) else (if x<2792 then (if x<2770 then 2 else 0) else (if x<3132 then 1 else 3))) else (if x<3244 then (if x<3186 then (if x<3174 then 4 else 3) else (if x<3222 then 4 else 3)) else (if x<3276 then (if x<3256 then 0 else 1) else (if x<3298 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7401 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2758,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7401 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7401 2710 5
  · have he : independentCachedBranchMembers7401.erase 2710=independentCachedBranchMembers7399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7399
  · have he : independentCachedBranchMembers7401.filter (independentCachedEdge 2710)=independentCachedBranchMembers7400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7400
def independentCachedBranchMembers7402 : Finset ℕ := ([136,252,1596,1622,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2792,3126,3164,3180,3186,3222,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7402 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7402 5 (fun x => (if x<2680 then (if x<1714 then (if x<1622 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 0 else 2))) else (if x<1768 then (if x<1734 then 1 else (if x<1752 then 2 else 1)) else (if x<2646 then (if x<2620 then 0 else 2) else (if x<2662 then 2 else 3)))) else (if x<3180 then (if x<2738 then (if x<2716 then 3 else (if x<2732 then 4 else 0)) else (if x<3126 then (if x<2792 then 3 else 4) else (if x<3164 then 1 else 1))) else (if x<3256 then (if x<3186 then 3 else (if x<3222 then 3 else 4)) else (if x<3282 then (if x<3276 then 0 else 0) else (if x<3298 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7403 : Finset ℕ := ([252,1714,1752,1768,2680,2738,2792,3126,3164,3180,3222,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7403 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7403 4 (fun x => (if x<2792 then (if x<1768 then (if x<1714 then 0 else (if x<1752 then 1 else 0)) else (if x<2680 then 1 else (if x<2738 then 0 else 2))) else (if x<3180 then (if x<3126 then 2 else (if x<3164 then 1 else 0)) else (if x<3222 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7404 : Finset ℕ := ([66,136,252,1596,1622,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2792,3126,3164,3180,3186,3222,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7404 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7404 66 4
  · have he : independentCachedBranchMembers7404.erase 66=independentCachedBranchMembers7402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7402
  · have he : independentCachedBranchMembers7404.filter (independentCachedEdge 66)=independentCachedBranchMembers7403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7403
def independentCachedBranchMembers7405 : Finset ℕ := ([136,1692,1714,1752,2662,2716,2738,3126,3164,3186,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7405 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7405 4 (fun x => (if x<2738 then (if x<1752 then (if x<1692 then 0 else (if x<1714 then 0 else 1)) else (if x<2662 then 1 else (if x<2716 then 0 else 2))) else (if x<3186 then (if x<3126 then 2 else (if x<3164 then 1 else 1)) else (if x<3276 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7406 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2792,3126,3164,3180,3186,3222,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7406 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7406 40 4
  · have he : independentCachedBranchMembers7406.erase 40=independentCachedBranchMembers7404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7404
  · have he : independentCachedBranchMembers7406.filter (independentCachedEdge 40)=independentCachedBranchMembers7405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7405
def independentCachedBranchMembers7407 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1768,2620,2646,2716,2792,3126,3164,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7407 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7407 4 (fun x => (if x<2620 then (if x<1596 then (if x<136 then (if x<66 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1692 then (if x<1622 then 0 else 0) else (if x<1768 then 1 else 1))) else (if x<3126 then (if x<2716 then (if x<2646 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3164 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7408 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2792,3126,3164,3180,3186,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7408 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7408 3238 4
  · have he : independentCachedBranchMembers7408.erase 3238=independentCachedBranchMembers7406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7406
  · have he : independentCachedBranchMembers7408.filter (independentCachedEdge 3238)=independentCachedBranchMembers7407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7407
def independentCachedBranchMembers7409 : Finset ℕ := ([40,66,1596,1622,1708,1714,1734,1752,2662,2680,2716,2792,3180,3186,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7409 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7409 4 (fun x => (if x<2662 then (if x<1708 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3180 then (if x<2716 then (if x<2680 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3186 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7410 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2776,2792,3126,3164,3180,3186,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7410 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7410 2776 4
  · have he : independentCachedBranchMembers7410.erase 2776=independentCachedBranchMembers7408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7408
  · have he : independentCachedBranchMembers7410.filter (independentCachedEdge 2776)=independentCachedBranchMembers7409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7409
def independentCachedBranchMembers7411 : Finset ℕ := ([136,252,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,3126,3164,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7411 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7411 4 (fun x => (if x<2620 then (if x<1714 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3126 then (if x<2662 then (if x<2646 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3180 then (if x<3164 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7412 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2716,2732,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7412 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7412 2758 4
  · have he : independentCachedBranchMembers7412.erase 2758=independentCachedBranchMembers7410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7410
  · have he : independentCachedBranchMembers7412.filter (independentCachedEdge 2758)=independentCachedBranchMembers7411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7411
def independentCachedBranchMembers7413 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2758,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7413 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7413 3250 5
  · have he : independentCachedBranchMembers7413.erase 3250=independentCachedBranchMembers7401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7401
  · have he : independentCachedBranchMembers7413.filter (independentCachedEdge 3250)=independentCachedBranchMembers7412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7412
def independentCachedBranchMembers7414 : Finset ℕ := ([66,130,246,1596,1622,1686,1702,1720,1740,1746,1762,2614,2652,2668,2674,2716,2732,2738,2758,2792,3132,3158,3174,3192,3222,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7414 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7414 5 (fun x => (if x<2674 then (if x<1720 then (if x<1596 then (if x<130 then 0 else (if x<246 then 1 else 0)) else (if x<1686 then (if x<1622 then 1 else 0) else (if x<1702 then 1 else 2))) else (if x<1762 then (if x<1740 then 2 else (if x<1746 then 2 else 2)) else (if x<2652 then (if x<2614 then 0 else 3) else (if x<2668 then 3 else 1)))) else (if x<3158 then (if x<2738 then (if x<2716 then 0 else (if x<2732 then 4 else 2)) else (if x<2792 then (if x<2758 then 2 else 0) else (if x<3132 then 4 else 3))) else (if x<3222 then (if x<3174 then 3 else (if x<3192 then 0 else 1)) else (if x<3282 then (if x<3276 then 4 else 3) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7415 : Finset ℕ := ([246,1702,1740,1762,2614,2652,2674,2716,2738,3174,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7415 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7415 4 (fun x => (if x<2674 then (if x<1762 then (if x<1702 then 0 else (if x<1740 then 0 else 1)) else (if x<2614 then 1 else (if x<2652 then 0 else 1))) else (if x<3174 then (if x<2716 then 1 else (if x<2738 then 2 else 2)) else (if x<3276 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7416 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1702,1720,1740,1746,1762,2614,2652,2668,2674,2716,2732,2738,2758,2792,3132,3158,3174,3192,3222,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7416 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7416 40 4
  · have he : independentCachedBranchMembers7416.erase 40=independentCachedBranchMembers7414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7414
  · have he : independentCachedBranchMembers7416.filter (independentCachedEdge 40)=independentCachedBranchMembers7415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7415
def independentCachedBranchMembers7417 : Finset ℕ := ([130,246,1686,1702,1720,1740,1746,1762,2614,2652,2668,2674,3132,3158,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7417 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7417 4 (fun x => (if x<2614 then (if x<1720 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3132 then (if x<2668 then (if x<2652 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3174 then (if x<3158 then 2 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7418 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1702,1720,1740,1746,1762,2614,2652,2668,2674,2716,2732,2738,2758,2792,3132,3158,3174,3192,3222,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7418 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7418 3256 4
  · have he : independentCachedBranchMembers7418.erase 3256=independentCachedBranchMembers7416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7416
  · have he : independentCachedBranchMembers7418.filter (independentCachedEdge 3256)=independentCachedBranchMembers7417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7417
def independentCachedBranchMembers7419 : Finset ℕ := ([40,66,1596,1622,1702,1720,1740,1746,2668,2674,2716,2792,3174,3192,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7419 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7419 4 (fun x => (if x<2668 then (if x<1702 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1740 then (if x<1720 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3174 then (if x<2716 then (if x<2674 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3192 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7420 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1702,1720,1740,1746,1762,2614,2652,2668,2674,2716,2732,2738,2758,2792,3132,3158,3174,3192,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7420 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7420 3238 4
  · have he : independentCachedBranchMembers7420.erase 3238=independentCachedBranchMembers7418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7418
  · have he : independentCachedBranchMembers7420.filter (independentCachedEdge 3238)=independentCachedBranchMembers7419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7419
def independentCachedBranchMembers7421 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1762,2614,2652,2716,2792,3132,3158,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7421 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7421 4 (fun x => (if x<2614 then (if x<1596 then (if x<130 then (if x<66 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1686 then (if x<1622 then 0 else 0) else (if x<1762 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2652 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3158 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7422 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1702,1720,1740,1746,1762,2614,2652,2668,2674,2716,2732,2738,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7422 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7422 2776 4
  · have he : independentCachedBranchMembers7422.erase 2776=independentCachedBranchMembers7420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7420
  · have he : independentCachedBranchMembers7422.filter (independentCachedEdge 2776)=independentCachedBranchMembers7421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7421
def independentCachedBranchMembers7423 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2758,2764,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7423 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7423 2764 5
  · have he : independentCachedBranchMembers7423.erase 2764=independentCachedBranchMembers7413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7413
  · have he : independentCachedBranchMembers7423.filter (independentCachedEdge 2764)=independentCachedBranchMembers7422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7422
end EntropyDesigns.QuadraticRefinement
