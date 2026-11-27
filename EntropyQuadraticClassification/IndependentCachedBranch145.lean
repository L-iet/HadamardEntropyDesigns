/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch144
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7424 : Finset ℕ := ([66,246,1596,1622,1644,1692,1702,1714,1740,1752,1762,2614,2652,2662,2674,2732,2758,2770,2792,3126,3164,3174,3186,3222,3244,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7424 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7424 5 (fun x => (if x<2662 then (if x<1702 then (if x<1622 then (if x<246 then 0 else (if x<1596 then 0 else 1)) else (if x<1644 then 0 else (if x<1692 then 2 else 2))) else (if x<1752 then (if x<1714 then 1 else (if x<1740 then 3 else 1)) else (if x<2614 then (if x<1762 then 3 else 0) else (if x<2652 then 1 else 1)))) else (if x<3164 then (if x<2758 then (if x<2674 then 0 else (if x<2732 then 4 else 1)) else (if x<2792 then (if x<2770 then 1 else 0) else (if x<3126 then 4 else 3))) else (if x<3222 then (if x<3174 then 2 else (if x<3186 then 2 else 0)) else (if x<3256 then (if x<3244 then 2 else 2) else (if x<3282 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7425 : Finset ℕ := ([246,1596,1644,1702,1714,1762,2652,2758,2770,3164,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7425 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7425 4 (fun x => (if x<2652 then (if x<1702 then (if x<1596 then 0 else (if x<1644 then 1 else 2)) else (if x<1714 then 0 else (if x<1762 then 1 else 2))) else (if x<3164 then (if x<2758 then 1 else (if x<2770 then 0 else 1)) else (if x<3222 then 2 else (if x<3282 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7426 : Finset ℕ := ([66,136,246,1596,1622,1644,1692,1702,1714,1740,1752,1762,2614,2652,2662,2674,2732,2758,2770,2792,3126,3164,3174,3186,3222,3244,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7426 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7426 136 4
  · have he : independentCachedBranchMembers7426.erase 136=independentCachedBranchMembers7424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7424
  · have he : independentCachedBranchMembers7426.filter (independentCachedEdge 136)=independentCachedBranchMembers7425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7425
def independentCachedBranchMembers7427 : Finset ℕ := ([66,1596,1692,1702,1752,1762,2652,2662,2758,3164,3174,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7427 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7427 4 (fun x => (if x<2652 then (if x<1702 then (if x<1596 then 0 else (if x<1692 then 0 else 1)) else (if x<1752 then 1 else (if x<1762 then 2 else 2))) else (if x<3164 then (if x<2662 then 1 else (if x<2758 then 1 else 0)) else (if x<3174 then 2 else (if x<3256 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7428 : Finset ℕ := ([18,66,136,246,1596,1622,1644,1692,1702,1714,1740,1752,1762,2614,2652,2662,2674,2732,2758,2770,2792,3126,3164,3174,3186,3222,3244,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7428 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7428 18 4
  · have he : independentCachedBranchMembers7428.erase 18=independentCachedBranchMembers7426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7426
  · have he : independentCachedBranchMembers7428.filter (independentCachedEdge 18)=independentCachedBranchMembers7427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7427
def independentCachedBranchMembers7429 : Finset ℕ := ([246,1596,1692,1702,1714,2652,2662,2674,2758,2770,2792,3126,3222,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7429 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7429 4 (fun x => (if x<2674 then (if x<1702 then (if x<1596 then 0 else (if x<1692 then 1 else 2)) else (if x<2652 then (if x<1714 then 0 else 1) else (if x<2662 then 1 else 0))) else (if x<3126 then (if x<2770 then (if x<2758 then 2 else 3) else (if x<2792 then 1 else 3)) else (if x<3244 then (if x<3222 then 0 else 3) else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7430 : Finset ℕ := ([1702,1714,2652,2792,3126,3222] : List ℕ).toFinset
theorem independentCachedBranchBound7430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7430 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7430 3 (fun x => (if x<2792 then (if x<1714 then 0 else (if x<2652 then 1 else 0)) else (if x<3126 then 2 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7431 : Finset ℕ := ([66,246,1596,1692,1702,1714,2652,2662,2674,2758,2770,2792,3126,3222,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7431 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7431 66 3
  · have he : independentCachedBranchMembers7431.erase 66=independentCachedBranchMembers7429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7429
  · have he : independentCachedBranchMembers7431.filter (independentCachedEdge 66)=independentCachedBranchMembers7430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7430
def independentCachedBranchMembers7432 : Finset ℕ := ([18,66,136,246,1596,1622,1644,1692,1702,1714,1740,1752,1762,2614,2652,2662,2674,2732,2758,2770,2792,3126,3164,3174,3186,3222,3244,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7432 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7432 3304 4
  · have he : independentCachedBranchMembers7432.erase 3304=independentCachedBranchMembers7428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7428
  · have he : independentCachedBranchMembers7432.filter (independentCachedEdge 3304)=independentCachedBranchMembers7431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7431
def independentCachedBranchMembers7433 : Finset ℕ := ([66,136,1596,1740,1752,1762,2614,2758,2770,2792,3164,3174,3186,3222,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7433 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7433 4 (fun x => (if x<2770 then (if x<1752 then (if x<1596 then (if x<136 then 0 else 0) else (if x<1740 then 1 else 1)) else (if x<2614 then (if x<1762 then 2 else 2) else (if x<2758 then 1 else 1))) else (if x<3186 then (if x<3164 then (if x<2792 then 2 else 2) else (if x<3174 then 3 else 0)) else (if x<3244 then (if x<3222 then 3 else 3) else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7434 : Finset ℕ := ([18,66,136,246,1596,1622,1644,1692,1702,1714,1740,1752,1762,2614,2652,2662,2674,2710,2732,2758,2770,2792,3126,3164,3174,3186,3222,3244,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7434 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7434 2710 4
  · have he : independentCachedBranchMembers7434.erase 2710=independentCachedBranchMembers7432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7432
  · have he : independentCachedBranchMembers7434.filter (independentCachedEdge 2710)=independentCachedBranchMembers7433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7433
def independentCachedBranchMembers7435 : Finset ℕ := ([246,1692,1702,1714,1740,1752,1762,2614,2652,2662,2674,3126,3164,3174,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7435 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7435 4 (fun x => (if x<2614 then (if x<1714 then (if x<1692 then 0 else (if x<1702 then 1 else 0)) else (if x<1752 then (if x<1740 then 1 else 2) else (if x<1762 then 3 else 2))) else (if x<3126 then (if x<2662 then (if x<2652 then 0 else 1) else (if x<2674 then 3 else 1)) else (if x<3174 then (if x<3164 then 3 else 2) else (if x<3186 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7436 : Finset ℕ := ([246,1702,1714,1762,2652,3164] : List ℕ).toFinset
theorem independentCachedBranchBound7436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7436 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7436 3 (fun x => (if x<1762 then (if x<1702 then 0 else (if x<1714 then 0 else 1)) else (if x<2652 then 2 else (if x<3164 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7437 : Finset ℕ := ([136,246,1692,1702,1714,1740,1752,1762,2614,2652,2662,2674,3126,3164,3174,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7437 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7437 136 3
  · have he : independentCachedBranchMembers7437.erase 136=independentCachedBranchMembers7435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7435
  · have he : independentCachedBranchMembers7437.filter (independentCachedEdge 136)=independentCachedBranchMembers7436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7436
def independentCachedBranchMembers7438 : Finset ℕ := ([18,40,66,136,246,1596,1622,1644,1692,1702,1714,1740,1752,1762,2614,2652,2662,2674,2710,2732,2758,2770,2792,3126,3164,3174,3186,3222,3244,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7438 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7438 40 4
  · have he : independentCachedBranchMembers7438.erase 40=independentCachedBranchMembers7434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7434
  · have he : independentCachedBranchMembers7438.filter (independentCachedEdge 40)=independentCachedBranchMembers7437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7437
def independentCachedBranchMembers7439 : Finset ℕ := ([12,18,40,66,130,136,246,252,1596,1622,1628,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2758,2764,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7439 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7439 1628 5
  · have he : independentCachedBranchMembers7439.erase 1628=independentCachedBranchMembers7423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7423
  · have he : independentCachedBranchMembers7439.filter (independentCachedEdge 1628)=independentCachedBranchMembers7438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7438
def independentCachedBranchMembers7440 : Finset ℕ := ([12,40,130,252,1596,1622,1650,1686,1702,1714,1740,1752,1768,2614,2652,2668,2680,2716,2732,2758,2770,3126,3164,3180,3192,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7440 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7440 5 (fun x => (if x<2652 then (if x<1686 then (if x<252 then (if x<40 then 0 else (if x<130 then 1 else 0)) else (if x<1622 then (if x<1596 then 1 else 0) else (if x<1650 then 2 else 3))) else (if x<1740 then (if x<1702 then 3 else (if x<1714 then 2 else 0)) else (if x<1768 then (if x<1752 then 2 else 3) else (if x<2614 then 1 else 2)))) else (if x<3126 then (if x<2716 then (if x<2668 then 0 else (if x<2680 then 1 else 3)) else (if x<2758 then (if x<2732 then 3 else 2) else (if x<2770 then 2 else 0))) else (if x<3244 then (if x<3180 then (if x<3164 then 4 else 4) else (if x<3192 then 0 else 1)) else (if x<3282 then (if x<3256 then 1 else 4) else (if x<3298 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7441 : Finset ℕ := ([130,1622,1702,1714,1768,2614,2668,2680,2716,2758,2770,3164,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7441 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7441 4 (fun x => (if x<2680 then (if x<1714 then (if x<1622 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2668 then 1 else 2))) else (if x<3164 then (if x<2758 then (if x<2716 then 0 else 3) else (if x<2770 then 3 else 1)) else (if x<3256 then (if x<3244 then 0 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7442 : Finset ℕ := ([1702,1714,2614,2716,3164,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7442 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7442 3 (fun x => (if x<2716 then (if x<1714 then 0 else (if x<2614 then 1 else 0)) else (if x<3164 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7443 : Finset ℕ := ([40,130,1622,1702,1714,1768,2614,2668,2680,2716,2758,2770,3164,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7443 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7443 40 3
  · have he : independentCachedBranchMembers7443.erase 40=independentCachedBranchMembers7441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7441
  · have he : independentCachedBranchMembers7443.filter (independentCachedEdge 40)=independentCachedBranchMembers7442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7442
def independentCachedBranchMembers7444 : Finset ℕ := ([12,40,130,252,1596,1622,1650,1686,1702,1714,1740,1752,1768,2614,2652,2668,2680,2716,2732,2758,2770,3126,3164,3180,3192,3228,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7444 3228 4
  · have he : independentCachedBranchMembers7444.erase 3228=independentCachedBranchMembers7440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7440
  · have he : independentCachedBranchMembers7444.filter (independentCachedEdge 3228)=independentCachedBranchMembers7443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7443
def independentCachedBranchMembers7445 : Finset ℕ := ([40,252,1622,1686,1740,1752,2652,2716,2758,2770,3126,3180,3192,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7445 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7445 4 (fun x => (if x<2758 then (if x<1740 then (if x<1622 then (if x<252 then 0 else 0) else (if x<1686 then 1 else 2)) else (if x<2652 then (if x<1752 then 1 else 2) else (if x<2716 then 1 else 2))) else (if x<3192 then (if x<3126 then (if x<2770 then 1 else 2) else (if x<3180 then 3 else 0)) else (if x<3256 then (if x<3244 then 3 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7446 : Finset ℕ := ([12,40,130,252,1596,1622,1650,1686,1702,1714,1740,1752,1768,2614,2652,2668,2680,2716,2732,2758,2770,2786,3126,3164,3180,3192,3228,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7446 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7446 2786 4
  · have he : independentCachedBranchMembers7446.erase 2786=independentCachedBranchMembers7444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7444
  · have he : independentCachedBranchMembers7446.filter (independentCachedEdge 2786)=independentCachedBranchMembers7445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7445
def independentCachedBranchMembers7447 : Finset ℕ := ([130,252,1686,1702,1714,1740,1752,1768,2614,2652,2668,2680,3126,3164,3180,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7447 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7447 4 (fun x => (if x<2614 then (if x<1714 then (if x<1686 then (if x<252 then 0 else 1) else (if x<1702 then 0 else 2)) else (if x<1752 then (if x<1740 then 3 else 1) else (if x<1768 then 3 else 2))) else (if x<3126 then (if x<2668 then (if x<2652 then 2 else 1) else (if x<2680 then 0 else 2)) else (if x<3180 then (if x<3164 then 3 else 3) else (if x<3192 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7448 : Finset ℕ := ([12,40,66,130,252,1596,1622,1650,1686,1702,1714,1740,1752,1768,2614,2652,2668,2680,2716,2732,2758,2770,2786,3126,3164,3180,3192,3228,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7448 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7448 66 4
  · have he : independentCachedBranchMembers7448.erase 66=independentCachedBranchMembers7446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7446
  · have he : independentCachedBranchMembers7448.filter (independentCachedEdge 66)=independentCachedBranchMembers7447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7447
def independentCachedBranchMembers7449 : Finset ℕ := ([12,18,40,66,130,136,246,252,1590,1596,1622,1628,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2758,2764,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7449 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7449 1590 5
  · have he : independentCachedBranchMembers7449.erase 1590=independentCachedBranchMembers7439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7439
  · have he : independentCachedBranchMembers7449.filter (independentCachedEdge 1590)=independentCachedBranchMembers7448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7448
def independentCachedBranchMembers7450 : Finset ℕ := ([40,66,136,246,1622,1650,1692,1708,1720,1734,1746,1762,2620,2646,2662,2674,2716,2732,2758,2770,3132,3158,3174,3186,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7450 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7450 5 (fun x => (if x<2662 then (if x<1708 then (if x<246 then (if x<66 then 0 else (if x<136 then 0 else 1)) else (if x<1650 then (if x<1622 then 2 else 0) else (if x<1692 then 1 else 3))) else (if x<1746 then (if x<1720 then 4 else (if x<1734 then 1 else 2)) else (if x<2620 then (if x<1762 then 3 else 4) else (if x<2646 then 3 else 1)))) else (if x<3158 then (if x<2732 then (if x<2674 then 2 else (if x<2716 then 3 else 1)) else (if x<2770 then (if x<2758 then 0 else 0) else (if x<3132 then 2 else 4))) else (if x<3244 then (if x<3174 then 2 else (if x<3186 then 1 else 4)) else (if x<3282 then (if x<3256 then 1 else 0) else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7451 : Finset ℕ := ([40,136,246,1622,1720,1734,2646,2662,2758,3158,3174,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7451 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7451 4 (fun x => (if x<2646 then (if x<1622 then (if x<136 then 0 else (if x<246 then 1 else 2)) else (if x<1720 then 0 else (if x<1734 then 1 else 2))) else (if x<3158 then (if x<2662 then 1 else (if x<2758 then 2 else 0)) else (if x<3174 then 2 else (if x<3256 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7452 : Finset ℕ := ([12,40,66,136,246,1622,1650,1692,1708,1720,1734,1746,1762,2620,2646,2662,2674,2716,2732,2758,2770,3132,3158,3174,3186,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7452 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7452 12 4
  · have he : independentCachedBranchMembers7452.erase 12=independentCachedBranchMembers7450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7450
  · have he : independentCachedBranchMembers7452.filter (independentCachedEdge 12)=independentCachedBranchMembers7451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7451
def independentCachedBranchMembers7453 : Finset ℕ := ([40,246,1622,1692,1734,1746,2646,2716,2758,2770,3132,3174,3186,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7453 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7453 4 (fun x => (if x<2758 then (if x<1734 then (if x<1622 then (if x<246 then 0 else 1) else (if x<1692 then 0 else 2)) else (if x<2646 then (if x<1746 then 1 else 2) else (if x<2716 then 1 else 3))) else (if x<3186 then (if x<3132 then (if x<2770 then 0 else 3) else (if x<3174 then 2 else 1)) else (if x<3256 then (if x<3244 then 2 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7454 : Finset ℕ := ([12,40,66,136,246,1622,1650,1692,1708,1720,1734,1746,1762,2620,2646,2662,2674,2716,2732,2758,2770,3132,3158,3174,3186,3228,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7454 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7454 3228 4
  · have he : independentCachedBranchMembers7454.erase 3228=independentCachedBranchMembers7452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7452
  · have he : independentCachedBranchMembers7454.filter (independentCachedEdge 3228)=independentCachedBranchMembers7453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7453
def independentCachedBranchMembers7455 : Finset ℕ := ([40,136,1622,1708,1720,1762,2620,2662,2674,2716,2758,2770,3158,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7455 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7455 4 (fun x => (if x<2674 then (if x<1720 then (if x<1622 then (if x<136 then 0 else 1) else (if x<1708 then 0 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2662 then 2 else 2))) else (if x<3158 then (if x<2758 then (if x<2716 then 1 else 3) else (if x<2770 then 0 else 3)) else (if x<3256 then (if x<3244 then 1 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
