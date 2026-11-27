/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch146
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7488 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2710,2732,2738,2758,2776,2786,3126,3164,3174,3192,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7488 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7488 2732 4
  · have he : independentCachedBranchMembers7488.erase 2732=independentCachedBranchMembers7486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7486
  · have he : independentCachedBranchMembers7488.filter (independentCachedEdge 2732)=independentCachedBranchMembers7487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7487
def independentCachedBranchMembers7489 : Finset ℕ := ([130,1622,1708,1714,1762,2620,2668,2674,2710,2758,2776,3164,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7489 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7489 4 (fun x => (if x<2674 then (if x<1714 then (if x<1622 then 0 else (if x<1708 then 1 else 2)) else (if x<2620 then (if x<1762 then 0 else 1) else (if x<2668 then 2 else 0))) else (if x<3164 then (if x<2758 then (if x<2710 then 1 else 3) else (if x<2776 then 1 else 3)) else (if x<3256 then (if x<3238 then 0 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7490 : Finset ℕ := ([1714,1762,2674,2776,3164,3238] : List ℕ).toFinset
theorem independentCachedBranchBound7490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7490 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7490 3 (fun x => (if x<2776 then (if x<1762 then 0 else (if x<2674 then 1 else 0)) else (if x<3164 then 2 else (if x<3238 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7491 : Finset ℕ := ([40,130,1622,1708,1714,1762,2620,2668,2674,2710,2758,2776,3164,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7491 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7491 40 3
  · have he : independentCachedBranchMembers7491.erase 40=independentCachedBranchMembers7489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7489
  · have he : independentCachedBranchMembers7491.filter (independentCachedEdge 40)=independentCachedBranchMembers7490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7490
def independentCachedBranchMembers7492 : Finset ℕ := ([40,66,130,246,1596,1622,1650,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2710,2732,2738,2758,2776,2786,3126,3164,3174,3192,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7492 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7492 1650 4
  · have he : independentCachedBranchMembers7492.erase 1650=independentCachedBranchMembers7488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7488
  · have he : independentCachedBranchMembers7492.filter (independentCachedEdge 1650)=independentCachedBranchMembers7491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7491
def independentCachedBranchMembers7493 : Finset ℕ := ([246,1596,1686,1708,1714,2646,2668,2674,2758,2776,2786,3126,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7493 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7493 4 (fun x => (if x<2674 then (if x<1708 then (if x<1596 then 0 else (if x<1686 then 1 else 0)) else (if x<2646 then (if x<1714 then 2 else 1) else (if x<2668 then 0 else 1))) else (if x<3126 then (if x<2776 then (if x<2758 then 2 else 3) else (if x<2786 then 3 else 1)) else (if x<3238 then (if x<3228 then 0 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7494 : Finset ℕ := ([1686,1714,2668,2776,3126,3238] : List ℕ).toFinset
theorem independentCachedBranchBound7494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7494 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7494 3 (fun x => (if x<2776 then (if x<1714 then 0 else (if x<2668 then 1 else 0)) else (if x<3126 then 2 else (if x<3238 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7495 : Finset ℕ := ([66,246,1596,1686,1708,1714,2646,2668,2674,2758,2776,2786,3126,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7495 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7495 66 3
  · have he : independentCachedBranchMembers7495.erase 66=independentCachedBranchMembers7493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7493
  · have he : independentCachedBranchMembers7495.filter (independentCachedEdge 66)=independentCachedBranchMembers7494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7494
def independentCachedBranchMembers7496 : Finset ℕ := ([40,66,130,246,1596,1622,1644,1650,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2710,2732,2738,2758,2776,2786,3126,3164,3174,3192,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7496 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7496 1644 4
  · have he : independentCachedBranchMembers7496.erase 1644=independentCachedBranchMembers7492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7492
  · have he : independentCachedBranchMembers7496.filter (independentCachedEdge 1644)=independentCachedBranchMembers7495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7495
def independentCachedBranchMembers7497 : Finset ℕ := ([66,130,1596,1734,1752,1762,2620,2758,2776,2786,3164,3174,3192,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7497 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7497 4 (fun x => (if x<2776 then (if x<1752 then (if x<1596 then (if x<130 then 0 else 1) else (if x<1734 then 0 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2758 then 1 else 0))) else (if x<3192 then (if x<3164 then (if x<2786 then 3 else 3) else (if x<3174 then 2 else 2)) else (if x<3238 then (if x<3228 then 1 else 3) else (if x<3256 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7498 : Finset ℕ := ([18,40,66,130,246,1596,1622,1644,1650,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2710,2732,2738,2758,2776,2786,3126,3164,3174,3192,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7498 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7498 18 4
  · have he : independentCachedBranchMembers7498.erase 18=independentCachedBranchMembers7496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7496
  · have he : independentCachedBranchMembers7498.filter (independentCachedEdge 18)=independentCachedBranchMembers7497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7497
def independentCachedBranchMembers7499 : Finset ℕ := ([40,246,1622,1686,1734,1752,2646,2710,2758,2776,3126,3174,3192,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7499 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7499 4 (fun x => (if x<2758 then (if x<1734 then (if x<1622 then (if x<246 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<2646 then (if x<1752 then 2 else 2) else (if x<2710 then 1 else 0))) else (if x<3192 then (if x<3126 then (if x<2776 then 3 else 3) else (if x<3174 then 1 else 2)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7500 : Finset ℕ := ([12,18,40,66,130,246,1596,1622,1644,1650,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2710,2732,2738,2758,2776,2786,3126,3164,3174,3192,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7500 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7500 12 4
  · have he : independentCachedBranchMembers7500.erase 12=independentCachedBranchMembers7498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7498
  · have he : independentCachedBranchMembers7500.filter (independentCachedEdge 12)=independentCachedBranchMembers7499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7499
def independentCachedBranchMembers7501 : Finset ℕ := ([12,18,34,40,66,72,130,136,246,252,1590,1596,1622,1628,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2758,2764,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7501 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7501 3288 5
  · have he : independentCachedBranchMembers7501.erase 3288=independentCachedBranchMembers7479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7479
  · have he : independentCachedBranchMembers7501.filter (independentCachedEdge 3288)=independentCachedBranchMembers7500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7500
def independentCachedBranchMembers7502 : Finset ℕ := ([72,136,252,1590,1628,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2716,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7502 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7502 5 (fun x => (if x<2674 then (if x<1714 then (if x<1590 then (if x<136 then 0 else (if x<252 then 1 else 0)) else (if x<1692 then (if x<1628 then 1 else 0) else (if x<1708 then 1 else 2))) else (if x<1768 then (if x<1734 then 2 else (if x<1752 then 2 else 2)) else (if x<2652 then (if x<2614 then 0 else 3) else (if x<2668 then 3 else 0)))) else (if x<3174 then (if x<2776 then (if x<2716 then 1 else (if x<2758 then 4 else 3)) else (if x<3132 then (if x<2792 then 0 else 4) else (if x<3158 then 3 else 3))) else (if x<3238 then (if x<3192 then 1 else (if x<3222 then 0 else 4)) else (if x<3276 then (if x<3256 then 2 else 2) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7503 : Finset ℕ := ([252,1708,1734,1768,2668,2758,2792,3132,3158,3192,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7503 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7503 4 (fun x => (if x<2792 then (if x<1768 then (if x<1708 then 0 else (if x<1734 then 0 else 1)) else (if x<2668 then 1 else (if x<2758 then 0 else 2))) else (if x<3192 then (if x<3132 then 2 else (if x<3158 then 0 else 1)) else (if x<3222 then 1 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7504 : Finset ℕ := ([34,72,136,252,1590,1628,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2716,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7504 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7504 34 4
  · have he : independentCachedBranchMembers7504.erase 34=independentCachedBranchMembers7502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7502
  · have he : independentCachedBranchMembers7504.filter (independentCachedEdge 34)=independentCachedBranchMembers7503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7503
def independentCachedBranchMembers7505 : Finset ℕ := ([34,72,136,252,1590,1628,1692,1768,2614,2652,2716,2792,3132,3158,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7505 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7505 4 (fun x => (if x<2614 then (if x<1590 then (if x<136 then (if x<72 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1692 then (if x<1628 then 0 else 0) else (if x<1768 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2652 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3158 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7506 : Finset ℕ := ([34,72,136,252,1590,1628,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2716,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7506 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7506 3282 4
  · have he : independentCachedBranchMembers7506.erase 3282=independentCachedBranchMembers7504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7504
  · have he : independentCachedBranchMembers7506.filter (independentCachedEdge 3282)=independentCachedBranchMembers7505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7505
def independentCachedBranchMembers7507 : Finset ℕ := ([136,252,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,3132,3158,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7507 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7507 4 (fun x => (if x<2614 then (if x<1714 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3132 then (if x<2668 then (if x<2652 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3174 then (if x<3158 then 2 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7508 : Finset ℕ := ([34,72,136,252,1590,1628,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2716,2738,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7508 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7508 2738 4
  · have he : independentCachedBranchMembers7508.erase 2738=independentCachedBranchMembers7506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7506
  · have he : independentCachedBranchMembers7508.filter (independentCachedEdge 2738)=independentCachedBranchMembers7507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7507
def independentCachedBranchMembers7509 : Finset ℕ := ([34,72,1590,1628,1708,1714,1734,1752,2668,2674,2716,2792,3174,3192,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7509 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7509 4 (fun x => (if x<2668 then (if x<1708 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1628 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3174 then (if x<2716 then (if x<2674 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3192 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7510 : Finset ℕ := ([34,72,136,252,1590,1628,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2716,2732,2738,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7510 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7510 2732 4
  · have he : independentCachedBranchMembers7510.erase 2732=independentCachedBranchMembers7508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7508
  · have he : independentCachedBranchMembers7510.filter (independentCachedEdge 2732)=independentCachedBranchMembers7509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7509
def independentCachedBranchMembers7511 : Finset ℕ := ([252,1590,1692,1708,1714,2652,2668,2674,2758,2776,2792,3132,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7511 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7511 4 (fun x => (if x<2674 then (if x<1708 then (if x<1590 then 0 else (if x<1692 then 1 else 0)) else (if x<2652 then (if x<1714 then 1 else 2) else (if x<2668 then 0 else 2))) else (if x<3132 then (if x<2776 then (if x<2758 then 1 else 3) else (if x<2792 then 3 else 1)) else (if x<3238 then (if x<3222 then 0 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7512 : Finset ℕ := ([1692,1708,2674,2758,3132,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7512 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7512 3 (fun x => (if x<2758 then (if x<1708 then 0 else (if x<2674 then 1 else 0)) else (if x<3132 then 2 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7513 : Finset ℕ := ([72,252,1590,1692,1708,1714,2652,2668,2674,2758,2776,2792,3132,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7513 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7513 72 3
  · have he : independentCachedBranchMembers7513.erase 72=independentCachedBranchMembers7511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7511
  · have he : independentCachedBranchMembers7513.filter (independentCachedEdge 72)=independentCachedBranchMembers7512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7512
def independentCachedBranchMembers7514 : Finset ℕ := ([34,72,136,252,1590,1628,1650,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2716,2732,2738,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7514 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7514 1650 4
  · have he : independentCachedBranchMembers7514.erase 1650=independentCachedBranchMembers7510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7510
  · have he : independentCachedBranchMembers7514.filter (independentCachedEdge 1650)=independentCachedBranchMembers7513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7513
def independentCachedBranchMembers7515 : Finset ℕ := ([136,1628,1708,1714,1768,2614,2668,2674,2716,2758,2776,3158,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7515 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7515 4 (fun x => (if x<2674 then (if x<1714 then (if x<1628 then 0 else (if x<1708 then 1 else 0)) else (if x<2614 then (if x<1768 then 2 else 1) else (if x<2668 then 2 else 1))) else (if x<3158 then (if x<2758 then (if x<2716 then 0 else 3) else (if x<2776 then 3 else 1)) else (if x<3256 then (if x<3238 then 0 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7516 : Finset ℕ := ([1708,1768,2668,2758,3158,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7516 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7516 3 (fun x => (if x<2758 then (if x<1768 then 0 else (if x<2668 then 1 else 0)) else (if x<3158 then 2 else (if x<3256 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7517 : Finset ℕ := ([34,136,1628,1708,1714,1768,2614,2668,2674,2716,2758,2776,3158,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7517 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7517 34 3
  · have he : independentCachedBranchMembers7517.erase 34=independentCachedBranchMembers7515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7515
  · have he : independentCachedBranchMembers7517.filter (independentCachedEdge 34)=independentCachedBranchMembers7516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7516
def independentCachedBranchMembers7518 : Finset ℕ := ([34,72,136,252,1590,1628,1644,1650,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2716,2732,2738,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7518 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7518 1644 4
  · have he : independentCachedBranchMembers7518.erase 1644=independentCachedBranchMembers7514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7514
  · have he : independentCachedBranchMembers7518.filter (independentCachedEdge 1644)=independentCachedBranchMembers7517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7517
def independentCachedBranchMembers7519 : Finset ℕ := ([34,252,1628,1692,1734,1752,2652,2716,2758,2776,3132,3174,3192,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7519 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7519 4 (fun x => (if x<2758 then (if x<1734 then (if x<1628 then (if x<252 then 0 else 1) else (if x<1692 then 0 else 1)) else (if x<2652 then (if x<1752 then 2 else 2) else (if x<2716 then 1 else 0))) else (if x<3192 then (if x<3132 then (if x<2776 then 3 else 3) else (if x<3174 then 1 else 2)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
