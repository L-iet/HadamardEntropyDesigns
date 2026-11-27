/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch145
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7456 : Finset ℕ := ([12,40,66,136,246,1622,1650,1692,1708,1720,1734,1746,1762,2620,2646,2662,2674,2716,2732,2758,2770,2786,3132,3158,3174,3186,3228,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7456 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7456 2786 4
  · have he : independentCachedBranchMembers7456.erase 2786=independentCachedBranchMembers7454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7454
  · have he : independentCachedBranchMembers7456.filter (independentCachedEdge 2786)=independentCachedBranchMembers7455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7455
def independentCachedBranchMembers7457 : Finset ℕ := ([136,246,1692,1708,1720,1734,1746,1762,2620,2646,2662,2674,3132,3158,3174,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7457 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7457 4 (fun x => (if x<2620 then (if x<1720 then (if x<1692 then (if x<246 then 0 else 1) else (if x<1708 then 0 else 2)) else (if x<1746 then (if x<1734 then 3 else 1) else (if x<1762 then 3 else 2))) else (if x<3132 then (if x<2662 then (if x<2646 then 2 else 1) else (if x<2674 then 0 else 2)) else (if x<3174 then (if x<3158 then 3 else 3) else (if x<3186 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7458 : Finset ℕ := ([12,40,66,136,246,1596,1622,1650,1692,1708,1720,1734,1746,1762,2620,2646,2662,2674,2716,2732,2758,2770,2786,3132,3158,3174,3186,3228,3244,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7458 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7458 1596 4
  · have he : independentCachedBranchMembers7458.erase 1596=independentCachedBranchMembers7456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7456
  · have he : independentCachedBranchMembers7458.filter (independentCachedEdge 1596)=independentCachedBranchMembers7457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7457
def independentCachedBranchMembers7459 : Finset ℕ := ([12,18,40,66,72,130,136,246,252,1590,1596,1622,1628,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2758,2764,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7459 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7459 72 5
  · have he : independentCachedBranchMembers7459.erase 72=independentCachedBranchMembers7449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7449
  · have he : independentCachedBranchMembers7459.filter (independentCachedEdge 72)=independentCachedBranchMembers7458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7458
def independentCachedBranchMembers7460 : Finset ℕ := ([40,130,252,1596,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2758,2770,2792,3132,3158,3180,3192,3222,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7460 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7460 5 (fun x => (if x<2668 then (if x<1720 then (if x<1596 then (if x<130 then 0 else (if x<252 then 0 else 1)) else (if x<1686 then 0 else (if x<1708 then 0 else 1))) else (if x<1768 then (if x<1734 then 2 else (if x<1746 then 3 else 2)) else (if x<2620 then 3 else (if x<2646 then 1 else 2)))) else (if x<3158 then (if x<2770 then (if x<2680 then 0 else (if x<2758 then 3 else 0)) else (if x<2792 then 4 else (if x<3132 then 1 else 4))) else (if x<3222 then (if x<3180 then 4 else (if x<3192 then 1 else 0)) else (if x<3244 then 3 else (if x<3256 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7461 : Finset ℕ := ([130,252,1686,1768,2668,2680,2792,3180,3192,3222] : List ℕ).toFinset
theorem independentCachedBranchBound7461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7461 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7461 4 (fun x => (if x<2680 then (if x<1686 then (if x<252 then 0 else 1) else (if x<1768 then 0 else (if x<2668 then 1 else 0))) else (if x<3180 then (if x<2792 then 1 else 2) else (if x<3192 then 1 else (if x<3222 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7462 : Finset ℕ := ([40,66,130,252,1596,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2758,2770,2792,3132,3158,3180,3192,3222,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7462 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7462 66 4
  · have he : independentCachedBranchMembers7462.erase 66=independentCachedBranchMembers7460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7460
  · have he : independentCachedBranchMembers7462.filter (independentCachedEdge 66)=independentCachedBranchMembers7461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7461
def independentCachedBranchMembers7463 : Finset ℕ := ([252,1720,1746,1768,2680,2770,2792,3132,3158,3180,3222,3244] : List ℕ).toFinset
theorem independentCachedBranchBound7463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7463 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7463 4 (fun x => (if x<2792 then (if x<1768 then (if x<1720 then 0 else (if x<1746 then 0 else 1)) else (if x<2680 then 1 else (if x<2770 then 0 else 2))) else (if x<3180 then (if x<3132 then 2 else (if x<3158 then 0 else 1)) else (if x<3222 then 1 else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7464 : Finset ℕ := ([40,66,130,252,1596,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2758,2770,2792,3132,3158,3180,3192,3222,3244,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7464 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7464 3282 4
  · have he : independentCachedBranchMembers7464.erase 3282=independentCachedBranchMembers7462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7462
  · have he : independentCachedBranchMembers7464.filter (independentCachedEdge 3282)=independentCachedBranchMembers7463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7463
def independentCachedBranchMembers7465 : Finset ℕ := ([130,1686,1708,1734,2620,2646,2668,2770,2792,3192,3222,3244] : List ℕ).toFinset
theorem independentCachedBranchBound7465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7465 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7465 4 (fun x => (if x<2668 then (if x<1734 then (if x<1686 then 0 else (if x<1708 then 0 else 1)) else (if x<2620 then 1 else (if x<2646 then 1 else 1))) else (if x<3192 then (if x<2770 then 0 else (if x<2792 then 2 else 2)) else (if x<3222 then 0 else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7466 : Finset ℕ := ([40,66,130,252,1596,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2732,2758,2770,2792,3132,3158,3180,3192,3222,3244,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7466 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7466 2732 4
  · have he : independentCachedBranchMembers7466.erase 2732=independentCachedBranchMembers7464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7464
  · have he : independentCachedBranchMembers7466.filter (independentCachedEdge 2732)=independentCachedBranchMembers7465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7465
def independentCachedBranchMembers7467 : Finset ℕ := ([66,1596,1686,1708,1746,1768,2646,2668,2758,3158,3180,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7467 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7467 4 (fun x => (if x<2646 then (if x<1708 then (if x<1596 then 0 else (if x<1686 then 0 else 1)) else (if x<1746 then 1 else (if x<1768 then 2 else 2))) else (if x<3158 then (if x<2668 then 1 else (if x<2758 then 1 else 0)) else (if x<3180 then 2 else (if x<3256 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7468 : Finset ℕ := ([40,66,130,252,1596,1644,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2732,2758,2770,2792,3132,3158,3180,3192,3222,3244,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7468 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7468 1644 4
  · have he : independentCachedBranchMembers7468.erase 1644=independentCachedBranchMembers7466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7466
  · have he : independentCachedBranchMembers7468.filter (independentCachedEdge 1644)=independentCachedBranchMembers7467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7467
def independentCachedBranchMembers7469 : Finset ℕ := ([66,130,252,1596,1720,1734,2620,2680,2758,3132,3192,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7469 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7469 4 (fun x => (if x<2620 then (if x<1596 then (if x<130 then 0 else (if x<252 then 1 else 2)) else (if x<1720 then 0 else (if x<1734 then 2 else 1))) else (if x<3132 then (if x<2680 then 1 else (if x<2758 then 2 else 0)) else (if x<3192 then 2 else (if x<3256 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7470 : Finset ℕ := ([18,40,66,130,252,1596,1644,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2732,2758,2770,2792,3132,3158,3180,3192,3222,3244,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7470 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7470 18 4
  · have he : independentCachedBranchMembers7470.erase 18=independentCachedBranchMembers7468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7468
  · have he : independentCachedBranchMembers7470.filter (independentCachedEdge 18)=independentCachedBranchMembers7469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7469
def independentCachedBranchMembers7471 : Finset ℕ := ([66,130,1596,1734,1746,1768,2620,2758,2770,2792,3158,3180,3192,3222,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7471 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7471 4 (fun x => (if x<2770 then (if x<1746 then (if x<1596 then (if x<130 then 0 else 1) else (if x<1734 then 0 else 1)) else (if x<2620 then (if x<1768 then 2 else 2) else (if x<2758 then 1 else 0))) else (if x<3192 then (if x<3158 then (if x<2792 then 3 else 3) else (if x<3180 then 2 else 2)) else (if x<3244 then (if x<3222 then 1 else 3) else (if x<3256 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7472 : Finset ℕ := ([18,40,66,130,252,1596,1644,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2732,2758,2770,2792,3132,3158,3180,3192,3222,3244,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7472 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7472 3304 4
  · have he : independentCachedBranchMembers7472.erase 3304=independentCachedBranchMembers7470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7470
  · have he : independentCachedBranchMembers7472.filter (independentCachedEdge 3304)=independentCachedBranchMembers7471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7471
def independentCachedBranchMembers7473 : Finset ℕ := ([66,252,1596,1686,1708,1720,2646,2668,2680,2758,2770,2792,3132,3222,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7473 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7473 4 (fun x => (if x<2680 then (if x<1708 then (if x<1596 then (if x<252 then 0 else 1) else (if x<1686 then 0 else 2)) else (if x<2646 then (if x<1720 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3132 then (if x<2770 then (if x<2758 then 2 else 0) else (if x<2792 then 3 else 3)) else (if x<3244 then (if x<3222 then 1 else 3) else (if x<3256 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7474 : Finset ℕ := ([18,40,66,130,252,1596,1644,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2710,2732,2758,2770,2792,3132,3158,3180,3192,3222,3244,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7474 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7474 2710 4
  · have he : independentCachedBranchMembers7474.erase 2710=independentCachedBranchMembers7472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7472
  · have he : independentCachedBranchMembers7474.filter (independentCachedEdge 2710)=independentCachedBranchMembers7473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7473
def independentCachedBranchMembers7475 : Finset ℕ := ([252,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,3132,3158,3180,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7475 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7475 4 (fun x => (if x<2620 then (if x<1720 then (if x<1686 then 0 else (if x<1708 then 1 else 0)) else (if x<1746 then (if x<1734 then 1 else 2) else (if x<1768 then 3 else 2))) else (if x<3132 then (if x<2668 then (if x<2646 then 0 else 1) else (if x<2680 then 3 else 1)) else (if x<3180 then (if x<3158 then 3 else 2) else (if x<3192 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7476 : Finset ℕ := ([252,1708,1720,1768,2646,3158] : List ℕ).toFinset
theorem independentCachedBranchBound7476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7476 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7476 3 (fun x => (if x<1768 then (if x<1708 then 0 else (if x<1720 then 0 else 1)) else (if x<2646 then 2 else (if x<3158 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7477 : Finset ℕ := ([130,252,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,3132,3158,3180,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7477 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7477 130 3
  · have he : independentCachedBranchMembers7477.erase 130=independentCachedBranchMembers7475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7475
  · have he : independentCachedBranchMembers7477.filter (independentCachedEdge 130)=independentCachedBranchMembers7476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7476
def independentCachedBranchMembers7478 : Finset ℕ := ([18,40,66,130,252,1596,1622,1644,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2710,2732,2758,2770,2792,3132,3158,3180,3192,3222,3244,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7478 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7478 1622 4
  · have he : independentCachedBranchMembers7478.erase 1622=independentCachedBranchMembers7474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7474
  · have he : independentCachedBranchMembers7478.filter (independentCachedEdge 1622)=independentCachedBranchMembers7477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7477
def independentCachedBranchMembers7479 : Finset ℕ := ([12,18,34,40,66,72,130,136,246,252,1590,1596,1622,1628,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2758,2764,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7479 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7479 34 5
  · have he : independentCachedBranchMembers7479.erase 34=independentCachedBranchMembers7459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7459
  · have he : independentCachedBranchMembers7479.filter (independentCachedEdge 34)=independentCachedBranchMembers7478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7478
def independentCachedBranchMembers7480 : Finset ℕ := ([66,130,246,1596,1622,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2710,2758,2776,2786,3126,3164,3174,3192,3228,3238,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7480 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7480 5 (fun x => (if x<2674 then (if x<1714 then (if x<1596 then (if x<130 then 0 else (if x<246 then 1 else 0)) else (if x<1686 then (if x<1622 then 1 else 0) else (if x<1708 then 1 else 2))) else (if x<1762 then (if x<1734 then 2 else (if x<1752 then 2 else 2)) else (if x<2646 then (if x<2620 then 0 else 3) else (if x<2668 then 3 else 1)))) else (if x<3174 then (if x<2776 then (if x<2710 then 0 else (if x<2758 then 4 else 0)) else (if x<3126 then (if x<2786 then 3 else 4) else (if x<3164 then 3 else 3))) else (if x<3238 then (if x<3192 then 0 else (if x<3228 then 1 else 4)) else (if x<3282 then (if x<3256 then 2 else 2) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7481 : Finset ℕ := ([246,1714,1752,1762,2674,2776,2786,3126,3164,3174,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound7481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7481 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7481 4 (fun x => (if x<2786 then (if x<1762 then (if x<1714 then 0 else (if x<1752 then 0 else 1)) else (if x<2674 then 1 else (if x<2776 then 0 else 2))) else (if x<3174 then (if x<3126 then 2 else (if x<3164 then 0 else 1)) else (if x<3228 then 1 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7482 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2710,2758,2776,2786,3126,3164,3174,3192,3228,3238,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7482 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7482 40 4
  · have he : independentCachedBranchMembers7482.erase 40=independentCachedBranchMembers7480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7480
  · have he : independentCachedBranchMembers7482.filter (independentCachedEdge 40)=independentCachedBranchMembers7481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7481
def independentCachedBranchMembers7483 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1762,2620,2646,2710,2786,3126,3164,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7483 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7483 4 (fun x => (if x<2620 then (if x<1596 then (if x<130 then (if x<66 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1686 then (if x<1622 then 0 else 0) else (if x<1762 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2646 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3164 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7484 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2710,2758,2776,2786,3126,3164,3174,3192,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7484 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7484 3276 4
  · have he : independentCachedBranchMembers7484.erase 3276=independentCachedBranchMembers7482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7482
  · have he : independentCachedBranchMembers7484.filter (independentCachedEdge 3276)=independentCachedBranchMembers7483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7483
def independentCachedBranchMembers7485 : Finset ℕ := ([40,66,1596,1622,1708,1714,1734,1752,2668,2674,2710,2786,3174,3192,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7485 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7485 4 (fun x => (if x<2668 then (if x<1708 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3174 then (if x<2710 then (if x<2674 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3192 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7486 : Finset ℕ := ([40,66,130,246,1596,1622,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2710,2738,2758,2776,2786,3126,3164,3174,3192,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7486 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7486 2738 4
  · have he : independentCachedBranchMembers7486.erase 2738=independentCachedBranchMembers7484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7484
  · have he : independentCachedBranchMembers7486.filter (independentCachedEdge 2738)=independentCachedBranchMembers7485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7485
def independentCachedBranchMembers7487 : Finset ℕ := ([130,246,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,3126,3164,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7487 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7487 4 (fun x => (if x<2620 then (if x<1714 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3126 then (if x<2668 then (if x<2646 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3174 then (if x<3164 then 2 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
