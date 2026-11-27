/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch147
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7520 : Finset ℕ := ([18,34,72,136,252,1590,1628,1644,1650,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2716,2732,2738,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7520 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7520 18 4
  · have he : independentCachedBranchMembers7520.erase 18=independentCachedBranchMembers7518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7518
  · have he : independentCachedBranchMembers7520.filter (independentCachedEdge 18)=independentCachedBranchMembers7519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7519
def independentCachedBranchMembers7521 : Finset ℕ := ([72,136,1590,1734,1752,1768,2614,2758,2776,2792,3158,3174,3192,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7521 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7521 4 (fun x => (if x<2776 then (if x<1752 then (if x<1590 then (if x<136 then 0 else 1) else (if x<1734 then 0 else 2)) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2758 then 1 else 3))) else (if x<3192 then (if x<3158 then (if x<2792 then 0 else 3) else (if x<3174 then 2 else 1)) else (if x<3238 then (if x<3222 then 2 else 3) else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7522 : Finset ℕ := ([12,18,34,72,136,252,1590,1628,1644,1650,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2716,2732,2738,2758,2776,2792,3132,3158,3174,3192,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7522 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7522 12 4
  · have he : independentCachedBranchMembers7522.erase 12=independentCachedBranchMembers7520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7520
  · have he : independentCachedBranchMembers7522.filter (independentCachedEdge 12)=independentCachedBranchMembers7521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7521
def independentCachedBranchMembers7523 : Finset ℕ := ([12,18,34,40,66,72,130,136,246,252,1590,1596,1622,1628,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2758,2764,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7523 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7523 3270 5
  · have he : independentCachedBranchMembers7523.erase 3270=independentCachedBranchMembers7501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7501
  · have he : independentCachedBranchMembers7523.filter (independentCachedEdge 3270)=independentCachedBranchMembers7522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7522
def independentCachedBranchMembers7524 : Finset ℕ := ([130,246,1590,1628,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7524 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7524 5 (fun x => (if x<2680 then (if x<1720 then (if x<1628 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1686 then 1 else (if x<1702 then 0 else 2))) else (if x<1762 then (if x<1740 then 1 else (if x<1746 then 2 else 1)) else (if x<2646 then (if x<2620 then 0 else 1) else (if x<2662 then 1 else 3)))) else (if x<3164 then (if x<2758 then (if x<2716 then 3 else (if x<2738 then 4 else 0)) else (if x<2792 then (if x<2776 then 0 else 1) else (if x<3126 then 4 else 2))) else (if x<3222 then (if x<3180 then 2 else (if x<3186 then 3 else 3)) else (if x<3256 then (if x<3238 then 4 else 0) else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7525 : Finset ℕ := ([246,1720,1746,1762,2620,2646,2662,2716,2758,3186,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7525 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7525 4 (fun x => (if x<2662 then (if x<1762 then (if x<1720 then 0 else (if x<1746 then 1 else 0)) else (if x<2620 then 1 else (if x<2646 then 1 else 0))) else (if x<3186 then (if x<2716 then 1 else (if x<2758 then 2 else 2)) else (if x<3256 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7526 : Finset ℕ := ([72,130,246,1590,1628,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7526 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7526 72 4
  · have he : independentCachedBranchMembers7526.erase 72=independentCachedBranchMembers7524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7524
  · have he : independentCachedBranchMembers7526.filter (independentCachedEdge 72)=independentCachedBranchMembers7525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7525
def independentCachedBranchMembers7527 : Finset ℕ := ([130,1686,1720,1746,2620,2646,2680,2758,2792,3180,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7527 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7527 4 (fun x => (if x<2680 then (if x<1746 then (if x<1686 then 0 else (if x<1720 then 0 else 1)) else (if x<2620 then 1 else (if x<2646 then 1 else 1))) else (if x<3180 then (if x<2758 then 0 else (if x<2792 then 2 else 2)) else (if x<3222 then 0 else (if x<3256 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7528 : Finset ℕ := ([34,72,130,246,1590,1628,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7528 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7528 34 4
  · have he : independentCachedBranchMembers7528.erase 34=independentCachedBranchMembers7526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7526
  · have he : independentCachedBranchMembers7528.filter (independentCachedEdge 34)=independentCachedBranchMembers7527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7527
def independentCachedBranchMembers7529 : Finset ℕ := ([34,72,1590,1628,1702,1720,1740,1746,2662,2680,2716,2792,3180,3186,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7529 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7529 4 (fun x => (if x<2662 then (if x<1702 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1628 then 0 else 0)) else (if x<1740 then (if x<1720 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3180 then (if x<2716 then (if x<2680 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3186 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7530 : Finset ℕ := ([34,72,130,246,1590,1628,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7530 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7530 3282 4
  · have he : independentCachedBranchMembers7530.erase 3282=independentCachedBranchMembers7528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7528
  · have he : independentCachedBranchMembers7530.filter (independentCachedEdge 3282)=independentCachedBranchMembers7529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7529
def independentCachedBranchMembers7531 : Finset ℕ := ([130,246,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,3126,3164,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7531 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7531 4 (fun x => (if x<2620 then (if x<1720 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<3126 then (if x<2662 then (if x<2646 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3180 then (if x<3164 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7532 : Finset ℕ := ([34,72,130,246,1590,1628,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7532 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7532 3276 4
  · have he : independentCachedBranchMembers7532.erase 3276=independentCachedBranchMembers7530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7530
  · have he : independentCachedBranchMembers7532.filter (independentCachedEdge 3276)=independentCachedBranchMembers7531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7531
def independentCachedBranchMembers7533 : Finset ℕ := ([34,72,130,246,1590,1628,1686,1762,2620,2646,2716,2792,3126,3164,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7533 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7533 4 (fun x => (if x<2620 then (if x<1590 then (if x<130 then (if x<72 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1686 then (if x<1628 then 0 else 0) else (if x<1762 then 1 else 1))) else (if x<3126 then (if x<2716 then (if x<2646 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3164 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7534 : Finset ℕ := ([34,72,130,246,1590,1628,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2732,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7534 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7534 2732 4
  · have he : independentCachedBranchMembers7534.erase 2732=independentCachedBranchMembers7532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7532
  · have he : independentCachedBranchMembers7534.filter (independentCachedEdge 2732)=independentCachedBranchMembers7533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7533
def independentCachedBranchMembers7535 : Finset ℕ := ([72,130,1590,1740,1746,1762,2620,2758,2776,2792,3164,3180,3186,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7535 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7535 4 (fun x => (if x<2776 then (if x<1746 then (if x<1590 then (if x<130 then 0 else 0) else (if x<1740 then 1 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2758 then 1 else 2))) else (if x<3186 then (if x<3164 then (if x<2792 then 1 else 2) else (if x<3180 then 0 else 3)) else (if x<3238 then (if x<3222 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7536 : Finset ℕ := ([34,72,130,246,1590,1628,1650,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2732,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7536 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7536 1650 4
  · have he : independentCachedBranchMembers7536.erase 1650=independentCachedBranchMembers7534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7534
  · have he : independentCachedBranchMembers7536.filter (independentCachedEdge 1650)=independentCachedBranchMembers7535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7535
def independentCachedBranchMembers7537 : Finset ℕ := ([34,246,1628,1686,1740,1746,2646,2716,2758,2776,3126,3180,3186,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7537 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7537 4 (fun x => (if x<2758 then (if x<1740 then (if x<1628 then (if x<246 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1746 then 2 else 2) else (if x<2716 then 1 else 1))) else (if x<3186 then (if x<3126 then (if x<2776 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7538 : Finset ℕ := ([34,72,130,246,1590,1628,1644,1650,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2732,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7538 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7538 1644 4
  · have he : independentCachedBranchMembers7538.erase 1644=independentCachedBranchMembers7536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7536
  · have he : independentCachedBranchMembers7538.filter (independentCachedEdge 1644)=independentCachedBranchMembers7537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7537
def independentCachedBranchMembers7539 : Finset ℕ := ([34,130,1628,1702,1720,1762,2620,2662,2680,2716,2758,2776,3164,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7539 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7539 4 (fun x => (if x<2680 then (if x<1720 then (if x<1628 then (if x<130 then 0 else 1) else (if x<1702 then 0 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2662 then 2 else 2))) else (if x<3164 then (if x<2758 then (if x<2716 then 1 else 0) else (if x<2776 then 3 else 3)) else (if x<3256 then (if x<3238 then 1 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7540 : Finset ℕ := ([18,34,72,130,246,1590,1628,1644,1650,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2732,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7540 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7540 18 4
  · have he : independentCachedBranchMembers7540.erase 18=independentCachedBranchMembers7538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7538
  · have he : independentCachedBranchMembers7540.filter (independentCachedEdge 18)=independentCachedBranchMembers7539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7539
def independentCachedBranchMembers7541 : Finset ℕ := ([72,246,1590,1686,1702,1720,2646,2662,2680,2758,2776,2792,3126,3222,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7541 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7541 4 (fun x => (if x<2680 then (if x<1702 then (if x<1590 then (if x<246 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<2646 then (if x<1720 then 2 else 2) else (if x<2662 then 1 else 2))) else (if x<3126 then (if x<2776 then (if x<2758 then 2 else 3) else (if x<2792 then 0 else 3)) else (if x<3238 then (if x<3222 then 1 else 3) else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7542 : Finset ℕ := ([12,18,34,72,130,246,1590,1628,1644,1650,1686,1702,1720,1740,1746,1762,2620,2646,2662,2680,2716,2732,2738,2758,2776,2792,3126,3164,3180,3186,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7542 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7542 12 4
  · have he : independentCachedBranchMembers7542.erase 12=independentCachedBranchMembers7540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7540
  · have he : independentCachedBranchMembers7542.filter (independentCachedEdge 12)=independentCachedBranchMembers7541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7541
def independentCachedBranchMembers7543 : Finset ℕ := ([12,18,34,40,66,72,130,136,246,252,1590,1596,1622,1628,1644,1650,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2710,2716,2732,2738,2744,2758,2764,2770,2776,2786,2792,3126,3132,3158,3164,3174,3180,3186,3192,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7543 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7543 2744 5
  · have he : independentCachedBranchMembers7543.erase 2744=independentCachedBranchMembers7523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7523
  · have he : independentCachedBranchMembers7543.filter (independentCachedEdge 2744)=independentCachedBranchMembers7542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7542
def independentCachedBranchMembers7544 : Finset ℕ := ([136,252,1596,1622,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7544 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7544 5 (fun x => (if x<2680 then (if x<1720 then (if x<1622 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 0 else 1))) else (if x<1768 then (if x<1740 then 2 else (if x<1746 then 1 else 2)) else (if x<2652 then (if x<2614 then 0 else 1) else (if x<2662 then 1 else 3)))) else (if x<3158 then (if x<2758 then (if x<2710 then 3 else (if x<2732 then 4 else 0)) else (if x<2786 then (if x<2776 then 1 else 0) else (if x<3132 then 4 else 2))) else (if x<3228 then (if x<3180 then 2 else (if x<3186 then 3 else 3)) else (if x<3256 then (if x<3238 then 4 else 3) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7545 : Finset ℕ := ([252,1702,1740,1768,2614,2652,2680,2710,2776,3180,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7545 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7545 4 (fun x => (if x<2680 then (if x<1768 then (if x<1702 then 0 else (if x<1740 then 1 else 0)) else (if x<2614 then 1 else (if x<2652 then 1 else 0))) else (if x<3180 then (if x<2710 then 1 else (if x<2776 then 2 else 2)) else (if x<3238 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7546 : Finset ℕ := ([66,136,252,1596,1622,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7546 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7546 66 4
  · have he : independentCachedBranchMembers7546.erase 66=independentCachedBranchMembers7544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7544
  · have he : independentCachedBranchMembers7546.filter (independentCachedEdge 66)=independentCachedBranchMembers7545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7545
def independentCachedBranchMembers7547 : Finset ℕ := ([136,1692,1702,1740,2614,2652,2662,2776,2786,3186,3228,3238] : List ℕ).toFinset
theorem independentCachedBranchBound7547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7547 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7547 4 (fun x => (if x<2662 then (if x<1740 then (if x<1692 then 0 else (if x<1702 then 0 else 1)) else (if x<2614 then 1 else (if x<2652 then 1 else 1))) else (if x<3186 then (if x<2776 then 0 else (if x<2786 then 2 else 2)) else (if x<3228 then 0 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7548 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7548 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7548 40 4
  · have he : independentCachedBranchMembers7548.erase 40=independentCachedBranchMembers7546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7546
  · have he : independentCachedBranchMembers7548.filter (independentCachedEdge 40)=independentCachedBranchMembers7547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7547
def independentCachedBranchMembers7549 : Finset ℕ := ([136,252,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,3132,3158,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7549 4 (fun x => (if x<2614 then (if x<1720 then (if x<1692 then (if x<252 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3132 then (if x<2662 then (if x<2652 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3180 then (if x<3158 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7550 : Finset ℕ := ([40,66,136,252,1596,1622,1692,1702,1720,1740,1746,1768,2614,2652,2662,2680,2710,2732,2758,2776,2786,3132,3158,3180,3186,3228,3238,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7550 3282 4
  · have he : independentCachedBranchMembers7550.erase 3282=independentCachedBranchMembers7548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7548
  · have he : independentCachedBranchMembers7550.filter (independentCachedEdge 3282)=independentCachedBranchMembers7549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7549
def independentCachedBranchMembers7551 : Finset ℕ := ([40,66,1596,1622,1702,1720,1740,1746,2662,2680,2710,2786,3180,3186,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound7551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7551 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7551 4 (fun x => (if x<2662 then (if x<1702 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1740 then (if x<1720 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3180 then (if x<2710 then (if x<2680 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3186 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
